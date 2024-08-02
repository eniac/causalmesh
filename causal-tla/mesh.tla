---- MODULE mesh ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANT Keys, Clients, Servers, NOP
MAXVC == 100 \* maximum value of the counter, for testing
NServer == Cardinality(Servers)
NClient == Cardinality(Clients)
NotOverlap(relation) == \A i, j \in DOMAIN relation : i /= j => relation[i] # relation[j]

(* 
    NeighborCC is map from the server id to its neighbor,
    it correponds to the propagation chain described in the paper
    e.g. In the case of 3 servers
    NeighborCC =
        S0 -> S1,
        S1 -> S2,
        S2 -> S0
*)
RECURSIVE Circle(_)
Circle(s) ==
    IF Cardinality(s) = 1 THEN
        [x \in s |-> x]
    ELSE
        LET s1 == CHOOSE x \in s : TRUE IN
        LET c == Circle(s \ {s1}) IN
        LET s2 == CHOOSE s2 \in DOMAIN c : TRUE IN
        LET s3 == CHOOSE s3 \in DOMAIN c : c[s3] = s2 IN
        [k \in {s1} |-> s2] @@ [c EXCEPT ![s3] = s1]
NeighborCC == Circle(Servers)


TypeKey(key) == key \in Keys

(* 
    Definition of vector clock and happens-before relationship.
    VCMerge is a function that computes the union of two vector clocks.
*)
TypeVC(vc) ==
    /\ vc = [i \in Servers |-> vc[i]]
    /\ \A i \in Servers : vc[i] \in Nat
EmptyVC == [i \in Servers |-> 0]
VCEqual(vc1, vc2) ==
    \A i \in Servers : vc1[i] = vc2[i]
VCHappensBefore(vc1, vc2) ==
    /\ TypeVC(vc1)
    /\ TypeVC(vc2)
    /\ ~VCEqual(vc1, vc2)
    /\ ~(\E i \in Servers : vc1[i] > vc2[i])
VCMerge(vc1, vc2) ==
    [i \in Servers |-> IF vc1[i] > vc2[i] THEN vc1[i] ELSE vc2[i]]
TestVCs == [Servers -> 1..MAXVC]

(* 
    Definition of dependencies.
    DepsMerge is a function that merges two dependencies using the same mechanism as vector
clocks.
*)
EMPTYDEPS == <<>>
TypeDeps(deps) ==
    deps = EMPTYDEPS
    \/ /\ DOMAIN deps \subseteq Keys
       /\ \A k \in DOMAIN deps : TypeVC(deps[k])
DepsEqual(deps1, deps2) ==
    /\ DOMAIN deps1 = DOMAIN deps2
    /\ \A k \in DOMAIN deps1 : VCEqual(deps1[k], deps2[k])
DepsMerge(deps1, deps2) ==
    [k \in DOMAIN deps1 \ DOMAIN deps2 |-> deps1[k]] @@
    [k \in DOMAIN deps2 \ DOMAIN deps1 |-> deps2[k]] @@
    [k \in DOMAIN deps1 \cap DOMAIN deps2 |-> VCMerge(deps1[k], deps2[k])]

InsertOrMergeVC(maps, key, vc) ==
    IF key \in DOMAIN maps THEN
        [k \in DOMAIN maps \ {key} |-> maps[k]] @@
        [k \in {key} |-> VCMerge(maps[key], vc)]
    ELSE
        [k \in DOMAIN maps |-> maps[k]] @@
        [k \in {key} |-> vc]

(* 
    Cache servers stores a hashmap from user keys to Meta.
    Meta is a tuple of user value, version and dependencies, as defined in Section 4 in the paper.
*)
TypeMeta(meta) ==
    /\ meta = [key |-> meta.key, vc |-> meta.vc, deps |-> meta.deps]
    /\ TypeKey(meta.key)
    /\ TypeVC(meta.vc)
    /\ TypeDeps(meta.deps)
MetaEqual(meta1, meta2) ==
    /\ meta1.key = meta2.key
    /\ VCEqual(meta1.vc, meta2.vc)
    /\ DepsEqual(meta1.deps, meta2.deps)
MetaHappensBefore(meta1, meta2) ==
    /\ TypeMeta(meta1)
    /\ TypeMeta(meta2)
    /\ VCHappensBefore(meta1.vc, meta2.vc)
MetaMerge(meta1, meta2) ==
    [key |-> meta1.key, vc |-> VCMerge(meta1.vc, meta2.vc), deps |-> DepsMerge(meta1.deps, meta2.deps)]
EmptyMeta(key) == [key |-> key, vc |-> EmptyVC, deps |-> EMPTYDEPS]

RECURSIVE FoldSet(_, _, _)
FoldSet(op(_, _), res, set) ==
    IF Cardinality(set) = 0 THEN
        res
    ELSE
        LET x == CHOOSE x \in set : TRUE IN
        FoldSet(op, op(res, x), set \ {x})

InsertOrMergeMeta(maps, meta) ==
    IF meta.key \in DOMAIN maps THEN
        [k \in DOMAIN maps \ {meta.key} |-> maps[k]] @@
        [k \in {meta.key} |-> MetaMerge(maps[meta.key], meta)]
    ELSE
        [k \in DOMAIN maps |-> maps[k]] @@
        [k \in {meta.key} |-> meta]
AppendMeta(black, meta) ==
    [black EXCEPT ![meta.key] = @ \cup {meta}]


(* 
    White is the Consistent Cache defined in Section 4.
*)
TypeWhite(white) ==
    /\ DOMAIN white \subseteq Keys
    /\ \A k \in DOMAIN white : TypeMeta(white[k]) /\ white[k].key = k
EmptyWhite == [k \in Keys |-> EmptyMeta(k)]

(* 
    Black is the Inconsistent Cache defined in Section 4.
*)
TypeBlack(black) ==
    /\ DOMAIN black \subseteq Keys
    /\ \A k \in DOMAIN black : IsFiniteSet(black[k])
    /\ \A k \in DOMAIN black : \A meta \in black[k] : TypeMeta(meta) /\ meta.key = k
EmptyBlack == [k \in Keys |-> {}]

WhiteMerge(white1, white2) ==
    [k \in DOMAIN white1 \ DOMAIN white2 |-> white1[k]] @@
    [k \in DOMAIN white2 \ DOMAIN white1 |-> white2[k]] @@
    [k \in DOMAIN white1 \cap DOMAIN white2 |-> MetaMerge(white1[k], white2[k])]

TypeCacheServer(server) ==
    /\ server = [id |-> server.id, white |-> server.white, black |-> server.black, vc |-> server.vc]
    /\ server.id \in Servers
    /\ TypeVC(server.vc)
    /\ TypeWhite(server.white)
    /\ TypeBlack(server.black)

TypeClient(client) ==
    /\ client = [local |-> client.local, deps |-> client.deps]
    /\ TypeDeps(client.local)
    /\ TypeDeps(client.deps)

(* 
    TLA+ code for get_deps function in Figure 4.
*)
RECURSIVE GetDeps(_, _, _)
GetDeps(black, deps, todos) ==
    IF deps = EMPTYDEPS THEN todos
    ELSE
        LET kk == CHOOSE kk \in DOMAIN deps: TRUE
        IN
            IF <<kk, deps[kk]>> \in todos THEN
                GetDeps(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], todos)
            ELSE
                IF kk \notin DOMAIN black THEN
                    GetDeps(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], todos)
                ELSE
                    IF \E meta \in black[kk]: VCEqual(meta.vc, deps[kk]) THEN
                        LET meta == CHOOSE meta \in black[kk]: VCEqual(meta.vc, deps[kk])
                        IN
                            LET res == GetDeps(black, meta.deps, todos \cup {<<kk, deps[kk]>>})
                            IN
                                GetDeps(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], res)
                    ELSE
                        GetDeps(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], todos \cup {<<kk, deps[kk]>>})
        
RECURSIVE MergeTodos(_, _)
MergeTodos(todos, res) ==
    IF todos = {} THEN res
    ELSE
        LET todo == CHOOSE todo \in todos: TRUE
        IN
            IF todo[1] \notin DOMAIN res THEN
                MergeTodos(todos \ {todo}, res @@ [k \in {todo[1]} |-> todo[2]])
            ELSE
                MergeTodos(todos \ {todo}, [res EXCEPT ![todo[1]] = VCMerge(res[todo[1]], todo[2])])

RECURSIVE RemoveNotLarger(_, _, _, _)
RemoveNotLarger(bk, vc, bk_res, res) ==
    IF Cardinality(bk) = 0 THEN <<bk_res, res>>
    ELSE
        LET meta == CHOOSE meta \in bk: TRUE
        IN 
            IF VCHappensBefore(meta.vc, vc) \/ VCEqual(meta.vc, vc) THEN
                RemoveNotLarger(bk \ {meta}, vc, bk_res, MetaMerge(res, meta))
            ELSE
                RemoveNotLarger(bk \ {meta}, vc, bk_res \cup {meta}, res)

RECURSIVE PullTodos(_, _, _)
PullTodos(black, white, todos) == 
    IF todos = <<>> THEN <<black, white>>
    ELSE
        LET todo == CHOOSE todo \in DOMAIN todos: TRUE
        IN 
            LET res == RemoveNotLarger(black[todo], todos[todo], {}, [key |-> todo, vc |-> EmptyVC, deps |-> EMPTYDEPS])
            IN
                PullTodos([black EXCEPT ![todo] = res[1]], [white EXCEPT ![todo] = MetaMerge(white[todo], res[2])], [k \in DOMAIN todos \ {todo} |-> todos[k]])
(* 
    TLA+ code for integrate function in Figure 4.
*)
PullDeps(black, white, deps) ==
    LET todos == GetDeps(black, deps, {})
    IN
        LET merged_todos == MergeTodos(todos, <<>>)
        IN
            PullTodos(black, white, merged_todos)

RECURSIVE GetDeps2(_, _, _)
GetDeps2(black, deps, todos) ==
    IF deps = EMPTYDEPS THEN todos
    ELSE
        LET kk == CHOOSE kk \in DOMAIN deps: TRUE
        IN
            IF kk \in DOMAIN todos /\ (VCHappensBefore(deps[kk], todos[kk]) \/ VCEqual(deps[kk], todos[kk])) THEN
                GetDeps2(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], todos)
            ELSE
                IF kk \notin DOMAIN black THEN
                    GetDeps2(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], todos)
                ELSE
                    LET metas == {meta \in black[kk]: VCHappensBefore(meta.vc, deps[kk]) \/ VCEqual(meta.vc, deps[kk])} IN
                    LET merged_meta == FoldSet(MetaMerge, [key |-> kk, vc |-> EmptyVC, deps |-> EMPTYDEPS], metas) IN
                    LET res == GetDeps2(black, merged_meta.deps, DepsMerge(todos, [k \in {kk} |-> merged_meta.vc])) IN
                    GetDeps2(black, [k \in DOMAIN deps \ {kk} |-> deps[k]], DepsMerge(DepsMerge(todos, res), [k \in {kk} |-> merged_meta.vc]))

PullDeps2(black, white, deps) ==
    LET todos == GetDeps2(black, deps, <<>>) IN 
    PullTodos(black, white, todos)

(* 
    TLA+ code for ClientRead function in Figure 8.
*)
Read(black, white, key, deps) ==
    LET res == PullDeps2(black, white, deps)
    IN
        LET black_res == res[1] IN
        LET white_res == res[2] IN
        white_res[key]

(* 
    TLA+ code for ClientWrite function in Figure 8.
*)
Write(id, black, white, global_vc, key, deps) ==
    LET new_global_vc == [global_vc EXCEPT ![id] = global_vc[id] + 1] IN 
    LET new_black == [black EXCEPT ![key] = black[key] @@ {[key |-> key, vc |-> new_global_vc, deps |-> deps]}] IN
    new_global_vc

(* 
    Definition of CausalCut in Section 4 Definition 1.
*)
CausalCut(white) ==
    /\  TypeWhite(white)
    /\  \A k \in DOMAIN white:
            \A kk \in DOMAIN white[k].deps:
                /\ kk \in DOMAIN white
                /\ VCHappensBefore(white[k].deps[kk], white[kk].vc) \/ VCEqual(white[k].deps[kk], white[kk].vc)


Neighbor(myid) == NeighborCC[myid]

(* 
    A message queue between different cache servers.
    The message between cache servers has the following format:
    [
        type |-> "server",
        headid |-> headid,
        frame |-> frame
    ]
    where headid is the server id of the head of the propagation chain,
          frame is the content of the message.
*)
SendToNeighbor(mq, myid, headid, frame) ==
    LET neighbor == Neighbor(myid) IN 
    IF myid = neighbor THEN
        mq
    ELSE
        [mq EXCEPT ![neighbor] = Append(mq[neighbor], [
            type |-> "server",
            headid |-> headid,
            frame |-> frame
        ])]

(* 
    A message queue between clients/workflows and cache servers.
    The message has the following format:
    [
        type |-> "client",
        from |-> client_id,
        frame |-> frame
    ]
    where client_id is unique identifier of a client,
          frame is the content of the message.
*)
SendToServer(mq, svr_id, cli_id, frame) ==
    [mq EXCEPT ![svr_id] = Append(mq[svr_id], [
        type |-> "client",
        from |-> cli_id,
        frame |-> frame
    ])]

(* 
    A message queue between clients/workflows and cache servers.
    The message has the following format:
    [
        frame |-> frame
    ]
    This is a response message for a client request.
*)
SendToClient(mq, cli_id, frame) ==
    [mq EXCEPT ![cli_id] = Append(mq[cli_id], [
        frame |-> frame
    ])]

TypeMsg(msg) ==
    /\ msg.type \in {"client", "server"}

ReadsDepsAreMet(black, white, deps) ==
    \A k \in DOMAIN deps:
        LET m == FoldSet(MetaMerge, white[k], black[k]) IN
        \/ VCEqual(deps[k], m.vc)
        \/ VCHappensBefore(deps[k], m.vc)

(* 
   UponReadsDepsAreMet is a correctness conditon meaning when a client $C$ tries to read from $S_i$, $(S_i \cap C) \cup C.local$ is a cut and it covers $C.local \cup C.deps$.
*)
UponReadsDepsAreMet(white, deps) ==
    \A k \in DOMAIN deps:
        \/ VCEqual(deps[k], white[k].vc)
        \/ VCHappensBefore(deps[k], white[k].vc)

(* --fair algorithm sq {
variables cli_mq = [i \in Clients |-> <<>>];
          svr_mq = [i \in Servers |-> <<>>];
          finished = 0;

process(Client \in Clients)
variables local;
          deps;
          cli_id;
          n_op = NOP;
        \*   res;
          cur_frame;
{
    init_client:
        local := <<>>;
        deps := <<>>;
        cli_id := self;
    run_client:
        while (n_op > 0) {
            n_op := n_op - 1;
            with (optype \in {"R", "W"}) {
                with (to_svr_id \in Servers) {
                    with (key \in Keys) {
                        if (optype = "R") {
                            \* read function in Figure 11
                            if (/\ local /= <<>>
                                /\ key \in DOMAIN local) {
                                goto run_client;
                            } else {
                                cur_frame := [
                                    op |-> "R",
                                    key |-> key,
                                    deps |-> [k \in DOMAIN deps |-> deps[k].vc]
                                ];
                                svr_mq := SendToServer(svr_mq, to_svr_id, cli_id, cur_frame);
                            };
                        } else {
                            \* write function in Figure 11
                            cur_frame := [
                                op |-> "W",
                                key |-> key,
                                deps |-> [k \in DOMAIN deps |-> deps[k].vc],
                                local |-> local
                            ];
                            svr_mq := SendToServer(svr_mq, to_svr_id, cli_id, cur_frame);
                        };
                    };
                };
            }; \* end with
            waiting_res:
                await (cli_mq[cli_id] /= <<>>);
                with (res = Head(cli_mq[cli_id])) {
                    cli_mq := [cli_mq EXCEPT ![cli_id] = Tail(cli_mq[cli_id])];
                    \* assert(TypeMeta(res.frame));
                    if (cur_frame.op = "R") {
                        if (deps /= <<>>) {
                            if (cur_frame.key \in DOMAIN deps) {
                                deps := [deps EXCEPT ![cur_frame.key] = res.frame];
                            } else {
                                deps := deps @@ [k \in {cur_frame.key} |-> res.frame];
                            };
                        } else {
                            deps := [k \in {cur_frame.key} |-> res.frame];
                        };
                    } else {
                        if (local /= <<>>) {
                            if (cur_frame.key \in DOMAIN local) {
                                local := [local EXCEPT ![cur_frame.key] = res.frame];
                            } else {
                                local := local @@ [k \in {cur_frame.key} |-> res.frame];
                            };
                        } else {
                            local := [k \in {cur_frame.key} |-> res.frame];
                        };
                    };
                };
        }; \* end while
    lbl_done:
        finished := finished + 1;
}

process(Server \in Servers)
variables svr_id;
          white;
          black;
          msg;
          gvc;
          meta;
          local;
          deps;
{
    init_server:
        svr_id := self;
        white := EmptyWhite;
        black := EmptyBlack;
        gvc := EmptyVC;
    run_server:
        while (finished /= NClient \/ Len(svr_mq[svr_id]) > 0) {
            await (svr_mq[svr_id] /= <<>>);
            msg := Head(svr_mq[svr_id]);
            svr_mq := [svr_mq EXCEPT ![svr_id] = Tail(svr_mq[svr_id])];
            if (msg.type = "client") {
                if (msg.frame.op = "R") {
                    assert(ReadsDepsAreMet(black, white, msg.frame.deps));
                    with (bw = PullDeps2(black, white, msg.frame.deps)) {
                        black := bw[1];
                        white := bw[2];
                    };
                    cli_mq := SendToClient(cli_mq, msg.from, white[msg.frame.key]); 
                    \* assert(TypeMeta(white[msg.frame.key]));
                    if (~UponReadsDepsAreMet(white, msg.frame.deps)) {
                        print("--");
                        print(white);
                        print(msg);
                        print("--");
                        assert(FALSE);
                    };
                } else {
                    \* assert(msg.frame.op = "W");
                    gvc := [gvc EXCEPT ![svr_id] = gvc[svr_id] + 1];
                    meta := [
                        key |-> msg.frame.key,
                        vc |-> gvc,
                        deps |-> msg.frame.deps
                    ];
                    local := {msg.frame.local[k]: k \in DOMAIN msg.frame.local};
                    black := [black EXCEPT ![msg.frame.key] = black[msg.frame.key] \cup {meta} \cup local];
\*                    black := [black EXCEPT ![msg.frame.key] = black[msg.frame.key] \cup {meta}];
                    cli_mq := SendToClient(cli_mq, msg.from, meta); 
                    zzz1: \* merge into one label?
                        svr_mq := SendToNeighbor(svr_mq, svr_id, svr_id, {meta});
\*                        svr_mq := SendToNeighbor(svr_mq, svr_id, svr_id, {meta} \cup local);
                };
            } else {
                if (msg.headid = Neighbor(svr_id)) {
                    gvc := FoldSet(VCMerge, gvc, {x.vc : x \in msg.frame});
                    deps := FoldSet(DepsMerge, EMPTYDEPS, {x.deps : x \in msg.frame});
                    \* gvc := VCMerge(gvc, msg.frame.vc);
                    with (bw = PullDeps2(black, white, deps)) {
                        black := bw[1];
                        \* white := InsertOrMergeMeta(bw[2], msg.frame);
                        white := FoldSet(InsertOrMergeMeta, bw[2], msg.frame);
                    };
                } else {
                    \* black := [black EXCEPT ![msg.frame.key] = black[msg.frame.key] \cup {msg.frame}];
                    black := FoldSet(AppendMeta, black, msg.frame);
                    zzz2:
                        svr_mq := SendToNeighbor(svr_mq, svr_id, msg.headid, msg.frame);
                };
            };
        };
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "2cadd3d8" /\ chksum(tla) = "9bb8fdb5")
\* Process variable local of process Client at line 270 col 11 changed to local_
\* Process variable deps of process Client at line 271 col 11 changed to deps_
CONSTANT defaultInitValue
VARIABLES cli_mq, svr_mq, finished, pc, local_, deps_, cli_id, n_op, 
          cur_frame, svr_id, white, black, msg, gvc, meta, local, deps

vars == << cli_mq, svr_mq, finished, pc, local_, deps_, cli_id, n_op, 
           cur_frame, svr_id, white, black, msg, gvc, meta, local, deps >>

ProcSet == (Clients) \cup (Servers)

Init == (* Global variables *)
        /\ cli_mq = [i \in Clients |-> <<>>]
        /\ svr_mq = [i \in Servers |-> <<>>]
        /\ finished = 0
        (* Process Client *)
        /\ local_ = [self \in Clients |-> defaultInitValue]
        /\ deps_ = [self \in Clients |-> defaultInitValue]
        /\ cli_id = [self \in Clients |-> defaultInitValue]
        /\ n_op = [self \in Clients |-> NOP]
        /\ cur_frame = [self \in Clients |-> defaultInitValue]
        (* Process Server *)
        /\ svr_id = [self \in Servers |-> defaultInitValue]
        /\ white = [self \in Servers |-> defaultInitValue]
        /\ black = [self \in Servers |-> defaultInitValue]
        /\ msg = [self \in Servers |-> defaultInitValue]
        /\ gvc = [self \in Servers |-> defaultInitValue]
        /\ meta = [self \in Servers |-> defaultInitValue]
        /\ local = [self \in Servers |-> defaultInitValue]
        /\ deps = [self \in Servers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "init_client"
                                        [] self \in Servers -> "init_server"]

init_client(self) == /\ pc[self] = "init_client"
                     /\ local_' = [local_ EXCEPT ![self] = <<>>]
                     /\ deps_' = [deps_ EXCEPT ![self] = <<>>]
                     /\ cli_id' = [cli_id EXCEPT ![self] = self]
                     /\ pc' = [pc EXCEPT ![self] = "run_client"]
                     /\ UNCHANGED << cli_mq, svr_mq, finished, n_op, cur_frame, 
                                     svr_id, white, black, msg, gvc, meta, 
                                     local, deps >>

run_client(self) == /\ pc[self] = "run_client"
                    /\ IF n_op[self] > 0
                          THEN /\ n_op' = [n_op EXCEPT ![self] = n_op[self] - 1]
                               /\ \E optype \in {"R", "W"}:
                                    \E to_svr_id \in Servers:
                                      \E key \in Keys:
                                        IF optype = "R"
                                           THEN /\ IF /\ local_[self] /= <<>>
                                                      /\ key \in DOMAIN local_[self]
                                                      THEN /\ pc' = [pc EXCEPT ![self] = "run_client"]
                                                           /\ UNCHANGED << svr_mq, 
                                                                           cur_frame >>
                                                      ELSE /\ cur_frame' = [cur_frame EXCEPT ![self] =              [
                                                                                                           op |-> "R",
                                                                                                           key |-> key,
                                                                                                           deps |-> [k \in DOMAIN deps_[self] |-> deps_[self][k].vc]
                                                                                                       ]]
                                                           /\ svr_mq' = SendToServer(svr_mq, to_svr_id, cli_id[self], cur_frame'[self])
                                                           /\ pc' = [pc EXCEPT ![self] = "waiting_res"]
                                           ELSE /\ cur_frame' = [cur_frame EXCEPT ![self] =              [
                                                                                                op |-> "W",
                                                                                                key |-> key,
                                                                                                deps |-> [k \in DOMAIN deps_[self] |-> deps_[self][k].vc],
                                                                                                local |-> local_[self]
                                                                                            ]]
                                                /\ svr_mq' = SendToServer(svr_mq, to_svr_id, cli_id[self], cur_frame'[self])
                                                /\ pc' = [pc EXCEPT ![self] = "waiting_res"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "lbl_done"]
                               /\ UNCHANGED << svr_mq, n_op, cur_frame >>
                    /\ UNCHANGED << cli_mq, finished, local_, deps_, cli_id, 
                                    svr_id, white, black, msg, gvc, meta, 
                                    local, deps >>

waiting_res(self) == /\ pc[self] = "waiting_res"
                     /\ (cli_mq[cli_id[self]] /= <<>>)
                     /\ LET res == Head(cli_mq[cli_id[self]]) IN
                          /\ cli_mq' = [cli_mq EXCEPT ![cli_id[self]] = Tail(cli_mq[cli_id[self]])]
                          /\ IF cur_frame[self].op = "R"
                                THEN /\ IF deps_[self] /= <<>>
                                           THEN /\ IF cur_frame[self].key \in DOMAIN deps_[self]
                                                      THEN /\ deps_' = [deps_ EXCEPT ![self] = [deps_[self] EXCEPT ![cur_frame[self].key] = res.frame]]
                                                      ELSE /\ deps_' = [deps_ EXCEPT ![self] = deps_[self] @@ [k \in {cur_frame[self].key} |-> res.frame]]
                                           ELSE /\ deps_' = [deps_ EXCEPT ![self] = [k \in {cur_frame[self].key} |-> res.frame]]
                                     /\ UNCHANGED local_
                                ELSE /\ IF local_[self] /= <<>>
                                           THEN /\ IF cur_frame[self].key \in DOMAIN local_[self]
                                                      THEN /\ local_' = [local_ EXCEPT ![self] = [local_[self] EXCEPT ![cur_frame[self].key] = res.frame]]
                                                      ELSE /\ local_' = [local_ EXCEPT ![self] = local_[self] @@ [k \in {cur_frame[self].key} |-> res.frame]]
                                           ELSE /\ local_' = [local_ EXCEPT ![self] = [k \in {cur_frame[self].key} |-> res.frame]]
                                     /\ deps_' = deps_
                     /\ pc' = [pc EXCEPT ![self] = "run_client"]
                     /\ UNCHANGED << svr_mq, finished, cli_id, n_op, cur_frame, 
                                     svr_id, white, black, msg, gvc, meta, 
                                     local, deps >>

lbl_done(self) == /\ pc[self] = "lbl_done"
                  /\ finished' = finished + 1
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << cli_mq, svr_mq, local_, deps_, cli_id, n_op, 
                                  cur_frame, svr_id, white, black, msg, gvc, 
                                  meta, local, deps >>

Client(self) == init_client(self) \/ run_client(self) \/ waiting_res(self)
                   \/ lbl_done(self)

init_server(self) == /\ pc[self] = "init_server"
                     /\ svr_id' = [svr_id EXCEPT ![self] = self]
                     /\ white' = [white EXCEPT ![self] = EmptyWhite]
                     /\ black' = [black EXCEPT ![self] = EmptyBlack]
                     /\ gvc' = [gvc EXCEPT ![self] = EmptyVC]
                     /\ pc' = [pc EXCEPT ![self] = "run_server"]
                     /\ UNCHANGED << cli_mq, svr_mq, finished, local_, deps_, 
                                     cli_id, n_op, cur_frame, msg, meta, local, 
                                     deps >>

run_server(self) == /\ pc[self] = "run_server"
                    /\ IF finished /= NClient \/ Len(svr_mq[svr_id[self]]) > 0
                          THEN /\ (svr_mq[svr_id[self]] /= <<>>)
                               /\ msg' = [msg EXCEPT ![self] = Head(svr_mq[svr_id[self]])]
                               /\ svr_mq' = [svr_mq EXCEPT ![svr_id[self]] = Tail(svr_mq[svr_id[self]])]
                               /\ IF msg'[self].type = "client"
                                     THEN /\ IF msg'[self].frame.op = "R"
                                                THEN /\ Assert((ReadsDepsAreMet(black[self], white[self], msg'[self].frame.deps)), 
                                                               "Failure of assertion at line 365, column 21.")
                                                     /\ LET bw == PullDeps2(black[self], white[self], msg'[self].frame.deps) IN
                                                          /\ black' = [black EXCEPT ![self] = bw[1]]
                                                          /\ white' = [white EXCEPT ![self] = bw[2]]
                                                     /\ cli_mq' = SendToClient(cli_mq, msg'[self].from, white'[self][msg'[self].frame.key])
                                                     /\ IF ~UponReadsDepsAreMet(white'[self], msg'[self].frame.deps)
                                                           THEN /\ PrintT(("--"))
                                                                /\ PrintT((white'[self]))
                                                                /\ PrintT((msg'[self]))
                                                                /\ PrintT(("--"))
                                                                /\ Assert((FALSE), 
                                                                          "Failure of assertion at line 377, column 25.")
                                                           ELSE /\ TRUE
                                                     /\ pc' = [pc EXCEPT ![self] = "run_server"]
                                                     /\ UNCHANGED << gvc, meta, 
                                                                     local >>
                                                ELSE /\ gvc' = [gvc EXCEPT ![self] = [gvc[self] EXCEPT ![svr_id[self]] = gvc[self][svr_id[self]] + 1]]
                                                     /\ meta' = [meta EXCEPT ![self] =         [
                                                                                           key |-> msg'[self].frame.key,
                                                                                           vc |-> gvc'[self],
                                                                                           deps |-> msg'[self].frame.deps
                                                                                       ]]
                                                     /\ local' = [local EXCEPT ![self] = {msg'[self].frame.local[k]: k \in DOMAIN msg'[self].frame.local}]
                                                     /\ black' = [black EXCEPT ![self] = [black[self] EXCEPT ![msg'[self].frame.key] = black[self][msg'[self].frame.key] \cup {meta'[self]} \cup local'[self]]]
                                                     /\ cli_mq' = SendToClient(cli_mq, msg'[self].from, meta'[self])
                                                     /\ pc' = [pc EXCEPT ![self] = "zzz1"]
                                                     /\ white' = white
                                          /\ deps' = deps
                                     ELSE /\ IF msg'[self].headid = Neighbor(svr_id[self])
                                                THEN /\ gvc' = [gvc EXCEPT ![self] = FoldSet(VCMerge, gvc[self], {x.vc : x \in msg'[self].frame})]
                                                     /\ deps' = [deps EXCEPT ![self] = FoldSet(DepsMerge, EMPTYDEPS, {x.deps : x \in msg'[self].frame})]
                                                     /\ LET bw == PullDeps2(black[self], white[self], deps'[self]) IN
                                                          /\ black' = [black EXCEPT ![self] = bw[1]]
                                                          /\ white' = [white EXCEPT ![self] = FoldSet(InsertOrMergeMeta, bw[2], msg'[self].frame)]
                                                     /\ pc' = [pc EXCEPT ![self] = "run_server"]
                                                ELSE /\ black' = [black EXCEPT ![self] = FoldSet(AppendMeta, black[self], msg'[self].frame)]
                                                     /\ pc' = [pc EXCEPT ![self] = "zzz2"]
                                                     /\ UNCHANGED << white, 
                                                                     gvc, deps >>
                                          /\ UNCHANGED << cli_mq, meta, local >>
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << cli_mq, svr_mq, white, black, 
                                               msg, gvc, meta, local, deps >>
                    /\ UNCHANGED << finished, local_, deps_, cli_id, n_op, 
                                    cur_frame, svr_id >>

zzz1(self) == /\ pc[self] = "zzz1"
              /\ svr_mq' = SendToNeighbor(svr_mq, svr_id[self], svr_id[self], {meta[self]})
              /\ pc' = [pc EXCEPT ![self] = "run_server"]
              /\ UNCHANGED << cli_mq, finished, local_, deps_, cli_id, n_op, 
                              cur_frame, svr_id, white, black, msg, gvc, meta, 
                              local, deps >>

zzz2(self) == /\ pc[self] = "zzz2"
              /\ svr_mq' = SendToNeighbor(svr_mq, svr_id[self], msg[self].headid, msg[self].frame)
              /\ pc' = [pc EXCEPT ![self] = "run_server"]
              /\ UNCHANGED << cli_mq, finished, local_, deps_, cli_id, n_op, 
                              cur_frame, svr_id, white, black, msg, gvc, meta, 
                              local, deps >>

Server(self) == init_server(self) \/ run_server(self) \/ zzz1(self)
                   \/ zzz2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Clients: Client(self))
           \/ (\E self \in Servers: Server(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
Inited == \A s \in Servers: white[s] /= defaultInitValue

\* BlacksCoverWhites is a correctness condition meaning a write $w$ in cache server's C-Cache implies on other servers it's either merged into C-Cache or exists in I-Cache.
BlacksCoverWhites ==
    Inited => 
        \A si \in Servers:
            \A sj \in Servers:
                \A k \in DOMAIN white[si]:
                    LET m == FoldSet(MetaMerge, white[si][k], black[sj][k]) IN
                    \/ VCEqual(white[si][k].vc, m.vc)
                    \/ VCHappensBefore(white[si][k].vc, m.vc)
\* PullingEnsureDeps is a correctness condition meaning during integration, all dependencies can be found, as described in Section 5.5.
PullingEnsureDeps ==
    Inited =>
        \A s \in Servers:
            \A k \in DOMAIN white[s]:
                \A kk \in DOMAIN white[s][k].deps:
                    \/ (kk \in DOMAIN white[s] /\ \/ VCEqual(white[s][k].deps[kk], white[s][kk].vc)
                                                  \/ VCHappensBefore(white[s][k].deps[kk], white[s][kk].vc))
                    \/ LET m == FoldSet(MetaMerge, white[s][kk], black[s][kk]) IN
                        \/ VCEqual(white[s][k].deps[kk], m.vc)
                        \/ VCHappensBefore(white[s][k].deps[kk], m.vc)

\* WhiteIsCausalCut is a correctness condition mearning a cache server’s C-cache is always a cut
WhiteIsCausalCut ==
    Inited =>
        \A s \in Servers: CausalCut(white[s])
======
