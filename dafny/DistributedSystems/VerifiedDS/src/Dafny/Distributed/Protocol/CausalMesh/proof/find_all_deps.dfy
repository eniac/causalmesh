include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_FindAllDeps_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_PullDeps_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma {:axiom} lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(
//     b:Behavior<CMState>,
//     i:int,
//     todos:map<Key, Meta>,
//     m:Meta
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//                     && forall kk :: kk in todos[k].deps ==> 
//                         VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
//     requires MetaValid(m)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers2(b, i, k, todos[k].vc)  && AllVersionsInDepsAreMetOnAllServers2(b, i, todos[k].deps)
//     requires AVersionIsMetOnAllServers2(b, i, m.key, m.vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, m.deps)
//     ensures var res := AddMetaToMetaMap(todos, m);
//             forall k :: k in res ==> AVersionIsMetOnAllServers2(b, i, k, res[k].vc)  && AllVersionsInDepsAreMetOnAllServers2(b, i, res[k].deps)
// // {

// // }

// lemma {:axiom} lemma_AllVersionsInDepsAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     deps:Dependency
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires DependencyValid(deps)
//     ensures AllVersionsInDepsAreMetOnAllServers2(b, i, deps)

// lemma lemma_AllVersionsInDepsAreMetOnAllServers2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int, 
//     icache:ICache,
//     deps:Dependency,
//     meta:Meta
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires DependencyValid(deps)
//     requires MetaValid(meta)
//     requires forall k :: k in Keys_domain ==> k in icache
//     requires AllVersionsInDepsAreMetOnAllServers2(b, i, deps)
//     requires meta.key in deps
//     requires meta in icache[meta.key] && VCEq(meta.vc, deps[meta.key])
//     ensures AllVersionsInDepsAreMetOnAllServers2(b, i, meta.deps)
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers2();
// }

function GetMetasOfAllDepsGlobalView(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    icache:ICache,
    deps:Dependency,
    todos:map<Key, Meta>,
    domain:set<Key>
) : (res:map<Key, Meta>)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    requires DependencyValid(deps)
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    requires forall k :: k in deps ==> k in domain 

    requires AllVersionsInDepsAreMetOnAllServers2(b, i, deps)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers2(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, todos[k].deps)

    ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    ensures forall k :: k in res ==> AVersionIsMetOnAllServers2(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, res[k].deps)
    decreases |icache.Values|, |deps|
{
    // lemma_BehaviorValidImpliesOneStepValid(b, i);
    reveal_AllVersionsInDepsAreMetOnAllServers2();
    // reveal_AllVersionsInCCacheAreMetOnAllServers();
    
    // assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc); //&& AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
    if |deps| == 0 then 
        todos
    else 
        var k :| k in deps;
        var new_deps := RemoveElt(deps, k);
        if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
            var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
            res
        else 
            // var metas := set m | m in icache[k] && VCEq(m.vc, deps[k]);
            if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
                var m :| m in icache[k] && VCEq(m.vc, deps[k]);
                var meta := m;
                
                
                // lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                assert (VCHappendsBefore(meta.vc, meta.vc) || VCEq(meta.vc, meta.vc));

                var new_cache := icache[k:= icache[k] - {meta}];
                assert icache[k] >= {meta};
                lemma_MapRemoveSubsetOfTheValOfKey(icache, k, {meta});
                assert |new_cache.Values| < |icache.Values|;

                lemma_AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
                assume AllVersionsInDepsAreMetOnAllServers2(b, i, meta.deps);

                var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, meta.deps, todos, domain);

                assume forall k :: k in res ==> AVersionIsMetOnAllServers2(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, res[k].deps);
                assume AVersionIsMetOnAllServers2(b, i, k, meta.vc);

                var todos' := AddMetaToMetaMap(res, meta);

                assert AllVersionsInDepsAreMetOnAllServers2(b, i, new_deps);
                lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
                assert forall k :: k in todos' ==> AVersionIsMetOnAllServers2(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, todos'[k].deps);

                var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
                res'
            else 
                var initial := EmptyMeta(k);
                var meta := initial.(vc:=deps[k]);
                assert AllVersionsInDepsAreMetOnAllServers2(b, i, deps);
                assert forall k :: k in todos ==> AVersionIsMetOnAllServers2(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, todos[k].deps);
                assert AVersionIsMetOnAllServers2(b, i, meta.key, meta.vc);
                assert AllVersionsInDepsAreMetOnAllServers2(b, i, meta.deps);
                var todos' := AddMetaToMetaMap(todos, meta);
                lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, todos, meta);
                assert forall k :: k in todos' ==> AVersionIsMetOnAllServers2(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers2(b, i, todos'[k].deps);
                
                var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
                res
}
}