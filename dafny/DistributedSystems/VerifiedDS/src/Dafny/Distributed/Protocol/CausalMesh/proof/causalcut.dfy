include "../distributed_system.dfy"
include "action.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_CausalCut_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_AllServersAreCausalCutAtAnyTime(
    low_level_behavior:seq<CMState>
)
    requires |low_level_behavior| > 0 
    requires CMInit(low_level_behavior[0])
    requires forall i {:trigger CMNext(low_level_behavior[i], low_level_behavior[i+1])} :: 
                0 <= i < |low_level_behavior| - 1 ==> CMNext(low_level_behavior[i], low_level_behavior[i+1])
    ensures forall i :: 0 <= i < |low_level_behavior| ==> AllServersAreCausalCut(low_level_behavior[i])
{
    assert AllServersAreCausalCut(low_level_behavior[0]);

    var b := ConvertBehaviorSeqToImap(low_level_behavior);
    lemma_AllServersAreCausalCutPrefix(b, |low_level_behavior|-1);
}

lemma lemma_AllServersAreCausalCutPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllServersAreCausalCut(b[0])
    ensures forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[j])
    decreases i
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_AllServersAreCausalCutPrefix(b, i-1);
    assert forall j :: 0 <= j <= i - 1 ==> AllServersAreCausalCut(b[j]);

    lemma_CMNextRemainsCausalCut(b, i-1);
    assert AllServersAreCausalCut(b[i]);
    lemma_BehaviorPrefixIsCausalCut(b, i);
    assert forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[j]);
}

lemma lemma_BehaviorPrefixIsCausalCut(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> AllServersAreCausalCut(b[j])
    requires AllServersAreCausalCut(b[i])
    ensures forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[j])
{

}


lemma lemma_CMNextRemainsCausalCut(b:Behavior<CMState>, i:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    // requires 0 <= i < |low_level_behavior| - 1
    requires CMNext(b[i], b[i+1])
    requires AllServersAreCausalCut(b[i])
    ensures AllServersAreCausalCut(b[i+1])
{
    var ps := b[i];
    var ps' := b[i+1];

    if ps.servers == ps'.servers {
        assert AllServersAreCausalCut(ps');
    } 
    else {
        var idx :| 0 <= idx < |ps.servers| && ps.servers[idx] != ps'.servers[idx];
        lemma_CMNextServerRemainsCausalCut(b, i, idx);
    }
}

lemma lemma_CMNextServerRemainsCausalCut(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    requires AllServersAreCausalCut(b[i])
    ensures AllServersAreCausalCut(b[i+1])
{
    var s := b[i].servers[idx].s;
    var s' := b[i+1].servers[idx].s;

    var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, idx);
    assert CMNextServer(b[i], b[i+1], idx, ios);
    assert LServerNext(b[i].servers[idx], b[i+1].servers[idx], ios);
    assert ServerValid(s);

    assert ios[0].LIoOpReceive?;
    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);
    assert p.msg.Message_Read? || p.msg.Message_Write? || p.msg.Message_Propagation?;

    assert ServerProcessPacket(s, s', ios);

    if p.msg.Message_Read? {
        assert ReceiveRead(s, s', p, sp);
        // lemma_PullDeps2RemainsCausalCut(s.icache, s.ccache, p.msg.deps_read);
        assert CausalCut(s'.ccache);
    } 
    else 
    if p.msg.Message_Write? {
        assert ReceiveWrite(s, s', p, sp);
        assert CausalCut(s'.ccache);
    } 
    else {
        assert p.msg.Message_Propagation?;
        assert ReceivePropagate(s, s', p, sp);
        if s.next == p.msg.start {
            // var deps := set x | x in p.msg.metas :: x.deps;
            // var new_deps := FoldDependency(map[], deps);
            var deps := p.msg.meta.deps;
            // lemma_PullDeps2RemainsCausalCut(s.icache, s.ccache, new_deps);
        }
        
        assert CausalCut(s'.ccache);
    }
 
}

// lemma lemma_ProcessReadRemainsCausalCut(s:Server, s':Server, p:Packet, sp:seq<Packet>)
//     requires p.msg.Message_Read?
//     requires ServerValid(s)
//     requires PacketValid(p) 
//     requires ReceiveRead(s, s', p, sp)
//     ensures ServerValid(s')
// {

// }

// lemma lemma_AllServersAreCausalSetPrefix(
//     b:Behavior<CMState>,
//     i:int
// )
//     requires 0 <= i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires AllServersAreCausalCut(b[0])
//     ensures forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[j])
//     decreases i
// {
//     if i == 0 {
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_AllServersAreCausalSetPrefix(b, i-1);
//     assume forall j :: 0 <= j < i ==> AllServersAreCausalCut(b[j]);

//     lemma_CMNextRemainsCausalCut(b, i-1);
//     assert AllServersAreCausalCut(b[i]);
// }

// lemma lemma_CMNextRemainsCausalCut(low_level_behavior:seq<CMState>, i:int)
//     requires |low_level_behavior| > 1
//     requires 0 <= i < |low_level_behavior| - 1
//     requires CMNext(low_level_behavior[i], low_level_behavior[i+1])
//     requires AllServersAreCausalCut(low_level_behavior[i])
//     // ensures AllServersAreCausalCut(low_level_behavior[i+1])
// {
//     var ps := low_level_behavior[i];
//     var ps' := low_level_behavior[i+1];

//     if ps.servers == ps'.servers {
//         assert AllServersAreCausalCut(ps');
//     } 
//     // else {
//     //     assume AllServersAreCausalCut(ps');
//     // }
// }

// function PullTodos2(icache:ICache, ccache:CCache, todos:Dependency) : (c:(ICache, CCache))
//     requires ICacheValid(icache)
//     requires CCacheValid(ccache)
//     requires DependencyValid(todos) 
//     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
//     requires forall k :: k in todos ==> k in icache 
//     requires ReadsDepsAreMet(icache, ccache, todos)
//     requires CausalCut(ccache)
//     // requires forall k :: k in todos ==> k in ccache // is this true?
//     // ensures var c := PullTodos(icache, ccache, todos);
//     ensures ICacheValid(c.0)
//     ensures CCacheValid(c.1)
//     // ensures forall k :: k in todos ==> k in c.0 && k in c.1
//     ensures forall k :: k in icache ==> k in c.0
//     ensures forall k :: k in ccache ==> k in c.1 && (VCHappendsBefore(ccache[k].vc, c.1[k].vc) || VCEq(ccache[k].vc, c.1[k].vc))
//     ensures forall k :: k in todos ==> k in c.1 && (VCHappendsBefore(todos[k], c.1[k].vc) || VCEq(todos[k], c.1[k].vc))
//     // ensures CausalCut(c.1)
//     decreases |todos|
// {
//     if |todos| == 0 then 
//         (icache, ccache)
//     else
//         var k :| k in todos;
//         var vc := todos[k];
//         if VCHappendsBefore(vc, ccache[k].vc) || VCEq(vc, ccache[k].vc) then 
//             var todos' := RemoveElt(todos, k);
//             var res := PullTodos(icache, ccache, todos');
//             res
//         else 
//             // assert VCHappendsBefore(ccache[k].vc, vc);
//             var metas := icache[k];
//             var init := Meta(k, EmptyVC(), map[]);
//             var domain := icache.Keys;
//             var pair := RemoveNotLarger(metas, vc, {}, init, domain);
//             assert pair.1.key == k;
//             assert VCEq(pair.1.vc, vc);
//             assert MetaValid(pair.1);
//             assert forall m :: m in metas ==> m.key == pair.1.key;
//             assert forall kv :: kv in pair.0 ==> forall kk :: kk in kv.deps ==> kk in icache;
//             var updated_icache := icache[k := pair.0];
//             // var updated_ccache := ccache[k := MetaMerge(ccache[k], pair.1)];

//             // assert VCHappendsBefore(todos[k], pair.1.vc) || VCEq(todos[k], pair.1.vc);
//             var updated_ccache := InsertIntoCCache(ccache, pair.1); // this is different from the TLA+ spec
//             // assert k in updated_ccache && (VCHappendsBefore(todos[k], updated_ccache[k].vc) || VCEq(todos[k], updated_ccache[k].vc));

//             assert forall kk :: kk in Keys_domain ==> kk in icache && kk in ccache;
//             assert forall kk :: kk in icache ==> kk in updated_icache;
//             assert forall kk :: kk in ccache ==> kk in updated_ccache;
//             lemma_DomainRemains(icache, ccache, updated_icache, updated_ccache);
//             assert forall kk :: kk in Keys_domain ==> kk in updated_icache && kk in updated_ccache;

//             lemma_InsertNotSmallerVCIntoCCache(ccache, pair.1);
//             assert VCHappendsBefore(vc, updated_ccache[k].vc) || VCEq(updated_ccache[k].vc, vc);

//             var todos' := RemoveElt(todos, k);
//             var res := PullTodos(updated_icache, updated_ccache, todos');
//             assert forall kk :: kk in todos' ==> kk in res.1; //&& (VCHappendsBefore(todos'[kk], res.1[kk].vc) || VCEq(todos'[kk], res.1[kk].vc));
//             assert todos.Keys == todos'.Keys + {k};
//             assert forall kk :: kk in updated_ccache ==> kk in res.1 && (VCHappendsBefore(updated_ccache[kk].vc, res.1[kk].vc) || VCEq(updated_ccache[kk].vc, res.1[kk].vc));
//             assert k in res.1 && (VCHappendsBefore(todos[k], res.1[k].vc) || VCEq(todos[k], res.1[k].vc));
//             // assert forall kk :: kk in todos' ==> kk in res
//             res
// }

// lemma lemma_PullDeps2RemainsCausalCut(icache:ICache, ccache:CCache, deps:Dependency)
//     requires ICacheValid(icache)
//     requires CCacheValid(ccache)
//     requires forall k :: k in ccache ==> k in icache
//     requires DependencyValid(deps)
//     requires forall k :: k in deps ==> k in icache
//     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
//     // requires ReadsDepsAreMet(icache, ccache, deps)
//     requires CausalCut(ccache)
//     ensures var (new_icache, new_ccache) := PullDeps2(icache, ccache, deps);
//             CausalCut(new_ccache)
// {
//     var domain := icache.Keys + deps.Keys;
//     var todos := GetDeps2(icache, deps, map[], domain);
//     // lemma_GetDeps2AreMet(icache, ccache, todos);
//     // var res := PullTodos(icache, ccache, todos);
//     // assert ReadsDepsAreMet(res.0, res.1, todos);
//     // assert UponReadsDepsAreMet(res.1, deps); 
//     lemma_PullTodosRemainCausalCut(icache, ccache, todos);
// }

// lemma {:axiom} lemma_PullTodosRemainCausalCut(icache:ICache, ccache:CCache, todos:Dependency)
//     requires ICacheValid(icache)
//     requires CCacheValid(ccache)
//     requires DependencyValid(todos) 
//     requires forall k :: k in todos ==> k in icache  
//     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
//     requires CausalCut(ccache)
//     ensures var (new_icache, new_ccache) := PullTodos(icache, ccache, todos);
//             CausalCut(new_ccache)
// {
//     if |todos| == 0 then 
//         returns;
//     else 

// }

// lemma lemma_InsertIntoCCacheRemainCausalCut(c:CCache, m:Meta)
//     requires CCacheValid(c)
//     requires MetaValid(m)
//     requires CausalCut(c)
//     requires forall k :: k in Keys_domain ==> k in c
//     // how to guarantee this?
//     requires forall kk :: kk in m.deps ==> VCHappendsBefore(m.deps[kk], c[kk].vc) || VCEq(m.deps[kk], c[kk].vc)
//     ensures var new_cache := InsertIntoCCache(c, m);
//             CausalCut(new_cache)
// {
//     assert m.key in c;
//     var m1 := c[m.key];
//     assert forall kk :: kk in m1.deps ==> 
//         kk in c && (VCHappendsBefore(m1.deps[kk], c[kk].vc) || VCEq(m1.deps[kk], c[kk].vc)); 

//     var new_deps := DependencyMerge(m.deps, m1.deps); 
//     var new_vc := VCMerge(m.vc, m1.vc);
    
//     // var k :| k in m.deps && k in m1.deps;
//     // assert new_deps[k] == VCMerge(m.deps[k], m1.deps[k]);

//     forall k | k in new_deps 
//     {
//         if k in m.deps && k in m1.deps {
//             assert new_deps[k] == VCMerge(m.deps[k], m1.deps[k]);
//             assert forall i :: 0 <= i < |new_deps[k]| ==> new_deps[k][i] == m.deps[k][i] || new_deps[k][i] == m1.deps[k][i];
//             assert VCHappendsBefore(new_deps[k], c[k].vc) || VCEq(new_deps[k], c[k].vc);
//         }
//         else if k in m1.deps {
//             assert new_deps[k] == m1.deps[k];
//             assert VCHappendsBefore(new_deps[k], c[k].vc) || VCEq(new_deps[k], c[k].vc);
//         }
//         else { 
//             assert new_deps[k] == m.deps[k];
//             assert VCHappendsBefore(new_deps[k], c[k].vc) || VCEq(new_deps[k], c[k].vc);
//         }
//     } 
// }
}