include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
// include "propagation.dfy"
include "propagation_lemma3.dfy"
include "always_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"
include "message_propagation.dfy"
include "message_write.dfy"

module CausalMesh_Proof_MetaIsMet_i {
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
// import opened CausalMesh_Proof_PropagationLemma_i
import opened CausalMesh_Proof_PropagationLemma3_i
// import opened CausalMesh_Proof_Propagation_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened CausalMesh_Proof_MessagePropagation_i
import opened CausalMesh_Proof_MessageWrite_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma lemma_MetaIsMetImpliesItsDepsAreMet(
//     b:Behavior<CMState>,
//     i:int,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires MetaValid(meta)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1 {
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         assert CMNext(b[i-1], b[i]);
//         lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(b, i, meta);
//         // reveal_AllVersionsInDepsAreMetOnAllServers();
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         return;
//     }

//     assert 0 < i - 1;

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if AVersionIsMetOnAllServers(b, i-1, meta.key, meta.vc)
//     {
//         lemma_MetaIsMetImpliesItsDepsAreMet(b, i-1, meta);
//         assume ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
//         assert i > 1;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert DependencyValid(meta.deps);
//         assume AllVersionsInDepsAreMetOnAllServers(b, i-1, meta.deps);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, meta.deps);
//         return;
//     }

//     // var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, )
    
//     // how to find the node that is the tail of propagation of meta?

//     var ios:seq<CMIo>;
//     var idx :| 0 <= idx < Nodes;

//     assert CMNext(b[i-1], b[i]);
//     assert 0 < i; 
//     assert IsValidBehaviorPrefix(b, i);
//     assert MetaValid(meta);
//     assert 0 <= idx < Nodes;

//     lemma_IosIsPropagationTail(b, i, idx, ios, meta);

//     assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));

//     var p_pro := ios[0].r;
//     assert p_pro.dst == idx;

//     lemma_PropagationAtTail2(b, i, idx, p_pro, ios);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p_pro.msg.meta.deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
// }

// lemma lemma_MetaIsMetImpliesItsDepsAreMet2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
//     requires MetaValid(meta)
//     requires AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc)
//     // requires meta in b[i].servers[idx].s.icache[meta.key]
//     // requires meta != EmptyMeta(meta.key)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1 {
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         assert CMNext(b[i-1], b[i]);
//         lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne2(b, i);
//         // reveal_AllVersionsInDepsAreMetOnAllServers();
//         // assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         assert b[i].servers[idx].s.icache == InitICache();
//         assert b[i].servers[idx].s.ccache == InitCCache();
//         if meta != EmptyMeta(meta.key){
//             if VCHappendsBefore(EmptyMeta(meta.key).vc, meta.vc) {
//                 assert meta !in b[i].servers[idx].s.icache[meta.key];
//                 assert !(VCHappendsBefore(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc) || VCEq(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc));
//                 var m := FoldMetaSet2(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert b[i].servers[idx].s.ccache[meta.key] == EmptyMeta(meta.key);
//                 assert forall m :: m in b[i].servers[idx].s.icache[meta.key] ==> m == EmptyMeta(meta.key);
//                 lemma_FoldEmptyMetasResultInEmptyMeta(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert m == EmptyMeta(meta.key);
//                 assert !AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc);
//                 assert false;
//             } else {
//                 lemma_MetaWithNonEmptyDepsImpliesTheVCLargerThanZero(meta);
//                 assert meta !in b[i].servers[idx].s.icache[meta.key];
//                 assert !(VCHappendsBefore(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc) || VCEq(meta.vc, b[i].servers[idx].s.ccache[meta.key].vc));
//                 var m := FoldMetaSet2(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert b[i].servers[idx].s.ccache[meta.key] == EmptyMeta(meta.key);
//                 assert forall m :: m in b[i].servers[idx].s.icache[meta.key] ==> m == EmptyMeta(meta.key);
//                 lemma_FoldEmptyMetasResultInEmptyMeta(b[i].servers[idx].s.ccache[meta.key], b[i].servers[idx].s.icache[meta.key]);
//                 assert m == EmptyMeta(meta.key);
//                 assert !AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, meta.key, meta.vc);
//                 assert false;
//             }
//         } 
//         else {
//             reveal_AllVersionsInDepsAreMetOnAllServers();
//             assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//         }
//         return;
//     }

//     assert 0 < i - 1;

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if AVersionIsMetOnAllServers(b, i-1, meta.key, meta.vc)
//     {
//         // assume meta in b[i-1].servers[idx].s.icache[meta.key];
//         lemma_MetaIsMetImpliesItsDepsAreMet2(b, i-1, idx, meta);
//         assume ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
//         assert i > 1;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert DependencyValid(meta.deps);
//         assume AllVersionsInDepsAreMetOnAllServers(b, i-1, meta.deps);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, meta.deps);
//         return;
//     }

//     // var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, )
    
//     // how to find the node that is the tail of propagation of meta?

//     var ios:seq<CMIo>;
//     var idx :| 0 <= idx < Nodes;

//     assert CMNext(b[i-1], b[i]);
//     assert 0 < i; 
//     assert IsValidBehaviorPrefix(b, i);
//     assert MetaValid(meta);
//     assert 0 <= idx < Nodes;

//     lemma_IosIsPropagationTail(b, i, idx, ios, meta);

//     assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));

//     var p_pro := ios[0].r;
//     assert p_pro.dst == idx;

//     lemma_PropagationAtTail2(b, i, idx, p_pro, ios);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p_pro.msg.meta.deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
// }

// lemma {:axiom} lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne(
//     b:Behavior<CMState>,
//     i:int
//     ,
//     meta:Meta
// )
//     requires i == 1 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires MetaValid(meta)
//     ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Propagation?
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
// // {
// //     assert CMNext(b[i-1], b[i]);
// // }

lemma lemma_MetaIsMetImpliesItsDepsAreMetForIndexOne2(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires 0 <= idx < Nodes
    // requires meta in b[i].servers[idx].s.icache[meta.key]
    // requires MetaValid(meta)
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Propagation?
    // ensures AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
{
    assert CMNext(b[i-1], b[i]);
}

// lemma {:axiom} lemma_IosIsPropagationTail(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     ios:seq<CMIo>,
//     meta:Meta
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires MetaValid(meta)
//     requires 0 <= idx < Nodes
//     ensures |ios| > 1
//     ensures ios[0].LIoOpReceive?
//     ensures ios[0].r.msg.Message_Propagation?
//     ensures ios[0].r in b[i-1].environment.sentPackets
//     ensures ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
//     ensures ios[0].r.msg.start == b[i-1].servers[idx].s.next
//     ensures ios[0].r.msg.round == 2
//     ensures ios[0].r.dst == idx
//     ensures ios[0].r.msg.meta == meta
//     // ensures forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)

// lemma {:axiom} lemma_MetaIsMetImpliesAllPreviousMetasAreMet(
//     b:Behavior<CMState>,
//     i:int,
//     meta:Meta,
//     meta2:Meta
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires MetaValid(meta)
//     requires MetaValid(meta2)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires VCHappendsBefore(meta2.vc, meta.vc) || VCEq(meta2.vc, meta.vc)
//     ensures AVersionIsMetOnAllServers(b, i, meta2.key, meta2.vc)

lemma lemma_AVersionIsPropagatedImpliesAllPreviousDepsAreMet(
    b:Behavior<CMState>,
    i:int,
    vc:VectorClock,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
    requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    forall k | k in deps 
        ensures AVersionIsMetOnAllServers(b, i, k, deps[k])
    {
        assert VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc);
        lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, vc, k, deps[k]);
        assert AVersionIsMetOnAllServers(b, i, k, deps[k]);
    }
}

// lemma lemma_AVersionOnServerImpliesPropogateInEnvironment(
//     b:Behavior<CMState>,
//     i:int,
// )

// lemma lemma_ActionThatInsertMeteIntoICache(
//     ps:CMState,
//     ps':CMState,
//     idx:int,
//     k:Key,
//     meta:Meta
// ) 
// returns (
//     start:int
// )
//     requires CMNext(ps, ps')
//     requires 0 <= idx < Nodes
//     requires k in ps.servers[idx].s.icache && k in ps'.servers[idx].s.icache
//     requires meta !in ps.servers[idx].s.icache[k]
//     requires meta in ps'.servers[idx].s.icache[k]
// {
//     var s := ps.servers[idx];
//     var s' := ps'.servers[idx];

//     var ios:seq<CMIo> :| CMNextServer(ps, ps', idx, ios);

//     assert CMNextServer(ps, ps', idx, ios);
//     assert LServerNext(ps.servers[idx], ps'.servers[idx], ios);

//     assert |ios| >= 1;
//     assert !ios[0].LIoOpTimeoutReceive?;
//     assert ios[0].LIoOpReceive?;
//     assert PacketValid(ios[0].r);

//     var p := ios[0].r;
//     var sp := ExtractSentPacketsFromIos(ios);

//     assert p.msg.Message_Propagation? || p.msg.Message_Write?;

//     if p.msg.Message_Write? {
//         return idx;
//     } else {
//         assert p.msg.Message_Propagation?;
//         // var j, p_write := lemma_PropagationHasInitialWriteMessage(b, i, p);
//         return idx;
//     }
// }


lemma lemma_AllServersMetasInCacheSmallThanPVCIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    pvc:VectorClock,
    nodes:seq<int>
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 < i
    // requires 0 <= idx < Nodes
    requires CMNext(b[i-1], b[i])
    requires VectorClockValid(pvc)
    requires NodesAreComplete(nodes)
    ensures AllServersMetasInCacheSmallThanPVCIsMetOnAllServers(b, i, pvc)
{
    forall j | 0 <= j < |b[i].servers|
        ensures var s :=  b[i].servers[j].s;
                forall k :: k in s.icache ==>
                forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
    {
        lemma_AllMetasInICacheSmallThanPVCIsMetOnAllServers(b, i, j, pvc, nodes);
        var s :=  b[i].servers[j].s;
        assert forall k :: k in s.icache ==>
                forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc);
    }
    reveal_AllServersMetasInCacheSmallThanPVCIsMetOnAllServers();
    assert AllServersMetasInCacheSmallThanPVCIsMetOnAllServers(b, i, pvc);
}

lemma lemma_AllMetasInICacheSmallThanPVCIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    pvc:VectorClock,
    nodes:seq<int>
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 < i
    requires 0 <= idx < Nodes
    requires CMNext(b[i-1], b[i])
    // requires ServerValid(b[i].servers[idx].s)
    requires VectorClockValid(pvc)
    // requires |nodes| > 1
    // requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    requires NodesAreComplete(nodes)
    ensures var s := b[i].servers[idx].s;
            forall k :: k in s.icache ==>
                forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    var s := b[i].servers[idx].s;
    forall k | k in s.icache 
        ensures forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
    {
        forall m | m in s.icache[k]
            ensures (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
        {
            if m != EmptyMeta(m.key) && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)){
                var j, start := lemma_FindTheSourceOfMetaInICache(b, i-1, idx, k, m);
                assert j < i;
                assert 0 <= start < Nodes;
                reveal_NodesAreComplete();
                assert start in nodes;
                lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, pvc, m.key, m.vc);
            } else if (m == EmptyMeta(m.key)) {
                assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
                assert (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc));
            }
        }
    }
    assert forall k :: k in s.icache ==>
            forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc);
}


lemma lemma_FindTheSourceOfMetaInICache(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    k:Key,
    meta:Meta
) 
returns (
    j:int,
    start:int
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires CMNext(b[i], b[i+1])
    requires 0 <= idx < Nodes
    requires k in Keys_domain
    requires meta.key == k
    requires k in b[i+1].servers[idx].s.icache
    requires k in b[i].servers[idx].s.icache
    requires meta != EmptyMeta(meta.key);
    requires meta in b[i+1].servers[idx].s.icache[k]
    ensures 0 <= start < Nodes
    ensures j <= i
{
    if i == 0 {
        assert b[i+1].servers[idx].s.icache == InitICache();
        assert meta != EmptyMeta(meta.key);
        assert meta !in InitICache()[k];
        assert meta !in b[i+1].servers[idx].s.icache[k];
        assert false;
        return;
    }

    if meta in b[i].servers[idx].s.icache[k]
    {
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        
        assert CMNext(b[i-1], b[i]);
        assert ServerValid(b[i-1].servers[idx].s);
        assert ServerValid(b[i].servers[idx].s);
        assert k in b[i].servers[idx].s.icache;
        assert k in b[i-1].servers[idx].s.icache;
        
        j, start :=
        lemma_FindTheSourceOfMetaInICache(b, i-1, idx, k, meta);
        return;
    }

    // lemma_AssumptionsMakeValidTransition(b, i-1);
    // lemma_ConstantsAllConsistent(b, i);
    // lemma_ConstantsAllConsistent(b, i-1);

    assert IsValidBehaviorPrefix(b, i+1);
    assert 0 <= i;
    assert CMNext(b[i], b[i+1]);
    assert 0 <= idx < Nodes;
    assert k in b[i].servers[idx].s.icache && k in b[i+1].servers[idx].s.icache;
    assert meta !in b[i].servers[idx].s.icache[k];
    assert meta in b[i+1].servers[idx].s.icache[k];

    j, start := lemma_FindTheSourceOfAInsertedMeta(b, i, idx, k, meta);
}

lemma lemma_FindTheSourceOfAInsertedMeta(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    k:Key,
    meta:Meta
) 
returns (
    j:int,
    start:int
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires CMNext(b[i], b[i+1])
    requires 0 <= idx < Nodes
    requires k in b[i].servers[idx].s.icache && k in b[i+1].servers[idx].s.icache
    requires meta !in b[i].servers[idx].s.icache[k]
    requires meta in b[i+1].servers[idx].s.icache[k]
    ensures 0 <= start < Nodes
    ensures j <= i
{
    var s := b[i].servers[idx];
    var s' := b[i+1].servers[idx];

    var ios:seq<CMIo> :| CMNextServer(b[i], b[i+1], idx, ios);

    assert CMNextServer(b[i], b[i+1], idx, ios);
    assert LServerNext(b[i].servers[idx], b[i+1].servers[idx], ios);

    assert |ios| >= 1;
    assert !ios[0].LIoOpTimeoutReceive?;
    assert ios[0].LIoOpReceive?;
    assert PacketValid(ios[0].r);

    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);

    assert p.msg.Message_Propagation? || p.msg.Message_Write?;

    if p.msg.Message_Write? {
        
        assert |sp| > 0;
        var p_pro := sp[1];
        assert ReceiveWrite(s.s, s'.s, p, sp);
        assert p_pro.msg.Message_Propagation?;
        assert p_pro.src == s.s.id;
        reveal_ServerIdsAreMatch();
        assert s.s.id == idx;
        assert p_pro.src == idx;

        if k == p.msg.key_write {
            j := i;
            start := idx;
        } else {
            var local_metas := set m | m in p.msg.local.Values;
            lemma_MetaInMetas(meta, local_metas);
            assume meta in local_metas;
            assert meta.key == k;
            assert forall k :: k in p.msg.local ==> p.msg.local[k].key == k;
            assert k in p.msg.local;
            assert exists m :: m in local_metas && m.key == k;

            // assert Nodes <= p.src < Nodes + Clients;
            // assert p.msg.Message_Write?;
            // assert p in b[i+1].environment.sentPackets;
            // assume p !in b[i].environment.sentPackets;
            var jj, client, ios1 := lemma_FindTheClientThatSentWriteContainsMeta(b, i, p, k, meta);
            assert IsValidBehaviorPrefix(b, jj);
            assert 0 <= jj-1;
            lemma_BehaviorValidImpliesOneStepValid(b, jj);
            assert CMNext(b[jj-1], b[jj]);
            assert 0 <= client < Clients;
            assert k in b[jj].clients[client].c.local;
            assert meta == b[jj].clients[client].c.local[k];
            var jjj, p_wreply := lemma_MetasInClientLocalHasCorrspondingWriteMessage(b, jj-1, client, k, meta);
            j := jjj;
            start := p_wreply.src;
            assert jjj <= i;
            assert 0 <= p_wreply.src < Nodes;
        }
        // assert k == p.msg.key_write;

        // assert p_pro.msg.key == k;
        // assert exists pp:Packet :: pp.msg.Message_Propagation? && pp.src == idx && pp in b[i+1].environment.sentPackets;
    } else {
        assert p.msg.Message_Propagation?;
        var jj, p_write := lemma_PropagationHasInitialWriteMessage(b, i, p);
        j := jj;
        start := p_write.dst;
    }
}

lemma {:axiom} lemma_MetaInMetas(meta:Meta, metas:set<Meta>)
    ensures meta in metas



lemma {:axiom} lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(
    b:Behavior<CMState>,
    i:int,
    vc:VectorClock,
    key:Key,
    vc2:VectorClock
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires VectorClockValid(vc2)
    requires VectorClockValid(vc)
    requires key in Keys_domain
    requires VCHappendsBefore(vc2, vc) || VCEq(vc2, vc)
    ensures AVersionIsMetOnAllServers(b, i, key, vc2)
}