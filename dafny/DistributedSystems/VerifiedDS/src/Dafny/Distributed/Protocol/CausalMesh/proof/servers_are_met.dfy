include "../distributed_system.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "environment.dfy"
include "deps_are_met.dfy"
include "read_reply_is_met.dfy"
include "propagation.dfy"
include "meta_is_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ServersAreMet_i {
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
import opened CausalMesh_Proof_Environment_i
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened CausalMesh_Proof_Propagation_i
import opened CausalMesh_Proof_PropagationLemma2_i
import opened CausalMesh_Proof_PropagationLemma3_i
import opened CausalMesh_Proof_MetaIsMet_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma lemma_AllServersAreMetAtAnyTime(
//     low_level_behavior:seq<CMState>
// )
//     requires |low_level_behavior| > 0 
//     requires CMInit(low_level_behavior[0])
//     requires forall i {:trigger CMNext(low_level_behavior[i], low_level_behavior[i+1])} :: 
//                 0 <= i < |low_level_behavior| - 1 ==> CMNext(low_level_behavior[i], low_level_behavior[i+1])
//     // ensures forall i :: 0 <= i < |low_level_behavior| ==> AllServersAreMet(low_level_behavior[i])
// {
//     assert AllServersAreCausalCut(low_level_behavior[0]);

//     var b := ConvertBehaviorSeqToImap(low_level_behavior);
//     lemma_AllServersAreMetPrefix(b, |low_level_behavior|-1);
// }



lemma lemma_AllServersAreMetPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllServersAreMet(b, j)
    decreases i
{
    if i <= 1 {
        if i == 1 {
            lemma_BehaviorValidImpliesOneStepValid(b, i);
            lemma_AllServersAreMetForIndexOne(b, i);
        }
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_AllServersAreMetPrefix(b, i-1);

    assume forall j :: 0 < j <= i - 1 ==> AllServersAreMet(b, j);

    lemma_ServersAreMetForCMNext(b, i-1);
    assert AllServersAreMet(b, i);
    lemma_BehaviorPrefixAllServersAreMet(b, i);
    assert forall j :: 0 < j <= i ==> AllServersAreMet(b, j);
}

lemma lemma_VCRelationIsTransitiveForDeps(
    deps:Dependency,
    vc1:VectorClock,
    vc2:VectorClock
)
    requires DependencyValid(deps)
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc1) || VCEq(deps[k], vc1)
    requires VCHappendsBefore(vc1, vc2) || VCEq(vc1, vc2)
    ensures forall k :: k in deps ==> VCHappendsBefore(deps[k], vc2) || VCEq(deps[k], vc2)
{

}


lemma lemma_AllServersAreMetForIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    ensures AllServersAreMet(b, i)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    assert CMNext(b[i-1], b[i]);

    assert CMInit(b[i-1]);
    assert forall j :: 0 <= j < |b[i-1].servers| ==> ServerInit(b[i-1].servers[j].s, j);
    assert forall j :: 0 <= j < |b[i-1].servers| ==> b[i-1].servers[j].s.ccache == InitCCache();
    assert forall j :: 0 <= j < |b[i-1].servers| ==> b[i-1].servers[j].s.pvc == EmptyVC();
    var init_ccache := InitCCache();
    // assert forall k :: k in init_ccache ==> AVersionIsMetOnAllServers(b, i, k, init_ccache[k].vc);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, map[]);
    // assume forall k :: k in init_ccache ==> init_ccache[k].deps == map[];
    // assert forall k :: k in init_ccache ==> AllVersionsInDepsAreMetOnAllServers(b, i, init_ccache[k].deps);
    // assume AllVersionsInCCacheAreMetOnAllServers(b, i, InitCCache());

    assert forall j :: 0 <= j < |b[i].servers| ==> 
        b[i-1].servers[j].s.ccache == b[i].servers[j].s.ccache;
    assert forall j :: 0 <= j < |b[i].servers| ==> 
            AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[j].s.ccache);
    
    assert forall j :: 0 <= j < |b[i].servers| ==> b[i].servers[j].s.ccache == InitCCache();
    assert forall j :: 0 <= j < |b[i].servers| ==> b[i].servers[j].s.pvc == b[i-1].servers[j].s.pvc;
    assert forall k :: k in InitCCache() ==> VCEq(InitCCache()[k].vc, EmptyVC());
    
    assert forall j :: 0 <= j < |b[i].servers| ==> (forall k :: k in b[i].servers[j].s.ccache ==> VCHappendsBefore(b[i].servers[j].s.ccache[k].vc, b[i].servers[j].s.pvc) || VCEq(b[i].servers[j].s.ccache[k].vc, b[i].servers[j].s.pvc));
    
}


lemma lemma_ServersAreMetForCMNext_WithStateChange(b:Behavior<CMState>, i:int, idx:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    requires CMNext(b[i], b[i+1])
    requires AllServersAreMet(b, i)
    requires forall j :: 0 < j <= i+1 ==> AllWriteDepsAreMet(b, j)
    requires forall j :: 0 < j <= i+1 ==> AllReadDepsAreMet(b, j)
    requires forall j :: 0 <= j < i+1 ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    // requires AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
    // requires AllVersionsInDepsAreMetOnAllServers(b, i-1, p.msg.deps_read)
    requires AllReadDepsAreMet(b, i)
    // requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    ensures AllServersAreMet(b, i+1)
{
    var s := b[i].servers[idx].s;
    var s' := b[i+1].servers[idx].s;

    var ios := lemma_ActionThatChangesServerIsThatServersAction(b, i, idx);
    assert CMNextServer(b[i], b[i+1], idx, ios);
    assert LServerNext(b[i].servers[idx], b[i+1].servers[idx], ios);
    assert ServerValid(s);
    assert |ios| > 0 && ios[0].LIoOpReceive? ==> ios[0].r.dst == idx;

    assert ios[0].LIoOpReceive?;
    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);
    assert p.msg.Message_Read? || p.msg.Message_Write? || p.msg.Message_Propagation?;
    assert p in b[i].environment.sentPackets;
    assert p.dst == idx;

    // lemma_BehaviorValidImpliesOneStepValid(b, i-1);

    assert ServerProcessPacket(s, s', ios);
    if p.msg.Message_Read? {
        assert ReceiveRead(s, s', p, sp);
        var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
        assert AllReadDepsAreMet(b, i);
        assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read? ==> 
            AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_read);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_read);

        // lemma_ServerReceiveReadOnlySentOnePacket(p);
        lemma_VersionsAfterPullDepsAreMetOnAllServers2(b, i, idx, p.msg.pvc_read, p.msg.deps_read);
        
        assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache);

        lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, new_ccache);

        assert s'.icache == new_icache;
        assert s'.ccache == new_ccache;
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
    } 
    else if p.msg.Message_Write?
    {
        assert ReceiveWrite(s, s', p, sp);
        // assert s'.icache == s.icache;
        assert s'.ccache == s.ccache;
        lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, s.ccache);
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
    }
    else
    {
        assert p.msg.Message_Propagation?;
        assert ReceivePropagate(s, s', p, sp);
        if s.next == p.msg.start && p.msg.round == 2 {
            var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.meta.deps);
            assert forall k :: k in p.msg.meta.deps ==> VCHappendsBefore(p.msg.meta.deps[k], p.msg.meta.vc) || VCEq(p.msg.meta.deps[k], p.msg.meta.vc);
            var new_pvc := if (VCHappendsBefore(p.msg.meta.vc, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.meta.vc);
            assert VCHappendsBefore(p.msg.meta.vc, new_pvc) || VCEq(p.msg.meta.vc, new_pvc);
            lemma_VCRelationIsTransitiveForDeps(p.msg.meta.deps, p.msg.meta.vc, new_pvc);
            assert forall k :: k in p.msg.meta.deps ==> VCHappendsBefore(p.msg.meta.deps[k], new_pvc) || VCEq(p.msg.meta.deps[k], new_pvc);

            assert i > 0;
            assert IsValidBehaviorPrefix(b, i+1);
            assert CMNext(b[i], b[i+1]);
            assert forall j :: 0 < j <= i+1 ==> AllWriteDepsAreMet(b, j);
            assert 0 <= idx < Nodes;
            assert |ios| > 0;
            assert ios[0].LIoOpReceive?;
            assert p.msg.Message_Propagation?;
            assert p in b[i].environment.sentPackets;
            // lemma_ReceivePktDstIsMe(p.dst, idx);
            assert p.dst == idx;
            reveal_ServerIdsAreMatch();
            // lemma_ServerIDsAreMatch(b[i]);
            assert idx == b[i].servers[idx].s.id;
            assert ios[0].r == p;
            assert PacketValid(p);
            assert p.msg.start == b[i].servers[idx].s.next;
            assert p.msg.round == 2;
            assert ReceivePropagate(b[i].servers[idx].s, b[i+1].servers[idx].s, p, ExtractSentPacketsFromIos(ios));

            assert forall k :: k in b[i+1].servers[idx].s.ccache ==> VCHappendsBefore(b[i+1].servers[idx].s.ccache[k].vc, b[i+1].servers[idx].s.pvc) || VCEq(b[i+1].servers[idx].s.ccache[k].vc, b[i+1].servers[idx].s.pvc);

            lemma_PropagationAtTail(b, i+1, idx, p, ios);
            // lemma_PropagationAtTail2(b, i+1, idx, p, ios);
            lemma_AVersionIsPropagatedImpliesAllPreviousDepsAreMet(b, i+1, new_pvc, p.msg.meta.deps);

            assert AVersionIsMetOnAllServers(b, i+1, p.msg.key, p.msg.meta.vc);
            // // lemma_MetaIsMetImpliesItsDepsAreMet(b, i+1, p.msg.meta);
            assert AllVersionsInDepsAreMetOnAllServers(b, i+1, p.msg.meta.deps);

            // lemma_PropagationToTheTailImpliesTheDepsAreMetOnAllServers(b, i, p.msg.meta.deps);
            lemma_AVersionIsPropagatedImpliesAllPreviousDepsAreMet(b, i, new_pvc, p.msg.meta.deps);
            assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.meta.deps);
            lemma_VersionsAfterPullDepsAreMetOnAllServers2(b, i, idx, new_pvc, p.msg.meta.deps);
        
            assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache);

            lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, new_ccache);
            // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i+1, p.msg.meta.deps);
            // lemma_BehaviorValidImpliesOneStepValid(b, i);
            // lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i+1, p.msg.key, p.msg.meta.vc);
            // assert AllVersionsInDepsAreMetOnAllServers(b, i+1, p.msg.meta.deps);
            // assert AVersionIsMetOnAllServers(b, i+1, p.msg.key, p.msg.meta.vc);
            assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, new_ccache);
            lemma_InsertIntoCCachePreserveAllVersionsInCCacheAreMetOnAllServers(b, i+1, new_ccache, p.msg.meta);
            assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
        } else {
            assert s'.ccache == s.ccache;
            lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, s.ccache);
            assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
        }
    }

    assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
    assert forall j :: 0 <= j < |b[i].servers| && j != idx ==> 
            b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache; //&& b[i].servers[j].s.icache == b[i+1].servers[j].s.icache;

    lemma_ServersAreMetForCMNext_helper(b, i, idx);
    assert AllServersAreMet(b, i+1);
}


lemma lemma_BehaviorPrefixAllServersAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 < j < i ==> AllServersAreMet(b, j)
    requires AllServersAreMet(b, i)
    ensures forall j :: 0 < j <= i ==> AllServersAreMet(b, j)
{

}

lemma lemma_ServersAreMetForCMNext(b:Behavior<CMState>, i:int)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires CMNext(b[i], b[i+1])
    requires AllServersAreMet(b, i)
    requires forall j :: 0 < j <= i+1 ==> AllWriteDepsAreMet(b, j)
    requires forall j :: 0 < j <= i+1 ==> AllReadDepsAreMet(b, j)
    requires forall j :: 0 <= j < i+1 ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires AllReadDepsAreMet(b, i)
    // requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    ensures AllServersAreMet(b, i+1)
{
    var ps := b[i];
    var ps' := b[i+1];

    if ps.servers == ps'.servers {
        forall j | 0 <= j < |b[i].servers|
            ensures AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[j].s.ccache)
        {
            assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[j].s.ccache);
            assert b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache;
            lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, b[i].servers[j].s.ccache);
            assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i].servers[j].s.ccache);
            assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[j].s.ccache);
        }
        assert AllServersAreMet(b, i+1);
    } 
    else {
        var idx :| 0 <= idx < |ps.servers| && ps.servers[idx] != ps'.servers[idx];
        lemma_ServersAreMetForCMNext_WithStateChange(b, i, idx);
    }
}

// lemma {:axiom} lemma_ServerReceiveReadOnlySentOnePacket(
//     p:Packet
// )
// requires PacketValid(p)
// requires p.msg.Message_Read?
// ensures AllReadDepsSmallerThanPVCRead(p.msg.pvc_read, p.msg.deps_read)



lemma lemma_ServersAreMetForCMNext_helper(
    b:Behavior<CMState>, i:int, idx:int
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i].servers[idx] != b[i+1].servers[idx]
    requires CMNext(b[i], b[i+1])
    requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    requires AllServersAreMet(b, i)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache)
    requires forall j :: 0 <= j < |b[i].servers| && j != idx ==> 
            b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache;
    ensures AllServersAreMet(b, i+1)
{
    assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[idx].s.ccache);
    assert forall j :: 0 <= j < |b[i].servers| && j != idx ==> 
            b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache;
    
    forall j | 0 <= j < |b[i].servers| && j != idx
        ensures AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[j].s.ccache);
    {
        assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[j].s.ccache);
        assert b[i].servers[j].s.ccache == b[i+1].servers[j].s.ccache;
        lemma_CCacheIsMetOnAllServersWillAlwaysMet(b, i+1, b[i].servers[j].s.ccache);
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i].servers[j].s.ccache);
        assert AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[j].s.ccache);
    }
    assert forall j :: 0 <= j < |b[i].servers| && j != idx ==>
            AllVersionsInCCacheAreMetOnAllServers(b, i+1, b[i+1].servers[j].s.ccache);
}

lemma lemma_InsertIntoCCachePreserveAllVersionsInCCacheAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache, meta:Meta
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 < i
    requires CCacheValid(ccache)
    requires MetaValid(meta)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
    requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
    ensures var new_ccache := InsertIntoCCache(ccache, meta);
            AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache)
{
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    if meta.key in ccache {
        var merged := MetaMerge(ccache[meta.key], meta);

        assert i > 0;
        assert IsValidBehaviorPrefix(b, i);
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        assert CMNext(b[i-1], b[i]);
        assert VectorClockValid(ccache[meta.key].vc);
        assert VectorClockValid(meta.vc);
        assert AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
        assert AVersionIsMetOnAllServers(b, i, meta.key, ccache[meta.key].vc);
        lemma_MergedVCIsMetOnAllServers(b, i, meta.key, ccache[meta.key].vc, meta.vc);
        assert AVersionIsMetOnAllServers(b, i, meta.key, merged.vc);
        assert AVersionIsMetOnAllServers(b, i, merged.key, merged.vc);

        assert DependencyValid(ccache[meta.key].deps);
        assert DependencyValid(meta.deps);
        // assert AllVersionsInDepsAreMetOnAllServers(b, i, ccache[meta.key].deps);
        // assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
        // lemma_MergedDepsIsMetOnAllServers(b, i, ccache[meta.key].deps, meta.deps);
        // assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);

        var new_ccache := InsertIntoCCache(ccache, meta);
        assert new_ccache == ccache[meta.key := merged];
        assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache);
    } else {
        var new_ccache := InsertIntoCCache(ccache, meta);
        assert new_ccache == ccache[meta.key := meta];
        assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_ccache);
    }

}

lemma lemma_CCacheIsMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CCacheValid(ccache)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, ccache)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
{
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInCCacheAreMetOnAllServers();

    forall k | k in ccache
        ensures AVersionIsMetOnAllServers(b, i, k, ccache[k].vc)
        // ensures AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps)
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, ccache[k].vc);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, ccache[k].vc);
        // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, ccache[k].deps);
    }
}

// lemma lemma_ICacheIsMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     icache:ICache
// )
//     requires 1 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires ICacheValid(icache)
//     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     requires AllDepsInICacheAreMetOnAllServers(b, i-1, icache)
//     ensures AllDepsInICacheAreMetOnAllServers(b, i, icache)
// {
//     assert i-1 > 0;
//     assert IsValidBehaviorPrefix(b, i-1);
//     lemma_BehaviorValidImpliesOneStepValid(b, i-1);
//     reveal_AllDepsInICacheAreMetOnAllServers();

//     forall k | k in icache
//     {
//         forall m:Meta | m in icache[k] 
//         {
//             forall kk | kk in m.deps 
//                 ensures AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
//             {
//                 assert AVersionIsMetOnAllServers(b, i-1, kk, m.deps[kk]);
//                 lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, kk, m.deps[kk]);
//                 assert AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
//             }
//         }
//     }

//     assert forall k :: k in icache ==>
//             forall m:Meta :: m in icache[k] ==> 
//                 forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
// }
}