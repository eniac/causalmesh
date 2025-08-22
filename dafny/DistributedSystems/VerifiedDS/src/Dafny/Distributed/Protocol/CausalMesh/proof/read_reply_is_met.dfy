include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "deps_are_met.dfy"
include "monotonic_read.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ReadReplyIsMet_i {
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
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_Monotonic_Read_i
import opened CausalMesh_Proof_Environment_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


lemma lemma_ReadRepliesIsMetOnAllServersTransfer(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    p_read:Packet
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadRepliesAreMet(b, i-1)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    // requires AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1)
    requires 0 <= idx < Nodes
    requires p in b[i].environment.sentPackets
    requires p !in b[i-1].environment.sentPackets
    requires p.msg.Message_Read_Reply?
    requires PacketValid(p)
    requires p_read in b[i-1].environment.sentPackets
    requires p_read.msg.Message_Read?
    requires CMNext(b[i-1], b[i])
    requires ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p])
    // requires AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_rreply)
    requires AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply)
    requires VCHappendsBefore(p.msg.vc_rreply, p.msg.pvc_rreply) || VCEq(p.msg.vc_rreply, p.msg.pvc_rreply)
    ensures AllReadRepliesAreMet(b, i)
{
    assert AllReadRepliesAreMet(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    assert CMNextCommon(b[i-1], b[i]);
    lemma_PacketsStaysInSentPackets(b, i-1, i);
    assert forall pp :: pp in b[i-1].environment.sentPackets && pp.msg.Message_Read_Reply? ==> 
        // AllVersionsInDepsAreMetOnAllServers(b, i-1, pp.msg.deps_rreply) && 
        AVersionIsMetOnAllServers(b, i-1, pp.msg.key_rreply, pp.msg.vc_rreply);
    assert forall pp :: pp in b[i-1].environment.sentPackets ==> pp in b[i].environment.sentPackets;

    
    // assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? && pp in b[i-1].environment.sentPackets ==> 
    //         AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_rreply) && AVersionIsMetOnAllServers(b, i, pp.msg.key_rreply, pp.msg.vc_rreply);
    forall pp | pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? && pp in b[i-1].environment.sentPackets
        ensures 
        // AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_rreply) && 
        AVersionIsMetOnAllServers(b, i, pp.msg.key_rreply, pp.msg.vc_rreply)
    {
        // assert AllVersionsInDepsAreMetOnAllServers(b, i-1, pp.msg.deps_rreply);
        assert AVersionIsMetOnAllServers(b, i-1, pp.msg.key_rreply, pp.msg.vc_rreply);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, pp.msg.key_rreply, pp.msg.vc_rreply);
        // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, pp.msg.deps_rreply);
    }
    assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? && pp in b[i-1].environment.sentPackets ==>
            // AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_rreply) && 
            AVersionIsMetOnAllServers(b, i, pp.msg.key_rreply, pp.msg.vc_rreply);

    lemma_ServerReceiveReadOnlySentOnePacket(b, i, idx, p, p_read);
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
    // assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_rreply);
    assert AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply);

    assert AllReadRepliesAreMet(b, i);
}

lemma lemma_ServerReadReplyIsMetOnAllServers2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    sp:seq<Packet>
)
    requires i > 1
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-2], b[i-1])
    requires CMNext(b[i-1], b[i])
    requires p.msg.Message_Read?
    requires PacketValid(p)
    requires 0 <= idx < Nodes
    requires ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p, sp)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i-1].servers[idx].s.ccache)
    requires AllVersionsInDepsAreMetOnAllServers(b, i-1, p.msg.deps_read)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires AllReadDepsSmallerThanPVCRead(p.msg.pvc_read, p.msg.deps_read)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
    // ensures AllVersionsInDepsAreMetOnAllServers(b, i, sp[0].msg.deps_rreply)
    ensures AVersionIsMetOnAllServers(b, i, sp[0].msg.key_rreply, sp[0].msg.vc_rreply)
    ensures VCHappendsBefore(sp[0].msg.vc_rreply, sp[0].msg.pvc_rreply) || VCEq(sp[0].msg.vc_rreply, sp[0].msg.pvc_rreply)
{
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;
    var deps := p.msg.deps_read;
    var p_reply := sp[0];
    assert p_reply.msg.Message_Read_Reply?;
    assert ServerValid(s);
    // assume forall k :: k in deps[k] ==> VCHappendsBefore(deps[k], p.msg.pvc_read) || VCEq(deps[k], p.msg.pvc_read);

    var new_pvc := if (VCHappendsBefore(p.msg.pvc_read, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.pvc_read);
    assert VCHappendsBefore(p.msg.pvc_read, new_pvc) || VCEq(p.msg.pvc_read, new_pvc);
    assume forall k :: k in deps ==> VCHappendsBefore(deps[k], new_pvc) || VCEq(deps[k], new_pvc);
    var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, deps);
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    assert CMNext(b[i-2], b[i-1]);
    assert AllVersionsInDepsAreMetOnAllServers(b, i-1, deps);
    assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i-1].servers[idx].s.ccache);
    lemma_VersionsAfterPullDepsAreMetOnAllServers2(b, i-1, idx, new_pvc, deps);
    assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, new_ccache);
    assert new_icache == s.icache;

    assert s'.icache == new_icache;
    assert s'.ccache == new_ccache;

    assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, s'.ccache);

    assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache);

    reveal_AllVersionsInCCacheAreMetOnAllServers();
    assert AVersionIsMetOnAllServers(b, i-1, p_reply.msg.key_rreply, p_reply.msg.vc_rreply);
    // assert AllVersionsInDepsAreMetOnAllServers(b, i-1, p_reply.msg.deps_rreply);

    lemma_VersionMetIsTransitive(b, i, idx, p_reply.msg.key_rreply, p_reply.msg.vc_rreply, p_reply.msg.deps_rreply);

    assert AVersionIsMetOnAllServers(b, i, p_reply.msg.key_rreply, p_reply.msg.vc_rreply);
    // assert AllVersionsInDepsAreMetOnAllServers(b, i, p_reply.msg.deps_rreply);
    assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache);
}

lemma lemma_ReadRepliesIsMetOnAllServersPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires forall j :: 0 < j <= i ==> AllServersAreMet(b, j)
    requires forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j)
    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    ensures forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j)
{
    if i == 0 {
        return;
    }
    
    if i == 1 {
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        lemma_ReadRepliesIsMetOnAllServersForIndexOne(b, i);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    if !StepSendsReadReply(b[i-1], b[i]){
        lemma_ReadRepliesIsMetOnAllServersPrefix(b, i-1);
        assume forall j :: 0 < j <= i-1 ==> AllReadRepliesAreMet(b, j);
        assert AllReadRepliesAreMet(b, i-1);
        lemma_PacketsStaysInSentPackets(b, i-1, i);
        assert forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets;
        assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets;
        assert 1 < i;
        assert IsValidBehaviorPrefix(b, i);
        assert AllReadRepliesAreMet(b, i-1);
        assert forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1]);
        assert CMNext(b[i-1], b[i]);
        lemma_ReadRepliesIsMetOnAllServersConstant(b, i);
        assert AllReadRepliesAreMet(b, i);
        assert forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j);
        return;
    }

    lemma_ReadRepliesIsMetOnAllServersPrefix(b, i-1);
    assume forall j :: 0 < j <= i-1 ==> AllReadRepliesAreMet(b, j);
    assert AllReadRepliesAreMet(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply?;
    assert PacketValid(p);
    var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p);
    var p_read := ios[0].r;

    assert p_read in b[i-1].environment.sentPackets;
    assert ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
    assert AllServersAreMet(b, i-1);
    assert AllReadDepsAreMet(b, i-1);
    assert AllVersionsInDepsAreMetOnAllServers(b, i-1, p_read.msg.deps_read);
    lemma_ServerReadReplyIsMetOnAllServers2(b, i, idx, p_read, [p]);

    assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache);
    // assert AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache);
    // assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_rreply);
    assert AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply);

    lemma_ReadRepliesIsMetOnAllServersTransfer(b, i, idx, p, p_read);
    assert AllReadRepliesAreMet(b, i);
    assert forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j);
}


// lemma lemma_ReadRepliesIsMetOnAllServersPrefix(
//     b:Behavior<CMState>,
//     i:int
// )
//     requires 0 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires forall j :: 0 < j <= i ==> AllServersAreMet(b, j)
//     requires forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     ensures AllReadRepliesAreMet(b, i)
// {
//     if i <= 1 {
//         lemma_ReadRepliesIsMetOnAllServersForIndexOne(b, i);
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if !StepSendsReadReply(b[i-1], b[i]){
//         lemma_ReadRepliesIsMetOnAllServersPrefix(b, i-1);
//         assert AllReadRepliesAreMet(b, i-1);
//         lemma_PacketsStaysInSentPackets(b, i-1, i);
//         assert forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets;
//         assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets;
//         assert 1 < i;
//         assert IsValidBehaviorPrefix(b, i);
//         assert AllReadRepliesAreMet(b, i-1);
//         assert forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1]);
//         assert CMNext(b[i-1], b[i]);
//         lemma_ReadRepliesIsMetOnAllServersConstant(b, i);
//         assert AllReadRepliesAreMet(b, i);
//         return;
//     }

//     lemma_ReadRepliesIsMetOnAllServersPrefix(b, i-1);
//     assert AllReadRepliesAreMet(b, i-1);

//     var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply?;
//     assert PacketValid(p);
//     var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p);
//     var p_read := ios[0].r;

//     assert p_read in b[i-1].environment.sentPackets;
//     assert ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
//     assert AllServersAreMet(b, i-1);
//     assert AllReadDepsAreMet(b, i-1);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i-1, p_read.msg.deps_read);
//     lemma_ServerReadReplyIsMetOnAllServers(b, i, idx, p_read, [p]);

//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache);
//     // assert AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_rreply);
//     assert AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply);

//     lemma_ReadRepliesIsMetOnAllServersTransfer(b, i, idx, p, p_read);
//     assert AllReadRepliesAreMet(b, i);
// }

lemma lemma_ReadRepliesIsMetOnAllServersForIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply?
    ensures AllReadRepliesAreMet(b, i)
{
    // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
    assert CMNext(b[i-1], b[i]);
}

lemma lemma_ReadRepliesIsMetOnAllServersConstant(
    b:Behavior<CMState>,
    i:int
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadRepliesAreMet(b, i-1)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets
    requires forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets
    ensures AllReadRepliesAreMet(b, i)
{
    assert AllReadRepliesAreMet(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    assert forall pp :: pp in b[i-1].environment.sentPackets && pp.msg.Message_Read_Reply? ==> 
        // AllVersionsInDepsAreMetOnAllServers(b, i-1, pp.msg.deps_rreply) && 
        AVersionIsMetOnAllServers(b, i-1, pp.msg.key_rreply, pp.msg.vc_rreply);
    assert forall pp :: pp in b[i-1].environment.sentPackets ==> pp in b[i].environment.sentPackets;

    assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? ==> pp in b[i-1].environment.sentPackets;
    forall pp | pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply?
        ensures 
        // AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_rreply) && 
        AVersionIsMetOnAllServers(b, i, pp.msg.key_rreply, pp.msg.vc_rreply)
    {
        // assert AllVersionsInDepsAreMetOnAllServers(b, i-1, pp.msg.deps_rreply);
        assert AVersionIsMetOnAllServers(b, i-1, pp.msg.key_rreply, pp.msg.vc_rreply);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, pp.msg.key_rreply, pp.msg.vc_rreply);
        // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, pp.msg.deps_rreply);
    }
    assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? ==>
            // AllVersionsInDepsAreMetOnAllServers(b, i, pp.msg.deps_rreply) && 
            AVersionIsMetOnAllServers(b, i, pp.msg.key_rreply, pp.msg.vc_rreply);
    assert AllReadRepliesAreMet(b, i);
}




// lemma lemma_ServerReadReplyIsMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     p:Packet,
//     sp:seq<Packet>
// )
//     requires i > 1
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-2], b[i-1])
//     requires CMNext(b[i-1], b[i])
//     requires p.msg.Message_Read?
//     requires PacketValid(p)
//     requires 0 <= idx < Nodes
//     requires ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p, sp)
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i-1].servers[idx].s.ccache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i-1, p.msg.deps_read)
//     // requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, sp[0].msg.deps_rreply)
//     ensures AVersionIsMetOnAllServers(b, i, sp[0].msg.key_rreply, sp[0].msg.vc_rreply)
// {
//     var s := b[i-1].servers[idx].s;
//     var s' := b[i].servers[idx].s;
//     var deps := p.msg.deps_read;
//     var p_reply := sp[0];
//     assert p_reply.msg.Message_Read_Reply?;
//     assert ServerValid(s);

//     var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, deps);
//     assert i-1 > 0;
//     assert IsValidBehaviorPrefix(b, i-1);
//     assert CMNext(b[i-2], b[i-1]);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i-1, deps);
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i-1].servers[idx].s.ccache);
//     lemma_VersionsAfterPullDepsAreMetOnAllServers(b, i-1, idx, deps);
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, new_ccache);
//     assert new_icache == s.icache;

//     assert s'.icache == new_icache;
//     assert s'.ccache == new_ccache;

//     assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, s'.ccache);

//     assert AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache);

//     reveal_AllVersionsInCCacheAreMetOnAllServers();
//     assert AVersionIsMetOnAllServers(b, i-1, p_reply.msg.key_rreply, p_reply.msg.vc_rreply);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i-1, p_reply.msg.deps_rreply);

//     lemma_VersionMetIsTransitive(b, i, idx, p_reply.msg.key_rreply, p_reply.msg.vc_rreply, p_reply.msg.deps_rreply);

//     assert AVersionIsMetOnAllServers(b, i, p_reply.msg.key_rreply, p_reply.msg.vc_rreply);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p_reply.msg.deps_rreply);
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache);
// }


lemma lemma_VersionMetIsTransitive(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    key:Key, 
    vc:VectorClock,
    deps:Dependency
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CMNext(b[i-2], b[i-1])
    requires 0 <= idx < Nodes
    requires key in Keys_domain
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
    requires AVersionIsMetOnAllServers(b, i-1, key, vc)
    // requires AllVersionsInDepsAreMetOnAllServers(b, i-1, deps)
    // requires AllDepsInICacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.icache)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache)

    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])

    ensures AVersionIsMetOnAllServers(b, i, key, vc)
    // ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    // ensures AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
{ 
    // assume ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
    lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, key, vc);
    // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, deps);
    // lemma_AllDepsInICacheAreMetOnAllServersWillAlwaysMet(b, i, idx);
    lemma_AllVersionsInCCacheAreMetOnAllServersWillAlwaysMet(b, i, idx);
}



// predicate MetaDoesNotDecrease(
//     m1:Meta,
//     m2:Meta
// )
//     requires m1.key == m2.key
// {

// }


// lemma {:axiom} lemma_AVersionIsMetWillAlwaysMet(
//     i1:ICache,
//     i2:ICache,
//     c1:CCache,
//     c2:CCache,
//     k:Key,
//     vc:VectorClock
// )
//     requires ICacheValid(i1)
//     requires ICacheValid(i2)
//     requires CCacheValid(c1)
//     requires CCacheValid(c2)
//     requires ICacheDoesNotDecrease(i1, i2)
//     requires CCacheDoesNotDecrease(c1, c2)
//     requires forall k :: k in Keys_domain ==> k in i1 && k in i2 && k in c1 && k in c2
//     requires k in Keys_domain
//     requires VectorClockValid(vc)
//     requires AVersionOfAKeyIsMet(i1, c1, k, vc)
//     ensures AVersionOfAKeyIsMet(i2, c2, k, vc)
// // {
// //     var m1 := FoldMetaSet2(c1[k], i1[k]);
// //     var m2 := FoldMetaSet2(c2[k], i2[k]);
// //     assume VCEq(m1.vc, m2.vc) || VCHappendsBefore(m1.vc, m2.vc);
// // }

// lemma lemma_AVersionIsMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     k:Key,
//     vc:VectorClock
// )
//     requires 1 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires CMNext(b[i-2], b[i-1])
//     requires k in Keys_domain
//     requires VectorClockValid(vc)
//     requires AVersionIsMetOnAllServers(b, i-1, k, vc)
//     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     ensures AVersionIsMetOnAllServers(b, i, k, vc)
// {
//     assert forall j :: 0 <= j < |b[i-1].servers| ==> 
//         CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
//         && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
//     forall j | 0 <= j < |b[i].servers| 
//         ensures AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc)
//     {
//         assert AVersionOfAKeyIsMet(b[i-1].servers[j].s.icache, b[i-1].servers[j].s.ccache, k, vc);
//         assert CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache);
//         assert ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
//         assert ServerValid(b[i-1].servers[j].s);
//         assert ServerValid(b[i].servers[j].s);
//         lemma_AVersionIsMetWillAlwaysMet(
//             b[i-1].servers[j].s.icache,
//             b[i].servers[j].s.icache,
//             b[i-1].servers[j].s.ccache,
//             b[i].servers[j].s.ccache,
//             k,
//             vc
//         );
//         assert AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc);
//     }
// }

// lemma lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     deps:Dependency
// )
//     requires 1 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     // requires CMNext(b[i-2], b[i-1])
//     requires DependencyValid(deps)
//     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     requires AllVersionsInDepsAreMetOnAllServers(b, i-1, deps)
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
// {
//     lemma_BehaviorValidImpliesOneStepValid(b, i-1);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     assert forall j :: 0 <= j < |b[i-1].servers| ==> 
//         CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
//         && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
//     forall k | k in deps 
//         ensures AVersionIsMetOnAllServers(b, i, k, deps[k])
//     {
//         assert AVersionIsMetOnAllServers(b, i-1, k, deps[k]);
//         lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, deps[k]);
//         assert AVersionIsMetOnAllServers(b, i, k, deps[k]);
//     }
// }

// // lemma {:axiom} lemma_AllDepsInICacheAreMetOnAllServersWillAlwaysMet(
// //     b:Behavior<CMState>,
// //     i:int,
// //     idx:int
// // )
// //     requires 1 < i
// //     requires IsValidBehaviorPrefix(b, i)
// //     requires CMNext(b[i-1], b[i])
// //     // requires CMNext(b[i-2], b[i-1])
// //     requires 0 <= idx < Nodes
// //     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
// //     requires AllDepsInICacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.icache)
// //     ensures AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[idx].s.icache)
// // {
// //     assert forall j :: 0 <= j < |b[i-1].servers| ==> 
// //         CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
// //         && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
// //     var icache := b[i].servers[idx].s.icache;
// //     assert ICacheValid(icache);
// //     assert AllDepsInICacheAreMetOnAllServers(b, i-1, icache);

// //     forall k | k in icache
// //     {
// //         forall m:Meta | m in icache[k] 
// //         {
// //             forall kk | kk in m.deps 
// //                 ensures AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
// //             {
// //                 assert AVersionIsMetOnAllServers(b, i-1, kk, m.deps[kk]);
// //                 lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, kk, m.deps[kk]);
// //                 assert AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
// //             }
// //         }
// //     }

// //     assert forall k :: k in icache ==>
// //             forall m:Meta :: m in icache[k] ==> 
// //                 forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk]);
// // }

// lemma lemma_AllVersionsInCCacheAreMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int
// )
//     requires 1 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     // requires CMNext(b[i-2], b[i-1])
//     requires 0 <= idx < Nodes
//     requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache)
//     ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
// {
//     assert i-1 > 0;
//     assert IsValidBehaviorPrefix(b, i-1);
//     lemma_BehaviorValidImpliesOneStepValid(b, i-1);
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
//     assert forall j :: 0 <= j < |b[i-1].servers| ==> 
//         CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
//         && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);

//     var ccache := b[i].servers[idx].s.ccache;

//     forall k | k in ccache
//         ensures AVersionIsMetOnAllServers(b, i, k, ccache[k].vc)
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps)
//     {
//         assert AVersionIsMetOnAllServers(b, i-1, k, ccache[k].vc);
//         lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, ccache[k].vc);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, ccache[k].deps);
//     }
// }


}