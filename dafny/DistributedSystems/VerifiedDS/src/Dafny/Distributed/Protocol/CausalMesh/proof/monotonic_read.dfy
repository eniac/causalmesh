include "../distributed_system.dfy"
include "causalcut.dfy"
include "packet_sending.dfy"
include "message_read_reply.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Monotonic_Read_i {
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
import opened CausalMesh_Proof_CausalCut_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_MonotonicRead(
    low_level_behavior:seq<CMState>
)
    requires |low_level_behavior| > 0 
    requires CMInit(low_level_behavior[0])
    requires forall i {:trigger CMNext(low_level_behavior[i], low_level_behavior[i+1])} ::
                0 <= i < |low_level_behavior| - 1 ==> CMNext(low_level_behavior[i], low_level_behavior[i+1])
    ensures var b := ConvertBehaviorSeqToImap(low_level_behavior);
        forall i :: 0 <= i < |low_level_behavior| ==> MonotonicRead(b, i)
{
    var b := ConvertBehaviorSeqToImap(low_level_behavior);
    if |low_level_behavior| == 1 { 
        assert !exists p :: p in b[0].environment.sentPackets;
        assert MonotonicRead(b, 0);
    }
    else
    { 
        lemma_BehaviorValidImpliesAllStepsValid(b, |low_level_behavior| - 1);
        assert forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < |low_level_behavior| - 1 ==> CMNext(b[j], b[j+1]); 
        assert forall j :: 0 <= j < |low_level_behavior| - 1 ==> CMNext(b[j], b[j+1]);
        // lemma_ReadReplyHasHigherVCThanDepsPrefix(b, |low_level_behavior| - 1);
        lemma_MonotonicReadPrefix(b, |low_level_behavior| - 1);
        // assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, |low_level_behavior| - 1);
        assert forall i :: 0 < i < |low_level_behavior| ==> AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i);
    }
    // assert forall i :: 0 <= i < |low_level_behavior| ==> MonotonicRead(b, i);
}

predicate MonotonicRead(
    b:Behavior<CMState>,
    i:int
)
    requires IsValidBehaviorPrefix(b, i)
    requires i >= 0
{
    if i == 0 then 
        !exists p :: p in b[i].environment.sentPackets
    else 
        AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
}

lemma lemma_MonotonicReadPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires i >= 0
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, j)
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_MonotonicReadPrefix(b, i-1);

    lemma_ReadReplyHasHigherVCThanDepsPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, j);
}

predicate ReadReplyVCIsLargerThanVCInDeps(deps:Dependency, vc:VectorClock, k:Key)
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
{
    if k in deps then 
        VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
    else
        true
}

predicate ReadReplyHasCorrspondingReadWithSmallerVC(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i) 
    // requires CMNext(b[i-1], b[i])
    requires p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    exists rp :: rp in b[i].environment.sentPackets && rp.msg.Message_Read? 
                        && p.msg.key_rreply == rp.msg.key_read
                        && p.dst == rp.src
                        && ReadReplyVCIsLargerThanVCInDeps(rp.msg.deps_read, p.msg.vc_rreply, p.msg.key_rreply)
                        // is the read reply deps contains all deps in read?
} 

predicate AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i) 
    // requires forall j :: 0 <= j <= i ==> AllServersAreCausalCut(b[i])
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall p :: p in b[i].environment.sentPackets ==> PacketValid(p);
    
    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p)
}


lemma lemma_ReadReplyHasHigherVCThanDepsPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // requires 
    // ensures forall j :: 0 <= j <= i ==> ReadReplyHasCorrspondingReadWithSmallerVC(b, j)
    ensures AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
    decreases i
{
    if i <= 1 {
        assert CMNext(b[i-1], b[i]);
        lemma_ReadReplyHasCorrspondingReadWithSmallerVCForIndexOne(b, i);
        // assume AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i);
        return;
    }

    assert 0 < i - 1;

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    // if b[i-1].environment.sentPackets == b[i].environment.sentPackets

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    if !StepSendsReadReply(b[i-1], b[i]){
        lemma_ReadReplyHasHigherVCThanDepsPrefix(b, i-1);
        assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);
        assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets;
        assert CMNext(b[i-1], b[i]);
        assert forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets;
        lemma_ReadReplyHasCorrspondingReadWithSmallerVCConstant(b, i);
        assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i);
        // assert forall j :: 0 <= j <= i ==> ReadReplyHasCorrspondingReadWithSmallerVC(b, j);
        return;
    }

    lemma_ReadReplyHasHigherVCThanDepsPrefix(b, i-1);

    

    // assume forall j :: 0 < j < i ==> AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, j);
    assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);
    
    // assert IsValidBehaviorPrefix(b, i-1);
    // assert i - 1 > 0;
    // assert 1 < i;
    // assert IsValidBehaviorPrefix(b, i);
    // lemma_ForallRangeImpliesOne(b, i);
    // lemma_test(b, i);
    // assume AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);
    // assert forall p :: p in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply? ==> 
    //         ReadReplyHasCorrspondingReadWithSmallerVC(b, i-1, p);

    // assert |b[i].environment.sentPackets| == |b[i-1].environment.sentPackets| + 1;

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply?;

    assert PacketValid(p);
    var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p);

    // assume AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);

    // var p_read := lemma_ReadReplyHasCorrspondingReadMessage(b, i, p);
    var p_read := ios[0].r;
    assert p_read in b[i-1].environment.sentPackets;

    // assert p_read.msg.key_read == p.msg.key_rreply;
    // assert p_read.dst == p.src;

    // assume AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);

    assert ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
    lemma_ServerReadReplyLargerVC(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
    assert ReadReplyVCIsLargerThanVCInDeps(p_read.msg.deps_read, p.msg.vc_rreply, p_read.msg.key_read);
    assert ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p);

    // assert 1 < i;
    // assert IsValidBehaviorPrefix(b,i);
    // assert 0 <= idx < Nodes;
    // assert p in b[i].environment.sentPackets;
    // assert p !in b[i-1].environment.sentPackets;
    // assert p.msg.Message_Read_Reply?;
    // assert PacketValid(p);
    // assert p_read in b[i-1].environment.sentPackets;
    // assert p_read.msg.Message_Read?;
    // assert CMNext(b[i-1], b[i]);
    // assert ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
    // assert ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p);
    // lemma_BehaviorValidImpliesOneStepValid(b, i);
    // assume AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);

    lemma_ReadReplyHasCorrspondingReadWithSmallerVCTransfer(b, i, idx, p, p_read);

    assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i);
    // assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && p in b[i-1].environment.sentPackets ==> 
    //         ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p);

    // assert forall j :: 0 < j <= i ==> ReadReplyHasCorrspondingReadWithSmallerVC(b, j);
}

predicate StepSendsReadReply(s:CMState, s':CMState)
    requires CMNext(s, s')
{
    // && s.environment.nextStep.LEnvStepHostIos?
    && exists p :: p in s'.environment.sentPackets && p.msg.Message_Read_Reply? && p !in s.environment.sentPackets
}

// lemma lemma_ReadReplyHasCorrspondingReadWithSmallerVCForIndexZero(
//     b:Behavior<CMState>,
//     i:int
// )
//     requires i == 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires CMNext(b[i-1], b[i])
//     // ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply?
//     ensures AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
// {
//     assert CMInit(b[i]);
// }

lemma lemma_ReadReplyHasCorrspondingReadWithSmallerVCForIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply?
    ensures AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
{
    // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
    assert CMNext(b[i-1], b[i]);
}

lemma lemma_ReadReplyHasCorrspondingReadWithSmallerVCConstant(
    b:Behavior<CMState>,
    i:int
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1)
    requires CMNext(b[i-1], b[i])
    requires forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets
    requires forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets
    ensures AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
{
    // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
}

lemma lemma_ReadReplyHasCorrspondingReadWithSmallerVCTransfer(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    p_read:Packet
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1)
    requires 0 <= idx < Nodes
    requires p in b[i].environment.sentPackets
    requires p !in b[i-1].environment.sentPackets
    requires p.msg.Message_Read_Reply?
    requires PacketValid(p)
    requires p_read in b[i-1].environment.sentPackets
    requires p_read.msg.Message_Read?
    requires CMNext(b[i-1], b[i])
    requires ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p])
    requires ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p)
    ensures AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i)
{
    // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
    assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall pp :: pp in b[i-1].environment.sentPackets && pp.msg.Message_Read_Reply? ==> 
        ReadReplyHasCorrspondingReadWithSmallerVC(b, i-1, pp);
    assert forall pp :: pp in b[i-1].environment.sentPackets ==> pp in b[i].environment.sentPackets;

    assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Read_Reply? && pp in b[i-1].environment.sentPackets ==> 
            ReadReplyHasCorrspondingReadWithSmallerVC(b, i, pp);
    assert ReadReplyHasCorrspondingReadWithSmallerVC(b, i, p);
    lemma_ServerReceiveReadOnlySentOnePacket(b, i, idx, p, p_read);
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
    assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, i);
}

lemma lemma_ServerReceiveReadOnlySentOnePacket(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    p_read:Packet
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
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
    ensures b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p}
{
    var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p);
    assert ios[0].LIoOpReceive?;
    // assert p_read == ios[0].r;
    assert ios[1].LIoOpSend?;
    var pkts := ExtractSentPacketsFromIos(ios);
    assert p in pkts;
    assert |pkts| == 1;
    assert pkts == [p];
    assert LEnvironment_Next(b[i-1].environment, b[i].environment);
    assert b[i-1].environment.nextStep.LEnvStepHostIos?;
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
    var pkts2 := set io | io in ios && io.LIoOpSend? :: io.s;
    assert pkts2 == {p};
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
}

lemma lemma_ServerReadReplyLargerVC(s:Server, s':Server, p:Packet, sp:seq<Packet>)
    requires p.msg.Message_Read?
    requires ServerValid(s)
    requires PacketValid(p) 
    requires ReceiveRead(s, s', p, sp)
    ensures |sp| == 1
    ensures sp[0].msg.Message_Read_Reply?
    ensures p.msg.key_read in p.msg.deps_read ==> 
                VCHappendsBefore(p.msg.deps_read[p.msg.key_read], sp[0].msg.vc_rreply) || VCEq(p.msg.deps_read[p.msg.key_read], sp[0].msg.vc_rreply)
    // ensures forall k :: k in p.msg.deps_read ==> 
    //             VCHappendsBefore(p.msg.deps_read[k], sp[0].msg.vc_rreply) || VCEq(p.msg.deps_read[k], sp[0].msg.vc_rreply)
{
    var deps := p.msg.deps_read;
    var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
    assert CausalCut(new_ccache);
    assert UponReadsDepsAreMet(new_ccache, deps);
    var reply_vc := new_ccache[p.msg.key_read].vc;
    assert forall k :: k in deps ==> 
            VCEq(deps[k], new_ccache[k].vc) || VCHappendsBefore(deps[k], new_ccache[k].vc);
    assert VectorClockValid(reply_vc);
    if p.msg.key_read in deps {
        assert VCHappendsBefore(deps[p.msg.key_read], reply_vc) || VCEq(deps[p.msg.key_read], reply_vc);
    }
}
}