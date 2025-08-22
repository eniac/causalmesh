include "../distributed_system.dfy"
include "causalcut.dfy"
include "packet_sending.dfy"
include "message_read_reply.dfy"
include "monotonic_read.dfy"
include "monotonic_write.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Read_After_Write_i {
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
import opened CausalMesh_Proof_Monotonic_Read_i
import opened CausalMesh_Proof_Monotonic_Write_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


lemma lemma_ReadAWriteCanObserveAllItsPreviousReadsAndWrites(
    behavior:seq<CMState>
)
    requires |behavior| > 0 
    requires CMInit(behavior[0])
    requires forall i {:trigger CMNext(behavior[i], behavior[i+1])} :: 
                0 <= i < |behavior| - 1 ==> CMNext(behavior[i], behavior[i+1])
    ensures var b := ConvertBehaviorSeqToImap(behavior);
        forall i :: 0 <= i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i) 
{
    var b := ConvertBehaviorSeqToImap(behavior);
    if |behavior| == 1 { 
        assert !exists p :: p in b[0].environment.sentPackets;
        assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, 0);
        lemma_AllReadReplyVCIsLargerThanAllPreviousWrites(b, 0);
        assert AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, 0);
    }
    else
    { 
        lemma_BehaviorValidImpliesAllStepsValid(b, |behavior| - 1);
        assert forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < |behavior| - 1 ==> CMNext(b[j], b[j+1]); 
        assert forall j :: 0 <= j < |behavior| - 1 ==> CMNext(b[j], b[j+1]);
        // lemma_ReadReplyHasHigherVCThanDepsPrefix(b, |low_level_behavior| - 1);
        lemma_ReadAfterWritePrefix(b, |behavior| - 1);
        // assert AllReadReplyHasCorrspondingReadWithSmallOrEqVCForSameKeyInDeps(b, |low_level_behavior| - 1);
        assert forall i :: 0 < i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
        // lemma_AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
        // assert forall i :: 0 < i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i);
    }

    assert forall i :: 0 <= i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
    lemma_AllReadReplyVCIsLargerThanAllPreviousWritesPrefix(b, |behavior|-1);
    assert forall i :: 0 <= i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i);
}

lemma lemma_AllReadReplyVCIsLargerThanAllPreviousWritesPrefix(
    b:Behavior<CMState>,
    k:int
)
    requires k >= 0 
    requires IsValidBehaviorPrefix(b, k)
    // requires forall i :: 
    //             0 <= i <= k ==> CMNext(b[i], b[i+1])
    requires forall i :: 0 <= i <= k ==> AllReadReplyVCIsLargerThanAllPreviousWrites(b, i) 
    ensures  forall i :: 0 <= i <= k ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i) 
{
    if k == 0 {
        lemma_AllReadReplyVCIsLargerThanAllPreviousWrites(b, 0);
        assert AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, 0);
        return;
    }
    lemma_AllReadReplyVCIsLargerThanAllPreviousWritesPrefix(b, k-1);
    assert forall i :: 0 <= i <= k-1 ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i);
    
    assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, k);
    lemma_AllReadReplyVCIsLargerThanAllPreviousWrites(b, k);
    assert AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, k);
    assert forall i :: 0 <= i <= k ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i);

}

predicate ReadReplyVCIsLargerThanAllPreviousWrites(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall wrp :: wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
            && p.msg.key_rreply == wrp.msg.key_wreply
            && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply))
                ==> WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, wrp)
}

predicate ReadReplyVCIsLargerThanAllPreviousWritesReal(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall wrp :: wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
            && p.msg.key_rreply == wrp.msg.key_wreply
            && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply))
                ==> exists wp :: wp in b[i].environment.sentPackets && wp.msg.Message_Write?
                    && wrp.msg.opn_wreply == wp.msg.opn_write
                    && wrp.msg.key_wreply == wp.msg.key_write
                    && wrp.dst == wp.src
                    // && WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, wrp.msg.vc_wreply)
                    // && WriteReplyIsLargerThanVCInLocal(wp.msg.local, wrp.msg.vc_wreply)
                    && WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, p.msg.vc_rreply)
                    && WriteReplyIsLargerThanVCInLocal(wp.msg.local, p.msg.vc_rreply)
}

lemma lemma_VCRelationIsTransitive(
    rrp:Packet,
    wrp:Packet,
    wp:Packet
)
    requires PacketValid(rrp)
    requires rrp.msg.Message_Read_Reply?
    requires PacketValid(wrp)
    requires wrp.msg.Message_Write_Reply?
    requires PacketValid(wp)
    requires wp.msg.Message_Write?
    requires (VCHappendsBefore(wrp.msg.vc_wreply, rrp.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, rrp.msg.vc_rreply))
    requires WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, wrp.msg.vc_wreply)
    requires WriteReplyIsLargerThanVCInLocal(wp.msg.local, wrp.msg.vc_wreply)
    ensures WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, rrp.msg.vc_rreply)
    ensures WriteReplyIsLargerThanVCInLocal(wp.msg.local, rrp.msg.vc_rreply)
{

}

lemma lemma_ReadReplyVCIsLargerThanAllPreviousWrites(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? && PacketValid(p)
    requires ReadReplyVCIsLargerThanAllPreviousWrites(b, i, p)
    ensures ReadReplyVCIsLargerThanAllPreviousWritesReal(b, i, p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall wrp :: wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
            && p.msg.key_rreply == wrp.msg.key_wreply
            && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply))
                ==> exists wp :: wp in b[i].environment.sentPackets && wp.msg.Message_Write?
                    && wrp.msg.opn_wreply == wp.msg.opn_write
                    && wrp.msg.key_wreply == wp.msg.key_write
                    && wrp.dst == wp.src
                    && WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, wrp.msg.vc_wreply)
                    && WriteReplyIsLargerThanVCInLocal(wp.msg.local, wrp.msg.vc_wreply);
    if exists wrp :: wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
            && p.msg.key_rreply == wrp.msg.key_wreply
            && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply)) {

        var wrp :| wrp in b[i].environment.sentPackets && wrp.msg.Message_Write_Reply?
                && p.msg.key_rreply == wrp.msg.key_wreply
                && (VCHappendsBefore(wrp.msg.vc_wreply, p.msg.vc_rreply) || VCEq(wrp.msg.vc_wreply, p.msg.vc_rreply));
        var wp :| wp in b[i].environment.sentPackets && wp.msg.Message_Write?
                    && wrp.msg.opn_wreply == wp.msg.opn_write
                    && wrp.msg.key_wreply == wp.msg.key_write
                    && wrp.dst == wp.src
                    && WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, wrp.msg.vc_wreply)
                    && WriteReplyIsLargerThanVCInLocal(wp.msg.local, wrp.msg.vc_wreply);
        lemma_VCRelationIsTransitive(p, wrp, wp);
        assert ReadReplyVCIsLargerThanAllPreviousWritesReal(b, i, p);
    }
}

predicate AllReadReplyVCIsLargerThanAllPreviousWrites(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
{
    if i == 0 then 
        !exists p :: p in b[i].environment.sentPackets
    else
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> 
            ReadReplyVCIsLargerThanAllPreviousWrites(b, i, p)
}

predicate AllReadReplyVCIsLargerThanAllPreviousWritesReal(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
{
    if i == 0 then 
        !exists p :: p in b[i].environment.sentPackets
    else
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> 
            ReadReplyVCIsLargerThanAllPreviousWritesReal(b, i, p)
}

lemma lemma_AllReadReplyVCIsLargerThanAllPreviousWrites(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadReplyVCIsLargerThanAllPreviousWrites(b, i)
    ensures AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i)
{
    if i > 0 {
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        if exists p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? {
            var p :| p in b[i].environment.sentPackets && p.msg.Message_Read_Reply?;
            lemma_ReadReplyVCIsLargerThanAllPreviousWrites(b, i, p);
        }
    }
}

lemma lemma_ReadAfterWritePrefix(
    b:Behavior<CMState>,
    i:int
)
    requires i >= 0
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllReadReplyVCIsLargerThanAllPreviousWrites(b, j)
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_ReadAfterWritePrefix(b, i-1);
    lemma_MonotonicWritePrefix(b, i);

    lemma_ReadReplyVCIsLargerThanAllPreviousWritesPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllReadReplyVCIsLargerThanAllPreviousWrites(b, j);
}


lemma lemma_ReadReplyVCIsLargerThanAllPreviousWritesPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocalsAlways(b, i)
    ensures AllReadReplyVCIsLargerThanAllPreviousWrites(b, i)
{
    if i <= 1 {
        assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    if !StepSendsReadReply(b[i-1], b[i]){
        lemma_ReadReplyVCIsLargerThanAllPreviousWritesPrefix(b, i-1); 
        // assume AllReadReplyVCIsLargerThanAllPreviousWrites(b, i-1);
        assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets; 
        assert CMNext(b[i-1], b[i]);
        assert forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets;
        lemma_ReadReplyVCIsLargerThanAllPreviousWritesConstant(b, i);
        assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
        return;
    }

    lemma_ReadReplyVCIsLargerThanAllPreviousWritesPrefix(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply?;

    assert PacketValid(p);
    var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p);

    var p_read := ios[0].r;
    assert ReceiveRead(b[i-1].servers[idx].s, b[i].servers[idx].s, p_read, [p]);
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);

    assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
}

lemma lemma_ReadReplyVCIsLargerThanAllPreviousWritesConstant(
    b:Behavior<CMState>,
    i:int
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllReadReplyVCIsLargerThanAllPreviousWrites(b, i-1)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets
    requires forall p :: p in b[i-1].environment.sentPackets ==> p in b[i].environment.sentPackets
    requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocalsAlways(b, i)
    ensures AllReadReplyVCIsLargerThanAllPreviousWrites(b, i)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);

    assert forall p :: p in b[i-1].environment.sentPackets && p.msg.Message_Read_Reply? ==> ReadReplyVCIsLargerThanAllPreviousWrites(b, i-1, p);
    assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> p in b[i-1].environment.sentPackets;
    assert forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> ReadReplyVCIsLargerThanAllPreviousWrites(b, i-1, p);
    if !StepSendsWriteReply(b[i-1], b[i]) {
        assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
        return;
    }

    assert StepSendsWriteReply(b[i-1], b[i]);
    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write_Reply?;
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
    assert WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p);
    assert AllReadReplyVCIsLargerThanAllPreviousWrites(b, i);
}

}