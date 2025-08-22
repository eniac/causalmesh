include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "action.dfy"
include "environment.dfy"
include "packet_sending.dfy"

module CausalMesh_Proof_MessageReadReply_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Environment_i
import opened CausalMesh_Proof_PacketSending_i

lemma lemma_ReadReplyHasCorrspondingReadMessage(
    b:Behavior<CMState>,
    i:int,
    p_rreply:Packet
) returns (
    p_read:Packet
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires p_rreply in b[i].environment.sentPackets
    requires 0 <= p_rreply.src < Nodes 
    requires p_rreply.msg.Message_Read_Reply?
    ensures p_read in b[i].environment.sentPackets
    ensures 0 <= p_read.src < Clients
    ensures p_read.msg.Message_Read?
    ensures p_read.msg.key_read == p_rreply.msg.key_rreply
    ensures p_read.dst == p_rreply.src
{
    if i == 0 
    {
        return;
    }

    if p_rreply in b[i-1].environment.sentPackets {
        p_read := lemma_ReadReplyHasCorrspondingReadMessage(b, i-1, p_rreply);
        lemma_PacketStaysInSentPackets(b, i-1, i, p_read);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, i-1);
    lemma_ConstantsAllConsistent(b, i);
    lemma_ConstantsAllConsistent(b, i-1);
    var idx, ios := lemma_ActionThatSendsReadReplyIsServerReceiveRead(b[i-1], b[i], p_rreply);
    p_read := ios[0].r;
}
}