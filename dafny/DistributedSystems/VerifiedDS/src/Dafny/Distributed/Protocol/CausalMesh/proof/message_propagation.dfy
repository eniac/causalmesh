include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "action.dfy"
include "environment.dfy"
include "packet_sending.dfy"

module CausalMesh_Proof_MessagePropagation_i {
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

lemma lemma_PropagationHasCoorspondingPropagationOrWriteMessage(
    b:Behavior<CMState>,
    i:int,
    p_pro:Packet
)
returns (
    p:Packet
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires p_pro in b[i].environment.sentPackets
    requires 0 <= p_pro.src < Nodes 
    requires p_pro.msg.Message_Propagation?
    ensures p in b[i].environment.sentPackets
    // ensures 0 <= p.src < Nodes
    ensures p.msg.Message_Propagation? || p.msg.Message_Write?
    // // ensures p.msg.key_read == p.msg.key_
    ensures p.dst == p_pro.src
{
    if i == 0 {
        return;
    }

    if p_pro in b[i-1].environment.sentPackets {
        p := lemma_PropagationHasCoorspondingPropagationOrWriteMessage(b, i-1, p_pro);
        lemma_PacketStaysInSentPackets(b, i-1, i, p);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, i-1);
    lemma_ConstantsAllConsistent(b, i);
    lemma_ConstantsAllConsistent(b, i-1);
    var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p_pro);
    p := ios[0].r;
}

lemma lemma_PropagationHasInitialWriteMessage(
    b:Behavior<CMState>,
    i:int,
    p_pro:Packet
) returns (
    j:int,
    p:Packet
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires p_pro in b[i].environment.sentPackets
    requires 0 <= p_pro.src < Nodes 
    requires p_pro.msg.Message_Propagation?
    ensures p in b[i].environment.sentPackets
    ensures p.msg.Message_Write?
    ensures 0 <= j < i
{
    if i == 0 {
        return;
    }

    if p_pro in b[i-1].environment.sentPackets {
        j, p := lemma_PropagationHasInitialWriteMessage(b, i-1, p_pro);
        lemma_PacketStaysInSentPackets(b, i-1, i, p);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, i-1);
    lemma_ConstantsAllConsistent(b, i);
    lemma_ConstantsAllConsistent(b, i-1);

    var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p_pro);
    var pp := ios[0].r;
    // p := pp;
    if pp.msg.Message_Write? {
        j := i-1;
        p := pp;
    } else {
        assert pp.msg.Message_Propagation?;
        j, p := lemma_PropagationHasInitialWriteMessage(b, i-1, pp);
        // var ppp := lemma_PropagationHasCoorspondingPropagationOrWriteMessage(b, i, pp);
    }
}
}