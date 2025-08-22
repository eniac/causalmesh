include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "action.dfy"
include "environment.dfy"
include "packet_sending.dfy"

module CausalMesh_Proof_MessageWrite_i {
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

lemma lemma_MetasInClientLocalHasCorrspondingWriteMessage(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    k:Key,
    meta:Meta
)
returns (
    j:int,
    p_wreply:Packet
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires CMNext(b[i], b[i+1])
    requires 0 <= idx < Clients
    requires k in b[i+1].clients[idx].c.local
    requires meta == b[i+1].clients[idx].c.local[k]
    // requires k !in b[i].clients[idx].c.local || (k in b[i].clients[idx].c.local && meta != b[i].clients[idx].c.local[k])
    ensures p_wreply.msg.Message_Write_Reply?
    ensures meta.key == p_wreply.msg.key_wreply
    ensures meta.vc == p_wreply.msg.vc_wreply
    ensures p_wreply in b[i].environment.sentPackets
    ensures 0 < j <= i
    ensures 0 <= p_wreply.src < Nodes
{
    if i == 0 {
        return;
    }

    if k in b[i].clients[idx].c.local && meta == b[i].clients[idx].c.local[k]
    {
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        assert IsValidBehaviorPrefix(b, i);
        assert i-1 >= 0;
        assert CMNext(b[i-1], b[i]);
        assert 0 <= idx < Clients;
        assert k in b[i].clients[idx].c.local;
        assert meta == b[i].clients[idx].c.local[k];

        j, p_wreply := lemma_MetasInClientLocalHasCorrspondingWriteMessage(b, i-1, idx, k, meta);
        return;
    }

    lemma_AssumptionsMakeValidTransition(b, i-1);
    lemma_ConstantsAllConsistent(b, i);
    lemma_ConstantsAllConsistent(b, i-1);

    assert CMNext(b[i-1], b[i]);
    var ios1 := lemma_ActionThatInsertMetaIntoLocalIsProcessWriteReply(b[i], b[i+1], idx, k, meta);

    var p_write_reply := ios1[0].r;
    assert meta.key == p_write_reply.msg.key_wreply;
    assert meta.vc == p_write_reply.msg.vc_wreply;
    j := i;
    p_wreply := p_write_reply;
    // var server, ios2 := lemma_FindTheServerThatSentWriteReply(b, i, p_write_reply);

    // p_write := ios2[0].r;
}

lemma lemma_FindTheServerThatSentWriteReply(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
returns (
    idx:int,
    ios:seq<CMIo>
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires p.msg.Message_Write_Reply?
    requires p in b[i].environment.sentPackets
    ensures 0 <= idx < Nodes
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Write?
{
    if i == 0 {
        return;
    }

    if p in b[i-1].environment.sentPackets
    {
        idx, ios := lemma_FindTheServerThatSentWriteReply(b, i-1, p);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    idx, ios := lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(b[i-1], b[i], p);
}

lemma lemma_FindTheClientThatSentWriteContainsMeta(
    b:Behavior<CMState>,
    i:int,
    p:Packet,
    k:Key,
    meta:Meta
)
returns (
    j:int,
    idx:int,
    ios:seq<CMIo>
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 <= i
    requires p.msg.Message_Write?
    requires p in b[i].environment.sentPackets
    requires k in p.msg.local
    requires meta == p.msg.local[k]
    ensures 0 <= idx < Clients
    ensures |ios| > 0
    ensures LIoOpSend(p) in ios
    ensures CMNext(b[j], b[j+1])
    ensures 0 < j < i
    ensures k in b[j].clients[idx].c.local
    ensures meta == b[j].clients[idx].c.local[k]
{
    if i == 0 {
        return;
    }

    if p in b[i-1].environment.sentPackets
    {
        j, idx, ios := lemma_FindTheClientThatSentWriteContainsMeta(b, i-1, p, k, meta);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    j := i-1;
    idx, ios := lemma_ActionThatSendsWriteIsClientSendWrite(b[i-1], b[i], p);
    assert CMNextClient(b[i-1], b[i], idx, ios);
    assert LClientNext(b[i-1].clients[idx], b[i].clients[idx], ios);
    assert SendWrite(b[i-1].clients[idx].c, b[i].clients[idx].c, ExtractSentPacketsFromIos(ios));
    assert k in b[i-1].clients[idx].c.local;
    assert meta == b[i-1].clients[idx].c.local[k];
}
}