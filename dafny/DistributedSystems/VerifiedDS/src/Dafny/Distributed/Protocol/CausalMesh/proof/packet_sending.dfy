include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "action.dfy"

module CausalMesh_Proof_PacketSending_i {
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

lemma lemma_ActionThatSendsReadReplyIsServerReceiveRead(
    ps:CMState,
    ps':CMState,
    p:Packet
) returns (
    idx:int,
    ios:seq<CMIo>
)
    requires 0 <= p.src < Nodes
    requires p.msg.Message_Read_Reply?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires CMNext(ps, ps')
    ensures 0 <= idx < Nodes
    ensures CMNextServer(ps, ps', idx, ios)
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Read?
    ensures LIoOpSend(p) in ios
    // ensures ios[0].r.dst == idx
    ensures ReceiveRead(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, [p])
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| CMNextServer(ps, ps', idx, ios) && LIoOpSend(p) in ios;

    assert CMNextServer(ps, ps', idx, ios);
    assert LServerNext(ps.servers[idx], ps'.servers[idx], ios);
    assert ServerNextProcessPacket(ps.servers[idx].s, ps'.servers[idx].s, ios);
    assert ServerValid(ps.servers[idx].s);
    assert |ios| >= 1;
    assert !ios[0].LIoOpTimeoutReceive?;
    assert ios[0].LIoOpReceive?;
    assert PacketValid(ios[0].r);
    if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation?{
        assert ServerProcessPacket(ps.servers[idx].s, ps'.servers[idx].s, ios);
        assert ios[0].r.msg.Message_Read?;
    } 
    else {
        assert |ios| == 1;
        var sent_packets := ExtractSentPacketsFromIos(ios);
        assert sent_packets == [];
        assert false;
    }
}

lemma lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(
    ps:CMState,
    ps':CMState,
    p:Packet
    // pp:Packet
) returns (
    idx:int,
    ios:seq<CMIo>
)
    requires 0 <= p.src < Nodes
    requires p.msg.Message_Write_Reply?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires CMNext(ps, ps')
    ensures 0 <= idx < Nodes
    ensures CMNextServer(ps, ps', idx, ios)
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Write?
    ensures LIoOpSend(p) in ios
    // ensures ios[0].r.dst == idx
    ensures ReceiveWrite(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| CMNextServer(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_TheSendPktsInWriteReplyAreExistInSentPackets(
    ps:CMState,
    ps':CMState,
    idx:int,
    ios:seq<CMIo>
)
    requires CMNext(ps, ps')
    requires 0 <= idx < Nodes
    requires CMNextServer(ps, ps', idx, ios)
    requires |ios| > 0
    requires ios[0].LIoOpReceive?
    requires ios[0].r.msg.Message_Write?
    requires ReceiveWrite(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
    ensures var sp := ExtractSentPacketsFromIos(ios);
            forall p :: p in sp ==> p in ps'.environment.sentPackets // && p !in ps.environment.sentPackets
{
    assert CMNextCommon(ps, ps');
    assert LEnvironment_Next(ps.environment, ps'.environment);
    assert LEnvironment_PerformIos(ps.environment, ps'.environment, idx, ios);
    assert ps'.environment.sentPackets == ps.environment.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
    var sp := ExtractSentPacketsFromIos(ios);
    assert forall p :: p in sp ==> p in ps'.environment.sentPackets;
}



lemma lemma_ActionThatSendsReadIsClientSendRead(
    ps:CMState,
    ps':CMState,
    p:Packet
) returns (
    idx:int,
    ios:seq<CMIo>
)
    requires Nodes <= p.src < Nodes + Clients
    requires p.msg.Message_Read?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires CMNext(ps, ps')
    ensures 0 <= idx < Clients
    ensures CMNextClient(ps, ps', idx, ios)
    ensures LIoOpSend(p) in ios
    ensures SendRead(ps.clients[idx].c, ps'.clients[idx].c, [p])
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| CMNextClient(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsWriteIsClientSendWrite(
    ps:CMState,
    ps':CMState,
    p:Packet
) returns (
    idx:int,
    ios:seq<CMIo>
)
    requires Nodes <= p.src < Nodes + Clients
    requires p.msg.Message_Write?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires CMNext(ps, ps')
    ensures 0 <= idx < Clients
    ensures CMNextClient(ps, ps', idx, ios)
    ensures LIoOpSend(p) in ios
    ensures SendWrite(ps.clients[idx].c, ps'.clients[idx].c, [p])
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| CMNextClient(ps, ps', idx, ios) && LIoOpSend(p) in ios;
}

lemma lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(
    ps:CMState,
    ps':CMState,
    p:Packet
) returns (
    idx:int,
    ios:seq<CMIo>
)
    requires 0 <= p.src < Nodes
    requires 0 <= p.dst < Nodes
    requires p.msg.Message_Propagation?
    requires p in ps'.environment.sentPackets
    requires p !in ps.environment.sentPackets
    requires CMNext(ps, ps')
    ensures 0 <= idx < Nodes
    ensures CMNextServer(ps, ps', idx, ios)
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation?
    ensures LIoOpSend(p) in ios
    ensures ios[0].r.dst == idx
    ensures ios[0].r.msg.Message_Propagation? ==> ReceivePropagate(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
    ensures ios[0].r.msg.Message_Write? ==> ReceiveWrite(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
{
    assert ps.environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in ps.environment.nextStep.ios;
    idx, ios :| CMNextServer(ps, ps', idx, ios) && LIoOpSend(p) in ios;

    assert CMNextServer(ps, ps', idx, ios);
    assert LEnvironment_Next(ps.environment, ps'.environment);
    assert IsValidLEnvStep(ps.environment, ps.environment.nextStep);
    assert ps.environment.nextStep.actor == idx;
    assert IsValidLIoOp(ios[0], ps.environment.nextStep.actor, ps.environment);
    
    assert LServerNext(ps.servers[idx], ps'.servers[idx], ios);
    assert ServerNextProcessPacket(ps.servers[idx].s, ps'.servers[idx].s, ios);
    assert ServerValid(ps.servers[idx].s);
    assert |ios| >= 1;
    assert !ios[0].LIoOpTimeoutReceive?;
    assert ios[0].LIoOpReceive?;
    assert ios[0].r.dst == idx;
    assert PacketValid(ios[0].r);
    if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation?{
        assert ServerProcessPacket(ps.servers[idx].s, ps'.servers[idx].s, ios);
        assert ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation?;
        if ios[0].r.msg.Message_Write? {
            assert ReceiveWrite(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
        }
        else 
        {
            assert ReceivePropagate(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
        }
        // assert ReceivePropagate(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios)) ||
        //     ReceiveWrite(ps.servers[idx].s, ps'.servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
    } 
    else {
        // assert ios[0].r.dst == idx;
        assert |ios| == 1;
        var sent_packets := ExtractSentPacketsFromIos(ios);
        assert sent_packets == [];
        assert false;
    }
}

lemma lemma_ActionThatInsertMetaIntoLocalIsProcessWriteReply(
    ps:CMState,
    ps':CMState,
    idx:int,
    k:Key,
    meta:Meta
)
returns(
    ios:seq<CMIo>
)
    requires 0 <= idx < Clients
    requires CMNext(ps, ps')
    requires k in ps'.clients[idx].c.local && meta == ps'.clients[idx].c.local[k]
    requires k !in ps.clients[idx].c.local || (k in ps.clients[idx].c.local && meta != ps.clients[idx].c.local[k])
    ensures CMNextClient(ps, ps', idx, ios)
    ensures |ios| > 0
    ensures ios[0].LIoOpReceive?
    ensures ios[0].r.msg.Message_Write_Reply?
    ensures ReceiveWriteReply(ps.clients[idx].c, ps'.clients[idx].c, ios[0].r, ExtractSentPacketsFromIos(ios))
{
    ios :| CMNextClient(ps, ps', idx, ios);

    var s := ps.clients[idx];
    var s' := ps'.clients[idx];

    assert LClientNext(s, s', ios);

    assert |ios| >= 1;
    assert !ios[0].LIoOpTimeoutReceive?;
    assert ios[0].LIoOpReceive?;
    assert PacketValid(ios[0].r);

    var p := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);

    assert p.msg.Message_Write_Reply?;
}

// lemma lemma_FindTheStartServerOfPropagation(
//     b:Behavior<CMState>,
//     i:int,

// )
}