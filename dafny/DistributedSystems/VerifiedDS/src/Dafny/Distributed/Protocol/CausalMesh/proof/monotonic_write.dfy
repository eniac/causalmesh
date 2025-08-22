include "../distributed_system.dfy"
include "causalcut.dfy"
include "packet_sending.dfy"
// include "message_read_reply.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Monotonic_Write_i {
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
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


predicate WriteReplyIsLargerThanVCInDeps(deps:Dependency, vc:VectorClock)
    requires DependencyValid(deps)
    requires VectorClockValid(vc)
{
    forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
}

predicate WriteReplyIsLargerThanVCInLocal(local:map<Key, Meta>, vc:VectorClock)
    requires forall k :: k in local ==> MetaValid(local[k])
    requires VectorClockValid(vc)
{
    forall k :: k in local ==> VCHappendsBefore(local[k].vc, vc) || VCEq(local[k].vc, vc)
}

/* with client operation number */
predicate WriteReplyHasCorrspondingWriteWithSmallerVC(
    b:Behavior<CMState>,
    i:int,
    p:Packet
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires p in b[i].environment.sentPackets && p.msg.Message_Write_Reply? && PacketValid(p)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    exists wp :: wp in b[i].environment.sentPackets && wp.msg.Message_Write?
                    && p.msg.opn_wreply == wp.msg.opn_write
                    && p.msg.key_wreply == wp.msg.key_write
                    && p.dst == wp.src
                    && WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, p.msg.vc_wreply)
                    && WriteReplyIsLargerThanVCInLocal(wp.msg.local, p.msg.vc_wreply)
}

/* without client operation number */
// predicate WriteReplyHasCorrspondingWriteWithSmallerVC(
//     b:Behavior<CMState>,
//     i:int,
//     p:Packet
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires p in b[i].environment.sentPackets && p.msg.Message_Write_Reply? && PacketValid(p)
// {
//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     forall wp :: wp in b[i].environment.sentPackets && wp.msg.Message_Write?
//                     && p.msg.key_wreply == wp.msg.key_write
//                     && p.dst == wp.src
//                     ==> WriteReplyIsLargerThanVCInDeps(wp.msg.deps_write, p.msg.vc_wreply)
//                         && WriteReplyIsLargerThanVCInLocal(wp.msg.local, p.msg.vc_wreply)
// }

predicate AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);

    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Write_Reply? ==> WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p)
}

predicate AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocalsAlways(
    b:Behavior<CMState>,
    i:int
)
    requires i >= 0
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
{
    forall j :: 0 < j <= i ==> AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, j)
}

lemma lemma_MonotonicWritePrefix(
    b:Behavior<CMState>,
    i:int
)
    requires i >= 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, j)
{
    if i == 0 {
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_MonotonicWritePrefix(b, i-1);

    lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, j);
}

lemma lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    ensures AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i)
    decreases i
{
    if i == 0 {
        return;
    }

    if i == 1 {
        // assume AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        assert CMNext(b[i-1], b[i]);
        lemma_WriteReplyHasCorrspondingWriteWithSmallerVCForIndexOne(b, i);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesAllStepsValid(b, i);

    if !StepSendsWriteReply(b[i-1], b[i]){
        // assume AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1);
        lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(b, i-1); 
        assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
        return;
    }

    lemma_WriteReplyHasHigerVCThanDepsAndLocalPrefix(b, i-1);
    // assume AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write_Reply?;

    // var pp :| pp in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Propagation?;

    assert PacketValid(p);

    var idx, ios := lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(b[i-1], b[i], p);

    var p_write := ios[0].r;
    var sp := ExtractSentPacketsFromIos(ios);

    
    assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, sp);
    lemma_ServerWriteReplyLargerVCThanLocalAndDeps(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, sp);
    assert p.msg.opn_wreply == p_write.msg.opn_write;
    assert p.dst == p_write.src;
    assert p.msg.key_wreply == p_write.msg.key_write;
    assert WriteReplyIsLargerThanVCInDeps(p_write.msg.deps_write, p.msg.vc_wreply);
    assert WriteReplyIsLargerThanVCInLocal(p_write.msg.local, p.msg.vc_wreply);
    assert WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p);

    assert 1 < i;
    assert IsValidBehaviorPrefix(b, i);
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1);
    assert 0 <= idx < Nodes;
    assert p in b[i].environment.sentPackets;
    assert p !in b[i-1].environment.sentPackets;
    assert p.msg.Message_Write_Reply?;
    assert PacketValid(p);
    assert p_write in b[i-1].environment.sentPackets;
    assert p_write.msg.Message_Write?;

    // assert |sp|== 2;
    // var p_pro := sp[1];
    // assert p_pro.msg.Message_Propagation?;
    // lemma_TheSendPktsInWriteReplyAreExistInSentPackets(b[i-1], b[i], idx, ios);
    // assert p_pro in b[i].environment.sentPackets;
    // assume p_pro !in b[i-1].environment.sentPackets;
    // assert sp[1].msg.Message_Propagation?;
    assert CMNext(b[i-1], b[i]);

    // lemma_WriteReplyHasCorrspondingWriteWithSmallerVCTransfer(b, i, idx, p, p_write, sp[1]);
    lemma_WriteReplyHasCorrspondingWriteWithSmallerVCTransfer2(b, i, idx, p, p_write, ios);
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
}

predicate StepSendsWriteReply(s:CMState, s':CMState)
    requires CMNext(s, s')
{
    // && s.environment.nextStep.LEnvStepHostIos?
    && (exists p :: p in s'.environment.sentPackets && p.msg.Message_Write_Reply? && p !in s.environment.sentPackets)
    // && (exists p :: p in s'.environment.sentPackets && p.msg.Message_Propagation? && p !in s.environment.sentPackets)
}

lemma lemma_WriteReplyHasCorrspondingWriteWithSmallerVCForIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    ensures !exists p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply?
    ensures AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i)
{
    // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
    assert CMNext(b[i-1], b[i]);
}

// lemma lemma_WriteReplyHasCorrspondingWriteWithSmallerVCTransfer(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     p:Packet,
//     p_write:Packet,
//     p_pro:Packet
// )
//     requires 1 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1)
//     requires 0 <= idx < Nodes
//     requires p in b[i].environment.sentPackets
//     requires p !in b[i-1].environment.sentPackets
//     requires p.msg.Message_Write_Reply?
//     requires PacketValid(p)
//     requires p_write in b[i-1].environment.sentPackets
//     requires p_write.msg.Message_Write?
//     requires p_pro in b[i].environment.sentPackets
//     requires p_pro !in b[i-1].environment.sentPackets
//     requires p_pro.msg.Message_Propagation?
//     requires CMNext(b[i-1], b[i])
//     requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, [p] + [p_pro])
//     requires WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p)
//     ensures AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i)
// {
//     // reveal_AllReadReplyHasCorrspondingReadWithSmallerVC();
//     assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1);
//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     assert forall pp :: pp in b[i-1].environment.sentPackets && pp.msg.Message_Write_Reply? ==> 
//         WriteReplyHasCorrspondingWriteWithSmallerVC(b, i-1, pp);
//     assert forall pp :: pp in b[i-1].environment.sentPackets ==> pp in b[i].environment.sentPackets;

//     assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Write_Reply? && pp in b[i-1].environment.sentPackets ==> 
//             WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, pp);
//     assert WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p);
//     lemma_ServerReceiveWriteOnlySentOneWriteReplyPacket(b, i, idx, p, p_write, p_pro);
//     // assume b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p} + {p_pro};
//     assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
// }

// lemma lemma_ServerReceiveWriteOnlySentOneWriteReplyPacket(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     p:Packet,
//     p_write:Packet,
//     p_pro:Packet
// )
//     requires 1 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1)
//     requires 0 <= idx < Nodes
//     requires p in b[i].environment.sentPackets
//     requires p !in b[i-1].environment.sentPackets
//     requires p.msg.Message_Write_Reply?
//     requires PacketValid(p)
//     requires p_write in b[i-1].environment.sentPackets
//     requires p_write.msg.Message_Write?
//     requires p_pro in b[i].environment.sentPackets
//     requires p_pro !in b[i-1].environment.sentPackets
//     requires p_pro.msg.Message_Propagation?
//     requires CMNext(b[i-1], b[i])
//     requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, [p] + [p_pro])
//     ensures b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p} + {p_pro}
// {
//     var idx, ios := lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(b[i-1], b[i], p);
//     assert ios[0].LIoOpReceive?;
//     // assert p_read == ios[0].r;
//     assert ios[1].LIoOpSend?;
//     var pkts := ExtractSentPacketsFromIos(ios);
//     assert p in pkts;
//     assert |pkts| == 2;
//     assert pkts == [p] + [p_pro];
//     assert LEnvironment_Next(b[i-1].environment, b[i].environment);
//     assert b[i-1].environment.nextStep.LEnvStepHostIos?;
//     assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
//     var pkts2 := set io | io in ios && io.LIoOpSend? :: io.s;
//     assert pkts2 == {p} + {p_pro};
//     assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p} + {p_pro};
// }

lemma lemma_WriteReplyHasCorrspondingWriteWithSmallerVCTransfer2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    p_write:Packet,
    ios:seq<CMIo>
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1)
    requires 0 <= idx < Nodes
    requires p in b[i].environment.sentPackets
    requires p !in b[i-1].environment.sentPackets
    requires p.msg.Message_Write_Reply?
    requires PacketValid(p)
    requires p_write in b[i-1].environment.sentPackets
    requires p_write.msg.Message_Write?
    requires LIoOpSend(p) in ios
    // requires p_pro in b[i].environment.sentPackets
    // requires p_pro !in b[i-1].environment.sentPackets
    // requires p_pro.msg.Message_Propagation?
    requires CMNext(b[i-1], b[i])
    requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, ExtractSentPacketsFromIos(ios))
    requires WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p)
    ensures AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i)
{
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall pp :: pp in b[i-1].environment.sentPackets && pp.msg.Message_Write_Reply? ==> 
        WriteReplyHasCorrspondingWriteWithSmallerVC(b, i-1, pp);
    assert forall pp :: pp in b[i-1].environment.sentPackets ==> pp in b[i].environment.sentPackets;

    assert forall pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Write_Reply? && pp in b[i-1].environment.sentPackets ==> 
            WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, pp);
    assert WriteReplyHasCorrspondingWriteWithSmallerVC(b, i, p);
    lemma_ServerReceiveWriteOnlySentOneWriteReplyPacket2(b, i, idx, p, p_write, ios);
    // assume b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p} + {p_pro};
    assert AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i);
}

lemma lemma_ServerReceiveWriteOnlySentOneWriteReplyPacket2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    p:Packet,
    p_write:Packet,
    ios:seq<CMIo>
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, i-1)
    requires 0 <= idx < Nodes
    requires p in b[i].environment.sentPackets
    requires p !in b[i-1].environment.sentPackets
    requires p.msg.Message_Write_Reply?
    requires PacketValid(p)
    requires p_write in b[i-1].environment.sentPackets
    requires p_write.msg.Message_Write?
    requires LIoOpSend(p) in ios
    // requires p_pro in b[i].environment.sentPackets
    // requires p_pro !in b[i-1].environment.sentPackets
    // requires p_pro.msg.Message_Propagation?
    requires CMNext(b[i-1], b[i])
    requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, p_write, ExtractSentPacketsFromIos(ios))
    // ensures b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p} + {p_pro}
    ensures var pkts := b[i].environment.sentPackets - b[i-1].environment.sentPackets;
            && p in pkts
            && !exists pp :: pp in pkts && pp != p && pp.msg.Message_Write_Reply?
{
    var idx, ios := lemma_ActionThatSendsWriteReplyIsServerReceiveWrite(b[i-1], b[i], p);
    assert ios[0].LIoOpReceive?;
    // assert p_read == ios[0].r;
    assert ios[1].LIoOpSend?;
    var pkts := ExtractSentPacketsFromIos(ios);
    assert p in pkts;
    // assert |pkts| == 2;
    assert LEnvironment_Next(b[i-1].environment, b[i].environment);
    assert b[i-1].environment.nextStep.LEnvStepHostIos?;
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
    var pkts2 := set io | io in ios && io.LIoOpSend? :: io.s;
    assert p in pkts2;
    assert !exists pp :: pp in pkts2 && pp != p && pp.msg.Message_Write_Reply?;
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + pkts2;
}


lemma lemma_ServerWriteReplyLargerVCThanLocalAndDeps(s:Server, s':Server, p:Packet, sp:seq<Packet>)
    requires p.msg.Message_Write?
    requires ServerValid(s)
    requires PacketValid(p) 
    requires ReceiveWrite(s, s', p, sp)
    // ensures |sp| == 2
    ensures sp[0].msg.Message_Write_Reply?
    ensures p.msg.key_write == sp[0].msg.key_wreply
    ensures forall k :: k in p.msg.local ==> 
                VCHappendsBefore(p.msg.local[k].vc, sp[0].msg.vc_wreply) || VCEq(p.msg.local[k].vc, sp[0].msg.vc_wreply)
    ensures forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], sp[0].msg.vc_wreply) || VCEq(p.msg.deps_write[k], sp[0].msg.vc_wreply)
{
    assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
    var local_metas := set m | m in p.msg.local.Values;
    var vcs_local := set m | m in local_metas :: m.vc;
    assert forall vc :: vc in vcs_local ==> VectorClockValid(vc); 
    var merged_vc := FoldVC(s.gvc, vcs_local);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc) || VCEq(vc, merged_vc);
    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, merged_vc) || VCEq(m.vc, merged_vc);
    assert forall k :: k in p.msg.local ==> p.msg.local[k] in local_metas;
    assert forall k :: k in p.msg.local ==> 
                VCHappendsBefore(p.msg.local[k].vc, sp[0].msg.vc_wreply) || VCEq(p.msg.local[k].vc, sp[0].msg.vc_wreply);

    var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];
    var merged_vc2 := FoldVC(merged_vc, vcs_deps);
    assert forall vc :: vc in vcs_deps ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], merged_vc2) || VCEq(p.msg.deps_write[k], merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> 
                VCHappendsBefore(p.msg.deps_write[k], sp[0].msg.vc_wreply) || VCEq(p.msg.deps_write[k], sp[0].msg.vc_wreply);
}

}