include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "clients_are_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ReadDepsIsMet_i {
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
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened CausalMesh_Proof_ClientsAreMet_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_ReadDepsIsMetOnAllServersPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 < j <= i ==> AllClientsAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j)
{
    if i == 0 {
        return;
    }

    if i == 1{
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        if !StepSendsRead(b[i-1], b[i]){
            assert AllReadDepsAreMet(b, i);
        } else {
            var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read?;
            assert p.msg.deps_read == map[];
            assert AllReadDepsAreMet(b, i);
        }
        assert forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    if !StepSendsRead(b[i-1], b[i]){
        lemma_ReadDepsIsMetOnAllServersPrefix(b, i-1);
        assert forall j :: 0 < j <= i-1 ==> AllReadDepsAreMet(b, j);
        assert AllReadDepsAreMet(b, i-1);
        forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Read?
            ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read)
        {
            assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
            assert 1 < i;
            assert IsValidBehaviorPrefix(b, i);
            assert  CMNext(b[i-1], b[i]);
            assert DependencyValid(rp.msg.deps_read);
            assert ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
            lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_read);
            assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
        }
        assert AllReadDepsAreMet(b, i);
        assert forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j);
        return;
    }

    lemma_ReadDepsIsMetOnAllServersPrefix(b, i-1);
    assert forall j :: 0 < j <= i-1 ==> AllReadDepsAreMet(b, j);
    assert AllReadDepsAreMet(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read?;
    assert PacketValid(p);
    assert CMNext(b[i-1], b[i]);
    assert p.msg.Message_Read?;
    assert p !in b[i-1].environment.sentPackets;
    assert p in b[i].environment.sentPackets;
    assert forall j :: 0 <= j < |b[i-1].clients| ==> Nodes <= b[i-1].clients[j].c.id < Nodes + Clients;
    assert Nodes <= p.src < Nodes +  Clients;
    var idx, ios := lemma_ActionThatSendsReadIsClientSendRead(b[i-1], b[i], p);

    lemma_ClientReadDepsIsMetOnAllServers(b, i, idx, [p]);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_read);
    assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Read? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
    
    assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Read? ==> 
        AllReadDepsSmallerThanPVCRead(p.msg.pvc_read, p.msg.deps_read);
    

    forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Read?
        ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read)
    {
        assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
        lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_read);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
    }
    assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Read? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
    assert forall rp :: rp in b[i].environment.sentPackets && rp.msg.Message_Read? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
    assert AllReadDepsAreMet(b, i);
    assert forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j);
}

// lemma lemma_ReadDepsIsMetOnAllServersPrefix(
//     b:Behavior<CMState>,
//     i:int
// )
//     requires 0 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires forall j :: 0 < j <= i ==> AllClientsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllReadDepsAreMet(b, i)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1{
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         if !StepSendsRead(b[i-1], b[i]){
//             assert AllReadDepsAreMet(b, i);
//         } else {
//             var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read?;
//             assert p.msg.deps_read == map[];
//             assert AllReadDepsAreMet(b, i);
//         }
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if !StepSendsRead(b[i-1], b[i]){
//         lemma_ReadDepsIsMetOnAllServersPrefix(b, i-1);
//         assume AllReadDepsAreMet(b, i-1);
//         forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Read?
//             ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read)
//         {
//             assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
//             assert 1 < i;
//             assert IsValidBehaviorPrefix(b, i);
//             assert  CMNext(b[i-1], b[i]);
//             assert DependencyValid(rp.msg.deps_read);
//             assert ServerNextDoesNotDecreaseVersions(b[i-1], b[i]);
//             lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_read);
//             assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
//         }
//         assert AllReadDepsAreMet(b, i);
//         return;
//     }

//     lemma_ReadDepsIsMetOnAllServersPrefix(b, i-1);
//     assume AllReadDepsAreMet(b, i-1);

//     var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Read?;
//     assert PacketValid(p);
//     assert CMNext(b[i-1], b[i]);
//     assert p.msg.Message_Read?;
//     assert p !in b[i-1].environment.sentPackets;
//     assert p in b[i].environment.sentPackets;
//     assert forall j :: 0 <= j < |b[i-1].clients| ==> Nodes <= b[i-1].clients[j].c.id < Nodes + Clients;
//     assert Nodes <= p.src < Nodes +  Clients;
//     var idx, ios := lemma_ActionThatSendsReadIsClientSendRead(b[i-1], b[i], p);

//     lemma_ClientReadDepsIsMetOnAllServers(b, i, idx, [p]);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_read);
//     assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Read? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
    

//     forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Read?
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read)
//     {
//         assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_read);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_read);
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
//     }
//     assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Read? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
//     assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
//     assert forall rp :: rp in b[i].environment.sentPackets && rp.msg.Message_Read? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_read);
// }

predicate StepSendsRead(s:CMState, s':CMState)
    requires CMNext(s, s')
{
    exists p :: p in s'.environment.sentPackets && p.msg.Message_Read? && p !in s.environment.sentPackets
}

lemma lemma_ClientReadDepsIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    sp:seq<Packet>
)
    requires i > 1
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Clients
    requires ClientValid(b[i-1].clients[idx].c)
    requires |sp| > 0
    requires SendRead(b[i-1].clients[idx].c, b[i].clients[idx].c, sp)
    requires AllClientsAreMet(b, i)

    ensures AllVersionsInDepsAreMetOnAllServers(b, i, sp[0].msg.deps_read)
{
    reveal_ServersAndClientsAreValid();
    var s := b[i-1].clients[idx].c;
    var s' := b[i].clients[idx].c;

    assert |sp| == 1;
    var p_read := sp[0];
    assert p_read.msg.Message_Read?;
    
    assert p_read.msg.deps_read == s.deps;
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p_read.msg.deps_read);
}

}