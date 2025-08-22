include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "clients_are_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_WriteDepsIsMet_i {
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


lemma lemma_WriteDepsIsMetOnAllServersPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 < j <= i ==> AllClientsAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
{
    if i == 0 {
        return;
    }

    if i == 1{
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        if !StepSendsWrite(b[i-1], b[i]){
            assert AllWriteDepsAreMet(b, i);
        } else {
            var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write?;
            assert p.msg.deps_write == map[];
            assert AllWriteDepsAreMet(b, i);
        }
        assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);

    if !StepSendsWrite(b[i-1], b[i]){
        lemma_WriteDepsIsMetOnAllServersPrefix(b, i-1);
        assume forall j :: 0 < j <= i-1 ==> AllWriteDepsAreMet(b, j);
        assert AllWriteDepsAreMet(b, i-1);
        forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Write?
            ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write)
        {
            assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
            lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_write);
            assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
        }
        assert AllWriteDepsAreMet(b, i);
        assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
        return;
    }

    lemma_WriteDepsIsMetOnAllServersPrefix(b, i-1);
    assume forall j :: 0 < j <= i-1 ==> AllWriteDepsAreMet(b, j);
    assert 0 < i-1 <= i-1;
    assert AllWriteDepsAreMet(b, i-1);

    var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write?;
    assert PacketValid(p);
    assert CMNext(b[i-1], b[i]);
    assert p.msg.Message_Write?;
    assert p !in b[i-1].environment.sentPackets;
    assert p in b[i].environment.sentPackets;
    assert forall j :: 0 <= j < |b[i-1].clients| ==> Nodes <= b[i-1].clients[j].c.id < Nodes + Clients;
    assert Nodes <= p.src < Nodes + Clients;
    var idx, ios := lemma_ActionThatSendsWriteIsClientSendWrite(b[i-1], b[i], p);

    lemma_ClientWriteDepsIsMetOnAllServers(b, i, idx, [p]);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_write);
    assume forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Write? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
    

    forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Write?
        ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write)
    {
        assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
        lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_write);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
    }
    assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Write? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
    assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
    assert forall rp :: rp in b[i].environment.sentPackets && rp.msg.Message_Write? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
    assert AllWriteDepsAreMet(b, i);
    assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
}



// lemma lemma_WriteDepsIsMetOnAllServersPrefix(
//     b:Behavior<CMState>,
//     i:int
// )
//     requires 0 < i
//     requires IsValidBehaviorPrefix(b, i)
//     requires forall j :: 0 < j <= i ==> AllClientsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     ensures AllWriteDepsAreMet(b, i)
// {
//     if i == 0 {
//         return;
//     }

//     if i == 1{
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         if !StepSendsWrite(b[i-1], b[i]){
//             assert AllWriteDepsAreMet(b, i);
//         } else {
//             var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write?;
//             assert p.msg.deps_write == map[];
//             assert AllWriteDepsAreMet(b, i);
//         }
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);

//     if !StepSendsWrite(b[i-1], b[i]){
//         lemma_WriteDepsIsMetOnAllServersPrefix(b, i-1);
//         assume AllWriteDepsAreMet(b, i-1);
//         forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Write?
//             ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write)
//         {
//             assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
//             lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_write);
//             assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
//         }
//         assert AllWriteDepsAreMet(b, i);
//         return;
//     }

//     lemma_WriteDepsIsMetOnAllServersPrefix(b, i-1);
//     assume AllWriteDepsAreMet(b, i-1);

//     var p :| p in b[i].environment.sentPackets && p !in b[i-1].environment.sentPackets && p.msg.Message_Write?;
//     assert PacketValid(p);
//     assert CMNext(b[i-1], b[i]);
//     assert p.msg.Message_Write?;
//     assert p !in b[i-1].environment.sentPackets;
//     assert p in b[i].environment.sentPackets;
//     assert forall j :: 0 <= j < |b[i-1].clients| ==> Nodes <= b[i-1].clients[j].c.id < Nodes + Clients;
//     assert Nodes <= p.src < Nodes + Clients;
//     var idx, ios := lemma_ActionThatSendsWriteIsClientSendWrite(b[i-1], b[i], p);

//     lemma_ClientWriteDepsIsMetOnAllServers(b, i, idx, [p]);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_write);
//     assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Write? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
    

//     forall rp | rp in b[i-1].environment.sentPackets && rp.msg.Message_Write?
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write)
//     {
//         assert AllVersionsInDepsAreMetOnAllServers(b, i-1, rp.msg.deps_write);
//         lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, rp.msg.deps_write);
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
//     }
//     assert forall rp :: rp in b[i-1].environment.sentPackets && rp.msg.Message_Write? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
//     assert b[i].environment.sentPackets == b[i-1].environment.sentPackets + {p};
//     assert forall rp :: rp in b[i].environment.sentPackets && rp.msg.Message_Write? ==> 
//         AllVersionsInDepsAreMetOnAllServers(b, i, rp.msg.deps_write);
// }

predicate StepSendsWrite(s:CMState, s':CMState)
    requires CMNext(s, s')
{
    exists p :: p in s'.environment.sentPackets && p.msg.Message_Write? && p !in s.environment.sentPackets
}

lemma lemma_ClientWriteDepsIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    sp:seq<Packet>
)
    requires i > 1
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Clients
    requires |sp| > 0
    requires SendWrite(b[i-1].clients[idx].c, b[i].clients[idx].c, sp)
    requires AllClientsAreMet(b, i)

    ensures AllVersionsInDepsAreMetOnAllServers(b, i, sp[0].msg.deps_write)
{
    var s := b[i-1].clients[idx].c;
    var s' := b[i].clients[idx].c;

    assert |sp| == 1;
    var p_write := sp[0];
    assert p_write.msg.Message_Write?;
    
    assert p_write.msg.deps_write == s.deps;
    assert AllVersionsInDepsAreMetOnAllServers(b, i, p_write.msg.deps_write);
}

}