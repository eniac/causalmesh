include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Heuristics.i.dfy"
include "constants.dfy"

module CausalMesh_Proof_Environment_i {
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

lemma lemma_PacketsStaysInSentPackets(
    b:Behavior<CMState>,
    i:int, 
    j:int
)
    requires IsValidBehaviorPrefix(b, j)
    requires 0 <= i <= j
    ensures forall p :: p in b[i].environment.sentPackets ==> p in b[j].environment.sentPackets
{
    if j == i {

    } else {
        forall p | p in b[i].environment.sentPackets
            ensures p in b[j].environment.sentPackets
        {
            lemma_PacketStaysInSentPackets(b, i, j, p);
        }
    }
}

lemma lemma_PacketStaysInSentPackets(
    b:Behavior<CMState>,
    i:int, 
    j:int,
    p:Packet
)
    requires IsValidBehaviorPrefix(b, j)
    requires 0 <= i <= j
    requires p in b[i].environment.sentPackets
    ensures p in b[j].environment.sentPackets
{
    if j == i {

    } else {
        lemma_PacketStaysInSentPackets(b, i, j-1, p);
        assert p in b[j-1].environment.sentPackets;
        var k := j-1;
        lemma_AssumptionsMakeValidTransition(b, k);
        assert CMNext(b[k], b[k+1]);
        lemma_PacketStaysInSentPackets_help(b, k, j);
        assert CMNext(b[j-1], b[j]);
        assert p in b[j].environment.sentPackets;
    }
}

lemma lemma_PacketStaysInSentPackets_help(
    b:Behavior<CMState>,
    k:int,
    j:int
)
    requires IsValidBehaviorPrefix(b, j)
    requires k == j-1
    requires CMNext(b[k], b[k+1])
    ensures CMNext(b[j-1], b[j])
{

}

}