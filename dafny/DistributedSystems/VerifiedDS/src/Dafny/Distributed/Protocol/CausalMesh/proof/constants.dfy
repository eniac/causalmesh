include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "assumptions.dfy"

module CausalMesh_Proof_Constants_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
// import opened CausalMesh_Properties_i
import opened Temporal__Temporal_s
import opened Temporal__Rules_i
import opened Temporal__Heuristics_i
import opened CausalMesh_proof_Assumptions_i


predicate ConstantsAllConsistentInv(ps:CMState)
{
    && |ps.servers| == Nodes
    && |ps.clients| == Clients
    && (forall idx :: 0 <= idx < Nodes ==> ps.servers[idx].s.id == idx)
    && (forall idx :: 0 <= idx < Clients ==> ps.clients[idx].c.id == idx + Nodes)
}

lemma lemma_AssumptionsMakeValidTransition(
  b:Behavior<CMState>,
  i:int
  )
  requires IsValidBehaviorPrefix(b, i+1)
  requires 0 <= i
  ensures  CMNext(b[i], b[i+1])
{
  assert CMNext(b[i], b[i+1]);
}


lemma lemma_ConstantsAllConsistent(
  b:Behavior<CMState>,
  i:int
  )
  requires IsValidBehaviorPrefix(b, i)
  requires 0 <= i
  ensures  ConstantsAllConsistentInv(b[i])
{
  TemporalAssist();

  if i > 0
  {
    // lemma_test(b, i-1);
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_ConstantsAllConsistent(b, i-1);
    assert IsValidBehaviorPrefix(b, i);
    assert i-1 >= 0;
    lemma_AssumptionsMakeValidTransition(b, i-1);
    lemma_test(b, i);
    assert ConstantsAllConsistentInv(b[i]);
  }
}

lemma {:axiom} lemma_test(b:Behavior<CMState>, i:int)
  requires IsValidBehaviorPrefix(b, i)
  requires 0 <= i
  ensures ConstantsAllConsistentInv(b[i])

}