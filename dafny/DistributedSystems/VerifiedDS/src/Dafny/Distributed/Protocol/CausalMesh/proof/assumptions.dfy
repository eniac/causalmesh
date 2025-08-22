include "../distributed_system.dfy"
include "../../../Common/Collections/Maps2.i.dfy"

module CausalMesh_proof_Assumptions_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened Temporal__Temporal_s
import opened Collections__Maps2_s

predicate IsValidBehaviorPrefix(
  b:Behavior<CMState>,
  i:int
  )
{
  && imaptotal(b)
  && CMInit(b[0])
  && (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]))
}

lemma lemma_BehaviorValidImpliesOneStepValid(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    ensures CMNext(b[i-1], b[i])
{
    ghost var j := i - 1;
    assert 0 <= j < i;
    assert j + 1 == i;
    assert CMNext(b[j], b[j+1]);
}

lemma lemma_BehaviorValidImpliesAllStepsValid(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    ensures forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
{
    if i == 0 {
      return;
    }

    if i == 1 {
      // assert (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]));
      // var j := i-1;
      // assert j == 0;
      // assert 
      // assert CMNext(b[0], b[1]);
      lemma_BehaviorValidImpliesOneStepValid(b, i);
      assert CMNext(b[0], b[1]);
      return;
    }

    lemma_BehaviorValidImpliesAllStepsValid(b, i-1);
    assume forall j :: 0 <= j < i-1 ==> CMNext(b[j], b[j+1]);

    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert CMNext(b[i-1], b[i]);
    assume forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1]);
}

/** if a version has dependency, then its vc is larder than 0 */
lemma {:axiom} lemma_MetaWithNonEmptyDepsImpliesTheVCLargerThanZero(
  m:Meta
)
  requires MetaValid(m)
  requires |m.deps| > 0
  ensures VCHappendsBefore(EmptyMeta(m.key).vc, m.vc)
// {

// }
}