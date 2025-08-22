include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "constants.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Actions_i {
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
import opened Collections__Seqs_s
import opened Collections__Maps_i

  lemma lemma_ActionThatChangesServerIsThatServersAction(
    b:Behavior<CMState>,
    i:int,
    idx:int
  )
    returns (ios:seq<CMIo>)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].servers|
    requires 0 <= idx < |b[i+1].servers|
    requires b[i+1].servers[idx] != b[i].servers[idx]
    ensures  b[i].environment.nextStep.LEnvStepHostIos?
    ensures  0 <= idx < Nodes
    ensures  b[i].environment.nextStep.actor == idx
    ensures  ios == b[i].environment.nextStep.ios
    ensures  CMNext(b[i], b[i+1])
    ensures  CMNextServer(b[i], b[i+1], idx, ios)
    ensures |ios| > 0 && ios[0].LIoOpReceive? ==> ios[0].r.dst == idx
  {
    lemma_AssumptionsMakeValidTransition(b, i);
    // lemma_ConstantsAllConsistent(b, i);
    assert CMNext(b[i], b[i+1]);
    ios :| CMNextServer(b[i], b[i+1], idx, ios);
    var ps := b[i];
    var ps' := b[i+1];
    assert LEnvironment_Next(ps.environment, ps'.environment);
    assert IsValidLEnvStep(ps.environment, ps.environment.nextStep);
    assert ps.environment.nextStep.actor == idx;
    assert IsValidLIoOp(ios[0], ps.environment.nextStep.actor, ps.environment);
    if |ios| > 0 && ios[0].LIoOpReceive?
    {
      assert ios[0].r.dst == idx;
    }
  }

  lemma lemma_ActionThatChangesClientIsThatClientsAction(
    b:Behavior<CMState>,
    i:int,
    idx:int
  )
    returns (ios:seq<CMIo>)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 <= i
    requires 0 <= idx < |b[i].clients|
    requires 0 <= idx < |b[i+1].clients|
    requires b[i+1].clients[idx] != b[i].clients[idx]
    ensures  b[i].environment.nextStep.LEnvStepHostIos?
    ensures  0 <= idx < Clients
    ensures  b[i].environment.nextStep.actor == idx + Nodes
    ensures  ios == b[i].environment.nextStep.ios
    ensures  CMNext(b[i], b[i+1])
    ensures  CMNextClient(b[i], b[i+1], idx, ios)
  {
    lemma_AssumptionsMakeValidTransition(b, i);

    assert CMNext(b[i], b[i+1]);
    ios :| CMNextClient(b[i], b[i+1], idx, ios);
  }

  function {:opaque} ConvertBehaviorSeqToImap<T>(s:seq<T>):imap<int, T>
    requires |s| > 0
    ensures  imaptotal(ConvertBehaviorSeqToImap(s))
    ensures  forall i :: 0 <= i < |s| ==> ConvertBehaviorSeqToImap(s)[i] == s[i]
  {
    imap i {:trigger s[i]} :: if i < 0 then s[0] else if 0 <= i < |s| then s[i] else last(s)
  }
}