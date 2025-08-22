include "../distributed_system.dfy"
include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "clients_are_met.dfy"
include "cache_does_not_decrease.dfy"
include "servers_are_met.dfy"
// include "clients_are_met.dfy"
include "read_deps_is_met.dfy"
include "write_deps_is_met.dfy"
include "read_reply_is_met.dfy"
include "monotonic_read.dfy"
include "monotonic_write.dfy"
include "read_after_write.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_PullDeps_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_Proof_CausalCut_i
import opened CausalMesh_Proof_CacheDoesNotDecrease_i
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened CausalMesh_Proof_ClientsAreMet_i
import opened CausalMesh_Proof_ServersAreMet_i
import opened CausalMesh_Proof_ReadDepsIsMet_i
import opened CausalMesh_Proof_WriteDepsIsMet_i
import opened CausalMesh_Proof_Monotonic_Read_i
import opened CausalMesh_Proof_Monotonic_Write_i
import opened CausalMesh_Proof_Read_After_Write_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_CausalMesh_correctness(
    behavior:seq<CMState>
)
    requires |behavior| > 0 
    requires CMInit(behavior[0])
    requires forall i {:trigger CMNext(behavior[i], behavior[i+1])} :: 
                0 <= i < |behavior| - 1 ==> CMNext(behavior[i], behavior[i+1])

    ensures forall i :: 0 <= i < |behavior| ==> AllServersAreCausalCut(behavior[i]) /** each server's ccache is always a causalcut */
    // ensures var b := ConvertBehaviorSeqToImap(behavior);
            // forall j :: 0 <= j < |behavior|-1 ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
{
    /** each server's ccache is always a causalcut */
    lemma_AllServersAreCausalCutAtAnyTime(behavior);

    var b := ConvertBehaviorSeqToImap(behavior);
    var i := |behavior|-1;
    assert IsValidBehaviorPrefix(b, i);

    /** all key's version on each server's ccache will never decrease */
    lemma_CMNextCacheDoesNotDecreasePrefix(b, i); 
    assert forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1]);

    /** let us assume them for now, they will be proved later */
    behaviro_propoties(b, i);
    assume forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
    assume forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j);
    assume forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j);

    /** all clients' local deps are satisfied on all servers */
    lemma_AllClientsAreMetPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllClientsAreMet(b, j);

    /** all versions on each server's ccache is satisfied on all servers */
    lemma_AllServersAreMetPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllServersAreMet(b, j);

    /** all read request's deps is satisfied on all servers */
    lemma_ReadDepsIsMetOnAllServersPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j);

    /** all write request's deps is satisfied on all servers */
    lemma_WriteDepsIsMetOnAllServersPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);

    /** all read reply's <k, vc> is satisfied on all servers */
    lemma_ReadRepliesIsMetOnAllServersPrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j);

    reveal_ConvertBehaviorSeqToImap();

    /** monotonic read */
    lemma_MonotonicRead(behavior);
    assert var bb := ConvertBehaviorSeqToImap(behavior); 
        && bb == b
        && forall j :: 0 <= j < |behavior| ==> MonotonicRead(bb, j);
    assert forall j :: 0 <= j < |behavior| ==> MonotonicRead(b, j);

    /** monotonic write */
    lemma_MonotonicWritePrefix(b, i);
    assert forall j :: 0 < j <= i ==> AllWriteReplyHasCoorspondingWriteWithSmallerOrEqVCInDepsAndLocals(b, j);

    /** writes follow reads */
    lemma_ReadAWriteCanObserveAllItsPreviousReadsAndWrites(behavior);
    assert forall i :: 0 <= i < |behavior| ==> AllReadReplyVCIsLargerThanAllPreviousWritesReal(b, i);
}

lemma {:axiom} behaviro_propoties(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    ensures forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    ensures forall j :: 0 < j <= i ==> AllReadDepsAreMet(b, j)
    ensures forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j)
}