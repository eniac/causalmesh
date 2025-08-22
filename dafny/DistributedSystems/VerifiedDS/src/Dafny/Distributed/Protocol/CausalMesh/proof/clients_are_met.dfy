include "../distributed_system.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "environment.dfy"
include "deps_are_met.dfy"
include "read_reply_is_met.dfy"
include "propagation.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_ClientsAreMet_i {
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
import opened CausalMesh_Proof_Environment_i
import opened CausalMesh_Proof_DepsAreMet_i
import opened CausalMesh_Proof_ReadReplyIsMet_i
import opened CausalMesh_Proof_Propagation_i
import opened CausalMesh_Proof_PropagationLemma2_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


lemma lemma_AllClientsAreMetPrefix(
    b:Behavior<CMState>,
    i:int
)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    requires forall j :: 0 < j <= i ==> AllReadRepliesAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    ensures forall j :: 0 < j <= i ==> AllClientsAreMet(b, j)
    decreases i
{
    if i == 0 {
        return;
    }
    
    if i == 1{
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        lemma_AllClientsAreMetForIndexOne(b, i);
        assert AllClientsAreMet(b, i);
        assert i == 1;
        assert AllClientsAreMet(b, 1);
        assert forall j :: 0 < j <= i ==> AllClientsAreMet(b, j);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_AllClientsAreMetPrefix(b, i-1);

    assume forall j :: 0 < j <= i - 1 ==> AllClientsAreMet(b, j);

    lemma_ClientsAreMetForCMNext(b, i-1);
    assert AllClientsAreMet(b, i);
    assert forall j :: 0 < j <= i ==> AllClientsAreMet(b, j);
}

lemma lemma_AllClientsAreMetForIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    ensures AllClientsAreMet(b, i)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    assert i-1 == 0;
    assert CMInit(b[i-1]);
    assert forall j :: 0 <= j < |b[i-1].clients| ==> ClientInit(b[i-1].clients[j].c, Nodes + j);
    assert forall j :: 0 <= j < |b[i-1].clients| ==> b[i-1].clients[j].c.deps == map[];
    
    assert forall j :: 0 <= j < |b[i].clients| ==> b[i-1].clients[j].c.deps == b[i].clients[j].c.deps;
    assert forall j :: 0 <= j < |b[i].clients| ==> b[i].clients[j].c.deps == map[];
    assert AllVersionsInDepsAreMetOnAllServers(b, i, map[]);
    assert forall j :: 0 <= j < |b[i].clients| ==> AllVersionsInDepsAreMetOnAllServers(b, i, b[i].clients[j].c.deps);
}

lemma lemma_ClientsAreMetForCMNext(
    b:Behavior<CMState>,
    i:int
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires CMNext(b[i], b[i+1])
    requires AllClientsAreMet(b, i)
    requires AllReadRepliesAreMet(b, i)
    requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    ensures AllClientsAreMet(b, i+1)
{
    reveal_ServersAndClientsAreValid();
    var ps := b[i];
    var ps' := b[i+1];

    if ps.clients == ps'.clients {
        forall j | 0 <= j < |b[i].clients|
            ensures AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps)
        {
            assert AllVersionsInDepsAreMetOnAllServers(b, i, b[i].clients[j].c.deps);
            assert b[i].clients[j].c.deps == b[i+1].clients[j].c.deps;
            lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i+1, b[i].clients[j].c.deps);
            assert AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps);

        }
        assert AllClientsAreMet(b, i+1);
    }
    else 
    {
        var idx :| 0 <= idx < |ps.clients| && ps.clients[idx] != ps'.clients[idx];
        var s := b[i].clients[idx].c;
        var s' := b[i+1].clients[idx].c;

        if s != s' {
            lemma_ClientsAreMetForCMNext_WithStateChange(b, i, idx);
            assert AllClientsAreMet(b, i+1);
        } else {
            forall j | 0 <= j < |b[i].clients|
                ensures AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps)
            {
                assert b[i].clients[j].c == b[i+1].clients[j].c;
                assert AllVersionsInDepsAreMetOnAllServers(b, i, b[i+1].clients[j].c.deps);
                lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i+1, b[i+1].clients[j].c.deps);
                assert AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps);
            }
            assert AllClientsAreMet(b, i+1);
        }
    }
}

lemma lemma_ClientsAreMetForCMNext_WithStateChange(
    b:Behavior<CMState>,
    i:int,
    idx:int
)
    requires IsValidBehaviorPrefix(b, i+1)
    requires 0 < i
    requires 0 <= idx < |b[i].clients|
    requires 0 <= idx < |b[i+1].clients|
    requires b[i].clients[idx].c != b[i+1].clients[idx].c
    requires CMNext(b[i], b[i+1])
    requires AllClientsAreMet(b, i)
    requires AllReadRepliesAreMet(b, i)
    // requires ServerNextDoesNotDecreaseVersions(b[i], b[i+1])
    ensures AllClientsAreMet(b, i+1)
{
    var s := b[i].clients[idx].c;
    var s' := b[i+1].clients[idx].c;
    assert s != s';

    var ios := lemma_ActionThatChangesClientIsThatClientsAction(b, i, idx);
    assert CMNextClient(b[i], b[i+1], idx, ios);
    assert LClientNext(b[i].clients[idx], b[i+1].clients[idx], ios);
    assert ClientValid(s);

    var sp := ExtractSentPacketsFromIos(ios);

    var nextActionIndex := b[i].clients[idx].nextActionIndex;

    if nextActionIndex == 0 {
        assert |ios| >= 1;
        if ios[0].LIoOpTimeoutReceive? {
            assert s == s';
            assert false;
        }
        assert ios[0].LIoOpReceive?;
        var p := ios[0].r;
        assert p.msg.Message_Read_Reply? || p.msg.Message_Write_Reply?;
        if p.msg.Message_Read_Reply? {
            assert ReceiveReadReply(s, s', p, sp);
            assert AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply);
            assert AllVersionsInDepsAreMetOnAllServers(b, i, s.deps);
            assert s'.deps == DependencyInsertOrMerge(s.deps, p.msg.key_rreply, p.msg.vc_rreply);
            lemma_DependencyInsertOrMergeIsMet(b, i, s.deps, p.msg.key_rreply, p.msg.vc_rreply);
            assert AllVersionsInDepsAreMetOnAllServers(b, i, s'.deps);
        } else {
            assert p.msg.Message_Write_Reply?;
            assert ReceiveWriteReply(s, s', p, sp);
            assert s.deps == s'.deps;
            assert AllVersionsInDepsAreMetOnAllServers(b, i, s'.deps);
        }

    } else if nextActionIndex == 1 {
        assert SendRead(s, s', sp);
        assert s.deps == s'.deps;
        assert AllVersionsInDepsAreMetOnAllServers(b, i, s'.deps);
    } else {
        assert nextActionIndex == 2;
        assert SendWrite(s, s', sp);
        assert s.deps == s'.deps;
        assert AllVersionsInDepsAreMetOnAllServers(b, i, s'.deps);
    }

    lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i+1, s'.deps);
    assert AllVersionsInDepsAreMetOnAllServers(b, i+1, s'.deps);
    assert forall j :: 0 <= j < |b[i].clients| && j != idx ==>
        b[i].clients[j].c.deps == b[i+1].clients[j].c.deps;
    
    reveal_ServersAndClientsAreValid();
    forall j | 0 <= j < |b[i].clients| && j != idx 
        ensures AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps)
    {
        assert AllVersionsInDepsAreMetOnAllServers(b, i, b[i+1].clients[j].c.deps);
        lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i+1, b[i+1].clients[j].c.deps);
        assert AllVersionsInDepsAreMetOnAllServers(b, i+1, b[i+1].clients[j].c.deps);
    }
    assert AllClientsAreMet(b, i+1);
}

// lemma lemma_DepsIsMetOnAllServersWillAlwaysMet(
//     b:Behavior<CMState>,
//     i:int,
//     deps:Dependency
// )
// {

// }

lemma lemma_DependencyInsertOrMergeIsMet(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency,
    k:Key, 
    vc:VectorClock
)
    requires IsValidBehaviorPrefix(b, i)
    requires 0 < i
    requires DependencyValid(deps)
    requires k in Keys_domain
    requires VectorClockValid(vc)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    requires AVersionIsMetOnAllServers(b, i, k, vc)
    ensures var deps' := DependencyInsertOrMerge(deps, k, vc);
            AllVersionsInDepsAreMetOnAllServers(b, i, deps')
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    if k in deps {
        var d := deps[k := VCMerge(deps[k], vc)];
        assert AllVersionsInDepsAreMetOnAllServers(b, i, d);
    }
    else {
        var d := deps[k := vc];
        assert AllVersionsInDepsAreMetOnAllServers(b, i, d);
    }
}

}