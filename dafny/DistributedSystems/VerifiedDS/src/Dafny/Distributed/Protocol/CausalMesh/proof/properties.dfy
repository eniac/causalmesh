include "../distributed_system.dfy"
include "../../../Common/Logic/Temporal/Rules.i.dfy"
include "constants.dfy"

module CausalMesh_Proof_Properties_i {
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

predicate AVersionIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc:VectorClock
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires k in Keys_domain
    requires VectorClockValid(vc)
{
    // assert CMNextCommon(b[i-1], b[i]);
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    // assert (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]));
    assert CMNext(b[i-1], b[i]);
    forall j :: 0 <= j < |b[i].servers| ==> AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc)
}

predicate {:opaque} AllServersMetasInCacheSmallThanPVCIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    pvc:VectorClock
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    requires VectorClockValid(pvc)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    // assert (forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1]));
    assert CMNext(b[i-1], b[i]);

    forall j :: 0 <= j < |b[i].servers| ==> var s :=  b[i].servers[j].s;
            forall k :: k in s.icache ==>
                forall m :: m in s.icache[k] && (VCHappendsBefore(m.vc, pvc) || VCEq(m.vc, pvc)) ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
}

predicate AVersionIsMetOnAllServers2(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc:VectorClock
)
    requires 0 < i
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires k in Keys_domain
    requires VectorClockValid(vc)
{
    
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    reveal_AllVersionsInDepsAreMetOnAllServers();
    assert CMNext(b[i-1], b[i]);
    forall j :: 0 <= j < |b[i].servers| ==> AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc) && 
        (exists m :: m in b[i].servers[j].s.icache[k] ==> AllVersionsInDepsAreMetOnAllServers2(b, i, m.deps))
}

predicate {:opaque} AllVersionsInDepsAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // requires CMNext(b[i-1], b[i])
    requires DependencyValid(deps)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall k :: k in deps ==> AVersionIsMetOnAllServers(b, i, k, deps[k])
}

predicate AllReadDepsSmallerThanPVCRead(
    vc:VectorClock,
    deps:Dependency
)
    requires DependencyValid(deps)
    requires VectorClockValid(vc)
{
    forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
}

predicate {:opaque} AllVersionsInDepsAreMetOnAllServers2(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    // requires CMNext(b[i-1], b[i])
    requires DependencyValid(deps)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    forall k :: k in deps ==> AVersionIsMetOnAllServers(b, i, k, deps[k])
}

predicate {:opaque} AllVersionsInCCacheAreMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    ccache:CCache
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CCacheValid(ccache)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    (forall k :: k in ccache ==> AVersionIsMetOnAllServers(b, i, k, ccache[k].vc))
    // && (forall k :: k in ccache ==> AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps))
}

// predicate AllDepsInCCacheAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     ccache:CCache
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CCacheValid(ccache)
// {
//     forall k :: k in ccache ==>
//         forall kk :: kk in ccache[k].deps ==> AVersionIsMetOnAllServers(b, i, kk, ccache[k].deps[kk])
// }

// predicate {:opaque} AllDepsInICacheAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     icache:ICache
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires CMNext(b[i-1], b[i])
//     // requires forall j {:trigger CMNext(b[j], b[j+1])} :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     // requires ICacheValid(icache)
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in Keys_domain))
// {
//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     forall k :: k in icache ==>
//         forall m :: m in icache[k] ==> 
//             forall kk :: kk in m.deps ==> AVersionIsMetOnAllServers(b, i, kk, m.deps[kk])
// }

predicate AllServersAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
{
    // if i == 0 then
    //     true
    // else 
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        forall j :: 0 <= j < |b[i].servers| ==> 
            // AllDepsInICacheAreMetOnAllServers(b, i, b[i].servers[j].s.icache)
            AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[j].s.ccache)
            && (forall k :: k in b[i].servers[j].s.ccache ==> VCHappendsBefore(b[i].servers[j].s.ccache[k].vc, b[i].servers[j].s.pvc) || VCEq(b[i].servers[j].s.ccache[k].vc, b[i].servers[j].s.pvc))
}

predicate AllClientsAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
{
    reveal_ServersAndClientsAreValid();
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall j :: 0 <= j < |b[i].clients| ==> ClientValid(b[i].clients[j].c);

    forall j :: 0 <= j < |b[i].clients| ==>
        AllVersionsInDepsAreMetOnAllServers(b, i, b[i].clients[j].c.deps)
        && (forall k :: k in b[i].clients[j].c.deps ==> VCHappendsBefore(b[i].clients[j].c.deps[k], b[i].clients[j].c.pvc) || VCEq(b[i].clients[j].c.deps[k], b[i].clients[j].c.pvc))
}

predicate AllReadDepsAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall p :: p in b[i].environment.sentPackets ==> PacketValid(p);

    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_read)
        && AllReadDepsSmallerThanPVCRead(p.msg.pvc_read, p.msg.deps_read)
}

predicate /*{:opaque}*/ AllWriteDepsAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall p :: p in b[i].environment.sentPackets ==> PacketValid(p);

    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Write? ==> 
        AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_write)
}

predicate AllReadRepliesAreMet(
    b:Behavior<CMState>,
    i:int
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert forall p :: p in b[i].environment.sentPackets ==> PacketValid(p);

    forall p :: p in b[i].environment.sentPackets && p.msg.Message_Read_Reply? ==> 
        // AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.deps_rreply) && 
        AVersionIsMetOnAllServers(b, i, p.msg.key_rreply, p.msg.vc_rreply)
        && (VCHappendsBefore(p.msg.vc_rreply, p.msg.pvc_rreply) || VCEq(p.msg.vc_rreply, p.msg.pvc_rreply))
}

predicate CCacheDoesNotDecrease(
    c1:CCache,
    c2:CCache
)
    requires CCacheValid(c1)
    requires CCacheValid(c2)
{
    && (forall k :: k in c1 ==> k in c2 && (VCHappendsBefore(c1[k].vc, c2[k].vc) || VCEq(c1[k].vc, c2[k].vc)))
    && (forall k :: k in c1 ==> 
            forall kk :: kk in c1[k].deps ==> kk in c2[k].deps && (VCHappendsBefore(c1[k].deps[kk], c2[k].deps[kk]) || VCEq(c1[k].deps[kk], c2[k].deps[kk])) )
}

predicate ICacheDoesNotDecrease(
    c1:ICache,
    c2:ICache
)
    requires ICacheValid(c1)
    requires ICacheValid(c2)
{
    forall k :: k in c1 ==> k in c2 && 
        forall m :: m in c1[k] ==> m in c2[k]
}

predicate ServerNextDoesNotDecreaseVersions(
    ps:CMState,
    ps':CMState
)
    requires CMNext(ps, ps')
{
    forall i :: 0 <= i < |ps.servers| ==> 
        CCacheDoesNotDecrease(ps.servers[i].s.ccache, ps'.servers[i].s.ccache) 
        && ICacheDoesNotDecrease(ps.servers[i].s.icache, ps'.servers[i].s.icache)
}


}