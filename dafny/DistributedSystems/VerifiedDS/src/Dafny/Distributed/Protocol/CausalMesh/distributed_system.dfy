include "cache.dfy"

module CausalMesh_DistributedSystem_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened CausalMesh_Properties_i
import opened Environment_s

datatype CMState = CMState(
    environment:LEnvironment<int, Message>,
    servers:seq<LServer>,
    clients:seq<LClient>
)

predicate {:opaque} ServerIdsAreMatch(ps:CMState)
    requires |ps.servers| == Nodes
{
    && (forall i :: 0 <= i < Nodes ==> ps.servers[i].s.id == i)
}

predicate CMComplete(ps:CMState)
{
    && |ps.servers| == Nodes
    && |ps.clients| == Clients
    && ServerIdsAreMatch(ps)
}

predicate ConstantsUnchanged(ps:CMState, ps':CMState)
{
    && |ps'.servers| == |ps.servers|
    && |ps'.clients| == |ps.clients|
}

predicate CMInit(ps:CMState)
{
    && LEnvironment_Init(ps.environment)
    && CMComplete(ps)
    && (forall i :: 0 <= i < Nodes ==> LServerInit(ps.servers[i], i))
    && (forall i :: 0 <= i < Clients ==> LClientInit(ps.clients[i], Nodes + i))
}

predicate {:opaque} ServersAndClientsAreValid(ps:CMState, ps':CMState)
{
    && (forall c :: c in ps.clients ==> ClientValid(c.c))
    && (forall c :: c in ps'.clients ==> ClientValid(c.c))
}

predicate CMNextCommon(ps:CMState, ps':CMState)
{
    && CMComplete(ps)
    && ConstantsUnchanged(ps, ps')
    && LEnvironment_Next(ps.environment, ps'.environment)
    && (forall p :: p in ps'.environment.sentPackets ==> PacketValid(p) && PacketHasCorrectSrcAndDst(p))
    && (forall s :: s in ps.servers ==> ServerValid(s.s))
    && (forall s :: s in ps'.servers ==> ServerValid(s.s))
    && ServersAndClientsAreValid(ps, ps')
}

predicate CMNextServer(ps:CMState, ps':CMState, idx:int, ios:seq<CMIo>)
{
    && CMNextCommon(ps, ps')
    && 0 <= idx < Nodes
    && LServerNext(ps.servers[idx], ps'.servers[idx], ios)
    && ps.environment.nextStep == LEnvStepHostIos(idx, ios)
    && ps'.servers == ps.servers[idx := ps'.servers[idx]]
    && ps'.clients == ps.clients
}

predicate CMNextClient(ps:CMState, ps':CMState, idx:int, ios:seq<CMIo>)
{
    && CMNextCommon(ps, ps')
    && 0 <= idx < Clients
    && LClientNext(ps.clients[idx], ps'.clients[idx], ios)
    && ps.environment.nextStep == LEnvStepHostIos(idx + Nodes, ios)
    && ps'.clients == ps.clients[idx := ps'.clients[idx]]
    && ps'.servers == ps.servers
}

predicate CMNextEnvironment(ps:CMState, ps':CMState)
{
  && CMNextCommon(ps, ps')
  && !ps.environment.nextStep.LEnvStepHostIos?
  && ps'.servers == ps.servers
  && ps'.clients == ps.clients
}

predicate CMNextOneExternal(ps:CMState, ps':CMState, eid:int, ios:seq<CMIo>)
{
  && CMNextCommon(ps, ps')
  && (eid < 0 || eid >= Nodes + Clients)
  && ps.environment.nextStep == LEnvStepHostIos(eid, ios)
  && ps'.servers == ps.servers
  && ps'.clients == ps.clients
}

predicate CMNext(ps:CMState, ps':CMState)
{
  || (exists idx, ios :: CMNextServer(ps, ps', idx, ios)) // && var sp := ExtractSentPacketsFromIos(ios); forall p :: p in sp ==> PacketValid(p))
  || (exists idx, ios :: CMNextClient(ps, ps', idx, ios)) //&& var sp := ExtractSentPacketsFromIos(ios); forall p :: p in sp ==> PacketValid(p))
  || (exists eid, ios :: CMNextOneExternal(ps, ps', eid, ios)) //&& var sp := ExtractSentPacketsFromIos(ios); forall p :: p in sp ==> PacketValid(p))
  || CMNextEnvironment(ps, ps')
}

lemma CMNextImpliesCMNextCommon(ps:CMState, ps':CMState)
    requires CMNext(ps, ps')
    ensures CMNextCommon(ps, ps')
{

}

predicate AllServersAreCausalCut(ps:CMState)
{
    forall s :: s in ps.servers ==> ServerValid(s.s) // && CausalCut(s.s.ccache)
}
}