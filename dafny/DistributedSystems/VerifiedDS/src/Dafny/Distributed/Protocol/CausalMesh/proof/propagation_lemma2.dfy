include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "propagation_lemma.dfy"
include "always_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_PropagationLemma2_i {
import opened CausalMesh_Cache_i
import opened CausalMesh_Message_i
import opened CausalMesh_Types_i
import opened Environment_s
import opened CausalMesh_DistributedSystem_i
import opened CausalMesh_Properties_i
import opened CausalMesh_Proof_Actions_i
import opened Temporal__Temporal_s
import opened CausalMesh_proof_Assumptions_i
import opened CausalMesh_Proof_Constants_i
import opened CausalMesh_Proof_PropagationLemma_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
import opened CausalMesh_Proof_AllwaysMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma lemma_Propagation2AtIndexOne(
    b:Behavior<CMState>,
    i:int
)
    requires i == 1
    requires IsValidBehaviorPrefix(b, i)
    // requires CMNext(b[i-1], b[i])
    ensures !exists pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Propagation?
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    assert CMNext(b[i-1], b[i]);
}

lemma lemma_Propagation2(
    b:Behavior<CMState>,
    i:int,
    p:Packet
    // nodes:set<int>
)
returns (nodes:seq<int>)
    requires 0 <= i 
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i], b[i+1])
    requires CMInit(b[0])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires p.msg.Message_Propagation?
    requires p in b[i].environment.sentPackets
    // requires forall n :: n in nodes ==> 0 <= n < Nodes
    requires PacketValid(p)
    requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    ensures |nodes| > 1
    ensures nodes[0] == p.msg.start
    ensures nodes[|nodes|-2] == p.src
    ensures nodes[|nodes|-1] == p.dst
    ensures forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    ensures forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
    ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
    // ensures forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps)
{
    if i == 0 {
        return;
    }

    if i == 1 {
        lemma_Propagation2AtIndexOne(b, i);
        assume !exists pp :: pp in b[i].environment.sentPackets && pp.msg.Message_Propagation?;
        assert false;
        return;
    }


    if p in b[i-1].environment.sentPackets{
        lemma_BehaviorValidImpliesOneStepValid(b, i);
        nodes := lemma_Propagation2(b, i-1, p);
        assert CMNext(b[i-1], b[i]);
        assume forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
        // assume forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.meta.deps);
        lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
        return;
    }

    lemma_ConstantsAllConsistent(b, i-1);
    lemma_ConstantsAllConsistent(b, i);

    lemma_BehaviorValidImpliesOneStepValid(b, i);
    // assert i-1 > 0;
    // assume AllWriteDepsAreMet(b, i-1);

    var ps := b[i-1];
    var ps' := b[i];

    var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p);
    // assert idx in nodes;
    assert ios[0].r.dst == idx;

    if ios[0].r.msg.Message_Propagation? {
        // assert 0 < i;
        // assert IsValidBehaviorPrefix(b, i);
        // assert CMNext(b[i-1], b[i]);
        // assert 0 <= idx < Nodes;
        // assert |ios| > 1;
        // assert ios[0].r.msg.Message_Propagation?;
        // assert p.msg.key == ios[0].r.msg.key;
        // assert p.msg.meta.deps == ios[0].r.msg.meta.deps;
        // var sp := ExtractSentPacketsFromIos(ios);
        // assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, sp);
        // assert sp[0].msg.Message_Propagation?;
        // assert sp[0].msg.meta.vc == p.msg.meta.vc;
        // assert sp[0].msg.meta.deps == p.msg.meta.deps;
        // assert ios[0].r.msg.start != b[i-1].servers[idx].s.next;
        lemma_PropagationNotTail(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
        assume AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
        assert DependencyValid(p.msg.meta.deps);
        // assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);
        var rp := ios[0].r;

        assert NodesAreNext(p.src, p.dst);

        assert rp.msg.Message_Propagation?;
        assert rp in b[i-1].environment.sentPackets;
        assert PacketValid(rp);
        var prev_nodes := lemma_Propagation2(b, i-1, rp);
        
        assert |prev_nodes| > 0;
        assume prev_nodes[0] == p.msg.start;
        assume prev_nodes[|prev_nodes|-2] == rp.src;
        assume prev_nodes[|prev_nodes|-1] == rp.dst;
        // lemma_ReceivePktDstIsMe(rp.dst, idx);
        assume rp.dst == idx;
        assert prev_nodes[|prev_nodes|-1] == p.src;
        assume forall j :: 0 <= j < |prev_nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, rp.msg.key, rp.msg.meta.vc);
        // assume forall j :: 0 <= j < |prev_nodes| - 1 ==> DepsIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, p.msg.meta.deps);

        assert forall j :: 0 <= j < |prev_nodes| ==> 0 <= prev_nodes[j] < Nodes;
        assert forall j :: 0 <= j < |prev_nodes| - 1 ==> NodesAreNext(prev_nodes[j], prev_nodes[j+1]);

        nodes := prev_nodes + [p.dst];
        assert nodes[0] == p.msg.start;
        assert nodes[|nodes|-2] == p.src;
        assert nodes[|nodes|-1] == p.dst;
        // assert |nodes| > 1;
        assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
        
        assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
        // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
        // assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    } else {
        assert i > 0;
        assert IsValidBehaviorPrefix(b, i);
        assert CMNext(b[i-1], b[i]);
        assert 0 <= idx < Nodes;
        assert |ios| > 1;
        assert ios[0].LIoOpReceive?;
        assert ios[0].r.msg.Message_Write?;
        assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
        var sp := ExtractSentPacketsFromIos(ios);

        var p_write := ios[0].r;
        assert p_write.msg.Message_Write?;
        assert p_write in b[i-1].environment.sentPackets;

        assert sp[|sp|-1].msg.Message_Propagation?;
        assert sp[|sp|-1].msg.meta.vc == p.msg.meta.vc;
        //         && sp[|sp|-1].msg.meta.deps == p.msg.meta.deps;

        assert i > 1;
        assert AllWriteDepsAreMet(b, i-1);

        // lemma_DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write);
        // assert AllWriteDepsAreMet(b, i-1);
        assert AllVersionsInDepsAreMetOnAllServers(b, i-1, p_write.msg.deps_write);
        reveal_AllVersionsInDepsAreMetOnAllServers();
        reveal_DepsIsMet();
        // assert DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write); // this is ture, but without the previous lemma, will timeout.
        lemma_PropagationAtHead(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
        assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
        // assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

        
        // assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p_write.msg.deps_write);
        // lemma_DepsInPropagationIsInWriteDepsOrLocals(b, i, idx, ios);
        // assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

        assert idx == p.msg.start;
        nodes := [idx] + [p.dst];
        var n := |nodes|;
        assert n == 2;
        assert nodes[0] == p.msg.start;
        assert p.src in nodes;
        assert nodes[|nodes|-2] == p.src;
        assert nodes[|nodes|-1] == p.dst;
        assert NodesAreNext(p.src, p.dst);
        assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);

        assert AVersionOfAKeyIsMet(b[i].servers[p.src].s.icache, b[i].servers[p.src].s.ccache, p.msg.key, p.msg.meta.vc);
        assert forall j :: 0 <= j < |nodes| - 1 ==> 
            AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
            // && DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
    }
}


// lemma lemma_Propagation2(
//     b:Behavior<CMState>,
//     i:int,
//     p:Packet
//     // nodes:set<int>
// )
// returns (nodes:seq<int>)
//     requires 0 <= i 
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i], b[i+1])
//     requires CMInit(b[0])
//     requires |b[i].servers| == Nodes
//     requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
//     requires p.msg.Message_Propagation?
//     requires p in b[i].environment.sentPackets
//     // requires forall n :: n in nodes ==> 0 <= n < Nodes
//     requires PacketValid(p)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     ensures |nodes| > 1
//     ensures nodes[0] == p.msg.start
//     ensures nodes[|nodes|-2] == p.src
//     ensures nodes[|nodes|-1] == p.dst
//     ensures forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
//     ensures forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
//     ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
//     ensures forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps)
// {
//     if i == 0 {
//         return;
//     }

//     if p in b[i-1].environment.sentPackets{
//         lemma_BehaviorValidImpliesOneStepValid(b, i);
//         nodes := lemma_Propagation2(b, i-1, p);
//         assert CMNext(b[i-1], b[i]);
//         assume forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//         assume forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.meta.deps);
//         lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
//         return;
//     }

//     lemma_ConstantsAllConsistent(b, i-1);
//     lemma_ConstantsAllConsistent(b, i);

//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     assert AllWriteDepsAreMet(b, i-1);

//     var ps := b[i-1];
//     var ps' := b[i];

//     var idx, ios := lemma_ActionThatSendsPropagationIsReceivePropogateOrReceiveWrite(b[i-1], b[i], p);
//     // assert idx in nodes;

//     if ios[0].r.msg.Message_Propagation? {
//         // assert 0 < i;
//         // assert IsValidBehaviorPrefix(b, i);
//         // assert CMNext(b[i-1], b[i]);
//         // assert 0 <= idx < Nodes;
//         // assert |ios| > 1;
//         // assert ios[0].r.msg.Message_Propagation?;
//         // assert p.msg.key == ios[0].r.msg.key;
//         // assert p.msg.meta.deps == ios[0].r.msg.meta.deps;
//         // var sp := ExtractSentPacketsFromIos(ios);
//         // assert ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, sp);
//         // assert sp[0].msg.Message_Propagation?;
//         // assert sp[0].msg.meta.vc == p.msg.meta.vc;
//         // assert sp[0].msg.meta.deps == p.msg.meta.deps;
//         // assert ios[0].r.msg.start != b[i-1].servers[idx].s.next;
//         lemma_PropagationNotTail(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
//         assume AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
//         assert DependencyValid(p.msg.meta.deps);
//         assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);
//         var rp := ios[0].r;

//         assert NodesAreNext(p.src, p.dst);

//         assert rp.msg.Message_Propagation?;
//         assert rp in b[i-1].environment.sentPackets;
//         assert PacketValid(rp);
//         var prev_nodes := lemma_Propagation2(b, i-1, rp);
        
//         assert |prev_nodes| > 0;
//         assume prev_nodes[0] == p.msg.start;
//         assume prev_nodes[|prev_nodes|-2] == rp.src;
//         assume prev_nodes[|prev_nodes|-1] == rp.dst;
//         lemma_ReceivePktDstIsMe(rp.dst, idx);
//         assume rp.dst == idx;
//         assert prev_nodes[|prev_nodes|-1] == p.src;
//         assume forall j :: 0 <= j < |prev_nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, rp.msg.key, rp.msg.meta.vc);
//         assume forall j :: 0 <= j < |prev_nodes| - 1 ==> DepsIsMet(b[i-1].servers[prev_nodes[j]].s.icache, b[i-1].servers[prev_nodes[j]].s.ccache, p.msg.meta.deps);

//         assert forall j :: 0 <= j < |prev_nodes| ==> 0 <= prev_nodes[j] < Nodes;
//         assert forall j :: 0 <= j < |prev_nodes| - 1 ==> NodesAreNext(prev_nodes[j], prev_nodes[j+1]);

//         nodes := prev_nodes + [p.dst];
//         assert nodes[0] == p.msg.start;
//         assert nodes[|nodes|-2] == p.src;
//         assert nodes[|nodes|-1] == p.dst;
//         // assert |nodes| > 1;
//         assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
        
//         assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
//         // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
//     } else {
//         assert i > 0;
//         assert IsValidBehaviorPrefix(b, i);
//         assert CMNext(b[i-1], b[i]);
//         assert 0 <= idx < Nodes;
//         assert |ios| > 1;
//         assert ios[0].LIoOpReceive?;
//         assert ios[0].r.msg.Message_Write?;
//         assert ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios));
//         var sp := ExtractSentPacketsFromIos(ios);

//         var p_write := ios[0].r;
//         assert p_write.msg.Message_Write?;
//         assert p_write in b[i-1].environment.sentPackets;

//         assert sp[|sp|-1].msg.Message_Propagation?;
//         assert sp[|sp|-1].msg.meta.vc == p.msg.meta.vc;
//         //         && sp[|sp|-1].msg.meta.deps == p.msg.meta.deps;

//         lemma_DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write);
//         // assert AllWriteDepsAreMet(b, i-1);
//         // // reveal_AllVersionsInDepsAreMetOnAllServers();
//         // // reveal_DepsIsMet();
//         assert DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, p_write.msg.deps_write); // this is ture, but without the previous lemma, will timeout.
//         lemma_PropagationAtHead(b, i, idx, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, ios);
//         assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.key, p.msg.meta.vc);
//         assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

        
//         // assume DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p_write.msg.deps_write);
//         // lemma_DepsInPropagationIsInWriteDepsOrLocals(b, i, idx, ios);
//         // assert DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps);

//         assert idx == p.msg.start;
//         nodes := [idx] + [p.dst];
//         var n := |nodes|;
//         assert n == 2;
//         assert nodes[0] == p.msg.start;
//         assert p.src in nodes;
//         assert nodes[|nodes|-2] == p.src;
//         assert nodes[|nodes|-1] == p.dst;
//         assert NodesAreNext(p.src, p.dst);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);

//         assert AVersionOfAKeyIsMet(b[i].servers[p.src].s.icache, b[i].servers[p.src].s.ccache, p.msg.key, p.msg.meta.vc);
//         assert forall j :: 0 <= j < |nodes| - 1 ==> 
//             AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc)
//             && DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
//     }
// }

lemma lemma_AVersionOfAKeyIsMetIsTransitive(
    b:Behavior<CMState>,
    i:int,
    key:Key,
    vc:VectorClock,
    deps:Dependency,
    nodes:seq<int>
)
    requires 1 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires key in Keys_domain
    requires VectorClockValid(vc)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    requires forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, key, vc)
    // requires forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, deps)
    ensures forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
    // ensures forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
{
    forall j | 0 <= j < |nodes| - 1
        ensures AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc)
        // ensures DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    {
        assert AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, key, vc);
        lemma_AVersionIsMetWillAlwaysMet(
            b[i-1].servers[nodes[j]].s.icache,
            b[i].servers[nodes[j]].s.icache,
            b[i-1].servers[nodes[j]].s.ccache,
            b[i].servers[nodes[j]].s.ccache,
            key, vc
        );
        assert AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, key, vc);

        // reveal_DepsIsMet();
        // assert DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, deps);
        // lemma_DepsIsMetWillAlwaysMet(b, i, nodes[j], deps);
        // assert DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps);
    }
    // var j :| 0 <= j < |nodes| - 1;
    // var s := b[i-1].servers[nodes[j]].s;
    // var s' := b[i].servers[nodes[j]].s;
    // assume forall k :: k in s.ccache ==> k in s'.ccache && (VCHappendsBefore(s.ccache[k].vc, s'.ccache[k].vc) || VCEq(s.ccache[k].vc, s'.ccache[k].vc));
}


lemma lemma_PropagationNotTail(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    key:Key,
    vc:VectorClock,
    deps:Dependency,
    ios:seq<CMIo>
    // ,
    // nodes:set<int>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires ios[0].r.msg.Message_Propagation?
    requires PacketValid(ios[0].r)
    requires ios[0].r.msg.start != b[i-1].servers[idx].s.next || ios[0].r.msg.round != 2
    // requires forall n :: n in nodes ==> 1 <= n < Nodes
    requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios)) 
    requires key == ios[0].r.msg.key
    requires deps == ios[0].r.msg.meta.deps
    requires var sp := ExtractSentPacketsFromIos(ios);
            sp[0].msg.Message_Propagation? && sp[0].msg.meta.vc == vc && sp[0].msg.meta.deps == deps
    ensures AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, key, vc)
    // ensures DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps)
    // ensures forall k :: 0 < k <= n ==> 
    //          var node := CalNode(ios[0].r.msg.start, k);
    //          AVersionOfAKeyIsMet(b[i].servers[node].s.icache, b[i].servers[node].s.ccache, ios[0].r.msg.key, ios[0].r.msg.meta.vc)
{
    reveal_DepsIsMet();
    var p := ios[0].r;
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;

    // lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(s.icache, s.ccache, p.msg.meta.deps);

    var sp := ExtractSentPacketsFromIos(ios);
    var p_pro := sp[0];
    assert p_pro.msg.Message_Propagation?;

    var k := p.msg.key;
    
    var meta := p.msg.meta;
    
    var new_icache := AddMetaToICache(s.icache, p.msg.meta);
    assert meta in s'.icache[k];

    assert AVersionOfAKeyIsMet(s'.icache, s'.ccache, p.msg.key, meta.vc);
    // assert DepsIsMet(s'.icache, s'.ccache, p.msg.meta.deps);
}

// lemma {:axiom} lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(icache:ICache, ccache:CCache, deps:Dependency)
//     requires ICacheValid(icache)
//     requires CCacheValid(ccache)
//     requires DependencyValid(deps)
//     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
//     ensures DepsIsMet(icache, ccache, deps)

// lemma {:axiom} lemma_PropagationToTheTailImpliesTheDepsAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     deps:Dependency
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires DependencyValid(deps)
//     ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)


// lemma {:axiom} lemma_ReceivePktDstIsMe(dst:int, me:int)
//     ensures dst == me
}