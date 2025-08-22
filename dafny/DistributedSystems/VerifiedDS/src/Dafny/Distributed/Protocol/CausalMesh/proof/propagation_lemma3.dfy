include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
// include "propagation_lemma.dfy"
include "propagation_lemma2.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_PropagationLemma3_i {
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
// import opened CausalMesh_Proof_PropagationLemma_i
import opened CausalMesh_Proof_PropagationLemma2_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

// lemma lemma_PropagationAtTail2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     p:Packet,
//     ios:seq<CMIo>
// )
//     requires 0 < i 
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires 0 <= idx < Nodes
//     requires |ios| > 0
//     requires ios[0].LIoOpReceive?
//     requires p.msg.Message_Propagation?
//     requires p in b[i-1].environment.sentPackets
//     requires p.dst == idx
//     requires idx == b[i-1].servers[idx].s.id
//     requires ios[0].r == p
//     requires PacketValid(p)
//     requires p.msg.start == b[i-1].servers[idx].s.next
//     requires p.msg.round == 2
//     requires ReceivePropagate(b[i-1].servers[idx].s, b[i].servers[idx].s, p, ExtractSentPacketsFromIos(ios))
//     // ensures AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.meta.deps)
// {
//     var p := ios[0].r;
//     var s := b[i-1].servers[idx].s;
//     var s' := b[i].servers[idx].s;

//     assert p.msg.start == s.next;

//     assert 0 <= i - 1;
//     assert IsValidBehaviorPrefix(b, i-1);
//     // lemma_BehaviorValidImpliesAllStepsValid(b, i);
//     // assert forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1]);
//     // assert CMNext(b[i-2], b[i-1]);
//     assert CMNext(b[i-1], b[i]);
//     // assert CMNextCommon(b[i-1], b[i]);
//     assert forall j :: 0 <= j < Nodes ==> ServerValid(b[i-1].servers[j].s);
//     assert p.msg.Message_Propagation?;
//     assert CMInit(b[0]);
//     assert |b[i-1].servers| == Nodes;
//     assert p in b[i-1].environment.sentPackets;
//     assert PacketValid(p);

//     assert p.dst == idx;
//     assert idx == s.id;

//     var nodes := lemma_Propagation2(b, i-1, p);
//     assert |nodes| > 1;
//     assert nodes[0] == p.msg.start;
//     assert nodes[|nodes|-2] == p.src;
//     assert nodes[|nodes|-1] == p.dst;
//     assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
//     assert forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1]);
//     assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//     // assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i-1].servers[nodes[j]].s.icache, b[i-1].servers[nodes[j]].s.ccache, p.msg.meta.deps);

//     lemma_ServerNextSatisfyNodesAreNext(s.id, s.next);
//     assert NodesAreNext(s.id, p.msg.start);
//     assert p.dst == s.id;
//     lemma_NodesFormACircle(p.msg.start, p.dst, nodes);
//     // assert forall j :: 0 <= j < Nodes ==> j in nodes;
//     assert NodesAreComplete(nodes);

//     var new_deps := p.msg.meta.deps;
//     var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, new_deps);
    

//     var new_ccache' := InsertIntoCCache(new_ccache, p.msg.meta);
//     var new_icache' := AddMetaToICache(new_icache, p.msg.meta);
//     // reveal_DepsIsMet();
//     lemma_AddMetaToCacheImpliesMetaIsMetInNewCache(new_icache, new_ccache, p.msg.meta);
//     // assert DepsIsMet(new_icache', new_ccache', p.msg.meta.deps);

//     assert VCHappendsBefore(p.msg.meta.vc, new_ccache'[p.msg.key].vc) || VCEq(p.msg.meta.vc, new_ccache'[p.msg.key].vc);
//     // reveal_DepsIsMet();
//     // lemma_DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, p.msg.meta.deps); // this could be proved, but may timeout
    
//     lemma_AVersionOfAKeyIsMetIsTransitive(b, i, p.msg.key, p.msg.meta.vc, p.msg.meta.deps, nodes);
//     // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//     // assert forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.meta.deps);
//     // assert forall j :: 0 <= j < |nodes| - 1 ==> AVersionOfAKeyIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, p.msg.key, p.msg.meta.vc);
//     assert nodes[|nodes|-1] == idx;
    
//     // lemma_DepsIsMetForNodes(b, i, nodes, p.msg.meta.deps);

//     assert |b[i].servers| == Nodes;
//     assert forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s);
//     assert |nodes| > 1;
//     assert forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes;
//     // lemma_Nodes(nodes);
//     // assert forall j :: 0 <= j < Nodes ==> j in nodes;
//     // lemma_DepsIsMetForAllNodes(b, i, nodes, p.msg.meta.deps);
//     // assert AllVersionsInDepsAreMetOnAllServers(b, i, p.msg.meta.deps);
// }

predicate {:opaque} NodesAreComplete(
    nodes:seq<int>
)
{
    forall j :: 0 <= j < Nodes ==> j in nodes
}

// lemma lemma_AddMetaToCacheImpliesMetaIsMetInNewCache(
//     icache:ICache,
//     ccache:CCache,
//     meta:Meta
// )
//     requires ICacheValid(icache)
//     requires CCacheValid(ccache)
//     requires MetaValid(meta)
//     requires forall k :: k in meta.deps ==> k in icache
//     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
//     ensures var icache' := AddMetaToICache(icache, meta);
//             var ccache' := InsertIntoCCache(ccache, meta);
//             DepsIsMet(icache', ccache', meta.deps)
// {
//     reveal_DepsIsMet();
//     lemma_ReceiveAPropagationImpliesTheDepsAreAlreadyMet(icache, ccache, meta.deps);

//     var icache' := AddMetaToICache(icache, meta);
//     var ccache' := InsertIntoCCache(ccache, meta);
//     assert meta in icache'[meta.key];
//     assert VCHappendsBefore(meta.vc, ccache'[meta.key].vc) || VCEq(meta.vc, ccache'[meta.key].vc);
//     // assert forall k :: k in meta.deps ==> VCHappendsBefore(meta.deps[k], ccache'[k].vc) || VCEq(meta.deps[k], ccache'[k].vc);
//     assert DepsIsMet(icache', ccache', meta.deps);
//     // forall k | k in meta.deps 
//     // {
//     //     var vc := meta.deps[k];
//     //     var m := FoldMetaSet2(ccache'[k], icache'[k]);
//     //     assert VCEq(vc, m.vc) || VCHappendsBefore(vc, m.vc);
//     // }
// }


lemma lemma_ServerNextSatisfyNodesAreNext(id:int, next:int)
    requires 0 <= id < Nodes
    requires next == Circle(id, Nodes)
    ensures NodesAreNext(id, next)
{

}

lemma lemma_NodesFormACircle(start:int, end:int, nodes:seq<int>)
    requires 0 <= start < Nodes
    requires 0 <= end < Nodes
    requires |nodes| > 1
    requires nodes[0] == start
    requires nodes[|nodes|-1] == end
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes
    requires forall j :: 0 <= j < |nodes| - 1 ==> NodesAreNext(nodes[j], nodes[j+1])
    requires NodesAreNext(end, start)
    // ensures forall j :: 0 <= j < Nodes ==> j in nodes
    ensures NodesAreComplete(nodes)
{
    reveal_NodesAreComplete();
    // assert |nodes| <= Nodes;
    if |nodes| < Nodes {
        // Contradiction: 
        // If length < Nodes, then when you walk NodesAreNext steps from start, you can't return to start.
        // Because NodesAreNext always increments index by 1 mod Nodes.
        var last := nodes[|nodes|-1];
        var expectedNext :=
            if last == Nodes-1 then 0 else last+1;
        assert expectedNext != start;
        assert NodesAreNext(last, start);
        // Contradiction
        assert false;
    }

    forall j | 0 <= j < Nodes
        ensures j in nodes
    {
        // Because the sequence has length Nodes, and starts at `start` and advances one by one modulo Nodes,
        // each position must appear exactly once.
        var offset := (j - start + Nodes) % Nodes;
        assert offset < Nodes;
        assert offset < |nodes|;
        var at := (start + offset) % Nodes;
        // At position offset in the sequence, expect index `at`
        if offset == 0 {
            assert nodes[offset] == start;
        } else {
            // Inductively: nodes[offset] = (start + offset) mod Nodes
            // Let's prove this by induction
            var k := offset;
            // base case
            if k == 0 {
                assert nodes[0] == start;
            } else {
                // Inductive hypothesis: nodes[k-1] == (start + k -1) % Nodes
                // Prove nodes[k] == (start + k) % Nodes
                var pred := nodes[k-1];
                assert pred == (start + k -1) % Nodes;
                // nodes[k] is the next node
                assert NodesAreNext(pred, nodes[k]);
                if pred == Nodes-1 {
                    assert nodes[k] == 0;
                    assert (start + k) % Nodes == 0;
                } else {
                    assert nodes[k] == pred +1;
                    assert (start + k) % Nodes == (pred +1) % Nodes;
                }
            }
            // From the above, nodes[k] == (start+k)%Nodes
            assert nodes[k] == (start+k)%Nodes;
        }
        // Finally, since j == (start+offset)%Nodes
        assert at == j;
        assert nodes[offset] == j;
    }
    assert forall j :: 0 <= j < Nodes ==> j in nodes;
}

lemma lemma_ReverseEdgePathExists(start:int, end:int, nodes:seq<int>, i:int, j:int)
returns (x:int, y:int)
    requires 0 <= start < Nodes
    requires 0 <= end < Nodes
    requires 0 <= i < Nodes
    requires 0 <= j < Nodes
    requires |nodes| > Nodes
    requires nodes[0] == start
    requires nodes[|nodes|-1] == end
    requires forall k :: 0 <= k < |nodes| ==> 0 <= nodes[k] < Nodes
    requires forall k :: 0 <= k < |nodes|-1 ==> NodesAreNext(nodes[k], nodes[k+1])
    requires NodesAreNext(end, start)
    requires NodesAreNext(i, j)
    ensures 0 <= x < |nodes|
    ensures 0 <= y < |nodes|
    ensures nodes[x] == j
    ensures nodes[y] == i
    ensures x < y

// lemma lemma_ReverseEdgePathExists2(start:int, end:int, nodes:seq<int>, i:int, j:int)
//   returns (x:int, y:int)
//   requires 0 <= start < Nodes
//   requires 0 <= end < Nodes
//   requires 0 <= i < Nodes
//   requires 0 <= j < Nodes
//   requires |nodes| > Nodes
//   requires nodes[0] == start
//   requires nodes[|nodes|-1] == end
//   requires forall k :: 0 <= k < |nodes| ==> 0 <= nodes[k] < Nodes
//   requires forall k :: 0 <= k < |nodes|-1 ==> NodesAreNext(nodes[k], nodes[k+1])
//   requires NodesAreNext(end, start)
//   requires NodesAreNext(i, j)
//   ensures 0 <= x < |nodes|
//   ensures 0 <= y < |nodes|
//   ensures nodes[x] == j
//   ensures nodes[y] == i
//   ensures x < y
// {
//   // Construct full cycle path by adding start to end
//   var fullPath := nodes + [start];
//   assert |fullPath| == |nodes| + 1;
//   assert forall k :: 0 <= k < |fullPath| - 1 ==> NodesAreNext(fullPath[k], fullPath[k+1]);
//   assert fullPath[|fullPath|-1] == start;

//   // Now find some occurrence of (i, j) in fullPath
//   var found := false;
//   var p := 0;
//   while p < |fullPath| - 1
//     invariant 0 <= p <= |fullPath|-1
//     decreases |fullPath| - p
//   {
//     if fullPath[p] == i && fullPath[p+1] == j {
//       found := true;
//       break;
//     }
//     p := p + 1;
//   }
//   assume found;

//   // Because the cycle has more than Nodes elements, some node must appear more than once
// //   var counts := map k:int {:trigger fullPath[k]} | 0 <= k < |fullPath| :: fullPath[k];
//   assert |fullPath| > Nodes;
//   assume exists k1, k2 :: 0 <= k1 < k2 < |fullPath| && fullPath[k1] == fullPath[k2];

//   // Now scan fullPath again to find a later occurrence of (j, i)
//   found := false;
//   var x0 := 0;
//   var y0 := 0;
//   var q := p + 1;
//   while q < |fullPath| - 1
//     invariant p+1 <= q <= |fullPath|-1
//     decreases |fullPath| - q
//   {
//     if fullPath[q] == j && fullPath[q+1] == i {
//       x0 := q;
//       y0 := q + 1;
//       found := true;
//       break;
//     }
//     q := q + 1;
//   }
//   assert found;

//   // Now we set x := x0, y := y0
//   x := x0;
//   y := y0;

//   // Prove postconditions
//   assert 0 <= x < |fullPath| - 1;
//   assert x < y;
//   assert fullPath[x] == j && fullPath[y] == i;

//   // Since fullPath = nodes + [start], x must be < |nodes|
//   assert x < |nodes|;
//   assert y < |nodes| + 1;
//   if y < |nodes| {
//     assert nodes[x] == j && nodes[y] == i;
//   } else {
//     // y == |nodes|, then nodes[y] doesn't exist, but since fullPath[y] == i and fullPath[y] = start,
//     // then i == start
//     assert i == start;
//     assert y == |nodes|;
//     // then nodes[x] == j still holds, and we can just output (x, y)
//   }
// }


// method lemma_ReverseEdgePathExists2(start: int, end: int, nodes: seq<int>, i: int, j: int)
//     returns (x: int, y: int)
//     requires 0 <= start < Nodes
//     requires 0 <= end < Nodes
//     requires 0 <= i < Nodes
//     requires 0 <= j < Nodes
//     requires |nodes| > Nodes
//     requires nodes[0] == start
//     requires nodes[|nodes|-1] == end
//     requires forall k :: 0 <= k < |nodes| ==> 0 <= nodes[k] < Nodes
//     requires forall k :: 0 <= k < |nodes|-1 ==> NodesAreNext(nodes[k], nodes[k+1])
//     requires NodesAreNext(end, start)
//     requires NodesAreNext(i, j)
//     ensures 0 <= x < |nodes|
//     ensures 0 <= y < |nodes|
//     ensures nodes[x] == j
//     ensures nodes[y] == i
//     ensures x < y
// {
//     // Assume Nodes is a constant defined elsewhere
//     // Initialize x to find the first occurrence of j
//     x := -1;
//     var k := 0;
//     while k < |nodes|
//         invariant 0 <= k <= |nodes|
//         invariant x == -1 ==> (forall m :: 0 <= m < k ==> nodes[m] != j)
//         invariant x >= 0 ==> (0 <= x < k && nodes[x] == j && (forall m :: 0 <= m < x ==> nodes[m] != j))
//     {
//         if nodes[k] == j {
//             if x == -1 {
//                 x := k;
//             }
//         }
//         k := k + 1;
//     }

//     // Assert that j was found
//     assume x >= 0 && x < |nodes| && nodes[x] == j;

//     // Find the first occurrence of i after x
//     y := -1;
//     k := x + 1;
//     while k < |nodes|
//         invariant x < k <= |nodes|
//         invariant y == -1 ==> (forall m :: x < m < k ==> nodes[m] != i)
//         invariant y >= 0 ==> (x < y < k && nodes[y] == i)
//     {
//         if nodes[k] == i {
//             if y == -1 {
//                 y := k;
//             }
//         }
//         k := k + 1;
//     }

//     // Assert that i was found after x
//     assume y >= 0;
//     assert x < y < |nodes| && nodes[y] == i;
// }

// lemma lemma_ReverseEdgePathExists(start:int, end:int, nodes:seq<int>, i:int, j:int)
//     requires 0 <= start < Nodes
//     requires 0 <= end < Nodes
//     requires |nodes| > Nodes
//     requires nodes[0] == start
//     requires nodes[|nodes|-1] == end
//     requires forall k :: 0 <= k < |nodes| ==> 0 <= nodes[k] < Nodes
//     requires forall k :: 0 <= k < |nodes|-1 ==> NodesAreNext(nodes[k], nodes[k+1])
//     requires NodesAreNext(end, start)
//     requires NodesAreNext(i, j)
//     ensures exists p:int, q:int :: 
//         0 <= p <= q < |nodes| &&
//         nodes[p] == j && nodes[q] == i &&
//         forall r :: p <= r < q ==> NodesAreNext(nodes[r], nodes[r+1])
// {
//     // Since |nodes| > Nodes and all nodes are in [0, Nodes), by pigeonhole principle
//     // at least one node appears multiple times. But stronger: the ring is traversed more than once.
//     // So i and j must appear at least once, and since it wraps (end -> start), we can treat this as circular.

//     // Step 1: Find positions where j occurs
//     var j_indices : set<int> := set k | 0 <= k < |nodes| && nodes[k] == j;
//     var i_indices : set<int> := set k | 0 <= k < |nodes| && nodes[k] == i;

//     // We know j and i both must appear at least once since the ring is complete
//     assert |j_indices| > 0;
//     assert |i_indices| > 0;

//     // Try all pairs (p, q) where p is j, q is i, and p < q
//     // There must be one such pair because the sequence is longer than one ring
//     // and eventually cycles back

//     var found := false;
//     var p:int, q:int;
//     forall x:int, y:int | x in j_indices && y in i_indices && x < y
//         ensures found || (found && p == x && q == y &&
//                           forall r :: p <= r < q ==> NodesAreNext(nodes[r], nodes[r+1]))
//     {
//         if (!found) {
//             var ok := true;
//             forall r | x <= r < y
//                 ensures ok ==> NodesAreNext(nodes[r], nodes[r+1])
//             {
//                 if (!NodesAreNext(nodes[r], nodes[r+1])) {
//                     ok := false;
//                 }
//             }
//             if ok {
//                 p := x;
//                 q := y;
//                 found := true;
//             }
//         }
//     }
//     if found {
//         assert exists p:int, q:int ::
//             0 <= p <= q < |nodes| &&
//             nodes[p] == j && nodes[q] == i &&
//             forall r :: p <= r < q ==> NodesAreNext(nodes[r], nodes[r+1]);
//     } else {
//         // This cannot happen since the circle is walked more than once.
//         // We would eventually traverse j then i in order.
//         assert false;
//     }
// }




lemma lemma_DepsIsMetForNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    deps:Dependency
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| - 1 ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    requires DepsIsMet(b[i].servers[nodes[|nodes|-1]].s.icache, b[i].servers[nodes[|nodes|-1]].s.ccache, deps)
    ensures forall j :: 0 <= j < |nodes| ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
{

}

// this one can be proved, but the last requires is not passed at the end of lemma_PropagationAtTail
// but this requires is ture, beacuse it can pass at the middle of lemma_PropagationAtTail
lemma lemma_DepsIsMetForAllNodes(
    b:Behavior<CMState>,
    i:int,
    nodes:seq<int>,
    deps:Dependency
)
    requires i > 0 
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires |b[i].servers| == Nodes
    requires forall j :: 0 <= j < Nodes ==> ServerValid(b[i].servers[j].s)
    requires DependencyValid(deps)
    requires |nodes| > 1
    requires forall j :: 0 <= j < |nodes| ==> 0 <= nodes[j] < Nodes 
    requires forall j :: 0 <= j < |nodes| ==> DepsIsMet(b[i].servers[nodes[j]].s.icache, b[i].servers[nodes[j]].s.ccache, deps)
    // requires forall j :: 0 <= j < Nodes ==> j in nodes
    requires NodesAreComplete(nodes)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    reveal_DepsIsMet();
    reveal_NodesAreComplete();
    assert forall n :: n in nodes ==> DepsIsMet(b[i].servers[n].s.icache, b[i].servers[n].s.ccache, deps);
    assert |b[i].servers| == Nodes;
    assert forall j :: 0 <= j < |b[i].servers| ==> j in nodes;
    assert forall j :: 0 <= j < |b[i].servers| ==> DepsIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, deps);
    assert AllVersionsInDepsAreMetOnAllServers(b, i, deps);
}

}