include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_PropagationLemma_i {
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
// import opened CausalMesh_Proof_CausalCut_i
import opened CausalMesh_Proof_PacketSending_i
import opened CausalMesh_Proof_Properties_i
// import opened CausalMesh_Proof_MessageReadReply_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s


lemma lemma_PropagationAtHead(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    key:Key,
    vc:VectorClock,
    deps:Dependency,
    ios:seq<CMIo>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires ios[0].r.msg.Message_Write?
    requires PacketValid(ios[0].r)
    requires key == ios[0].r.msg.key_write
    // requires ios[0].r.msg.start != b[i-1].servers[idx].s.next
    requires DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, ios[0].r.msg.deps_write)
    requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
    requires var sp := ExtractSentPacketsFromIos(ios);
                sp[|sp|-1].msg.Message_Propagation? && sp[|sp|-1].msg.meta.vc == vc 
                && sp[|sp|-1].msg.meta.deps == deps
    ensures AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, key, vc)
    ensures DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps)
{
    reveal_DepsIsMet();
    var p := ios[0].r;
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;

    var sp := ExtractSentPacketsFromIos(ios);
    var p_pro := sp[|sp|-1];
    assert p_pro.msg.Message_Propagation?;
    assert p_pro.msg.start == s.id;

    var k := p.msg.key_write;
    
    // var meta := p_pro.msg.meta;
    assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
    var local_metas := set m | m in p.msg.local.Values;
    assert forall m :: m in local_metas ==> MetaValid(m);
    var vcs_local := set m | m in local_metas :: m.vc;
    var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];

    var merged_vc := FoldVC(s.gvc, vcs_local);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc) || VCEq(vc, merged_vc);

    var merged_vc2 := FoldVC(merged_vc, vcs_deps);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);
    assert forall vc :: vc in vcs_deps ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);

    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, merged_vc2) || VCEq(m.vc, merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> VCHappendsBefore(p.msg.deps_write[k], merged_vc2) || VCEq(p.msg.deps_write[k], merged_vc2);

    var new_vc := AdvanceVC(merged_vc2, s.id);

    assert VCHappendsBefore(merged_vc2, new_vc) || VCEq(merged_vc2, new_vc);
    lemma_VCRelationIsTransitive2(p.msg.deps_write, local_metas, merged_vc2, new_vc);
    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, new_vc) || VCEq(m.vc, new_vc);
    assert forall k :: k in p.msg.deps_write ==> VCHappendsBefore(p.msg.deps_write[k], new_vc) || VCEq(p.msg.deps_write[k], new_vc);

    var merged_deps := FoldDependencyFromMetaSet(p.msg.deps_write, local_metas);
    lemma_FoldDependencyFromMetaSet(p.msg.deps_write, local_metas, new_vc);
    assert forall k :: k in FoldDependencyFromMetaSet(p.msg.deps_write, local_metas) ==> VCHappendsBefore(FoldDependencyFromMetaSet(p.msg.deps_write, local_metas)[k], new_vc) || VCEq(FoldDependencyFromMetaSet(p.msg.deps_write, local_metas)[k], new_vc);

    var meta := Meta(p.msg.key_write, new_vc, merged_deps);

    assert forall k :: k in meta.deps ==> VCHappendsBefore(meta.deps[k], meta.vc) || VCEq(meta.deps[k], meta.vc);

    var new_local_metas := local_metas + {meta};

    // // assert forall m :: m in new_local_metas ==> MetaValid(m);

    var new_icache := AddMetasToICache(s.icache, new_local_metas);
    lemma_AddMetasToICache_ensures_contains(s.icache, new_local_metas);
    assert meta in new_icache[k];

    assert p_pro.msg.meta == meta;
    assert s'.icache == new_icache;

    assert meta in s'.icache[k];

    var merged_meta := FoldMetaSet2(s'.ccache[k], s'.icache[k]);

    assert VCHappendsBefore(s'.ccache[k].vc, merged_meta.vc) || VCEq(s'.ccache[k].vc, merged_meta.vc);
    assert forall m :: m in s'.icache[k] ==> VCHappendsBefore(m.vc, merged_meta.vc) || VCEq(m.vc, merged_meta.vc);
    assert VCHappendsBefore(meta.vc, merged_meta.vc) || VCEq(meta.vc, merged_meta.vc);
    assert AVersionOfAKeyIsMet(s'.icache, s'.ccache, p_pro.msg.key, meta.vc);

    lemma_DepsInPropagationIsInWriteDepsOrLocals(b, i, idx, ios);
}

lemma lemma_DepsInPropagationIsInWriteDepsOrLocals(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    ios:seq<CMIo>
)
    requires 0 < i 
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires |ios| > 1
    requires ios[0].LIoOpReceive?
    requires ios[0].r.msg.Message_Write?
    requires PacketValid(ios[0].r)
    requires DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, ios[0].r.msg.deps_write)
    requires ReceiveWrite(b[i-1].servers[idx].s, b[i].servers[idx].s, ios[0].r, ExtractSentPacketsFromIos(ios))
    ensures var sp := ExtractSentPacketsFromIos(ios);
            DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, sp[|sp|-1].msg.meta.deps)
{
    reveal_DepsIsMet();
    var p := ios[0].r;
    var s := b[i-1].servers[idx].s;
    var s' := b[i].servers[idx].s;

    var sp := ExtractSentPacketsFromIos(ios);
    var p_pro := sp[|sp|-1];
    assert p_pro.msg.Message_Propagation?;
    assert p_pro.msg.start == s.id;

    var k := p.msg.key_write;
    
    // var meta := p_pro.msg.meta;
    assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
    var local_metas := set m | m in p.msg.local.Values;
    assert forall m :: m in local_metas ==> MetaValid(m);
    var vcs_local := set m | m in local_metas :: m.vc;
    var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];

    var merged_vc := FoldVC(s.gvc, vcs_local);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc) || VCEq(vc, merged_vc);

    var merged_vc2 := FoldVC(merged_vc, vcs_deps);
    assert forall vc :: vc in vcs_local ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);
    assert forall vc :: vc in vcs_deps ==> VCHappendsBefore(vc, merged_vc2) || VCEq(vc, merged_vc2);

    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, merged_vc2) || VCEq(m.vc, merged_vc2);
    assert forall k :: k in p.msg.deps_write ==> VCHappendsBefore(p.msg.deps_write[k], merged_vc2) || VCEq(p.msg.deps_write[k], merged_vc2);

    var new_vc := AdvanceVC(merged_vc2, s.id);

    assert VCHappendsBefore(merged_vc2, new_vc) || VCEq(merged_vc2, new_vc);
    lemma_VCRelationIsTransitive2(p.msg.deps_write, local_metas, merged_vc2, new_vc);
    assert forall m :: m in local_metas ==> VCHappendsBefore(m.vc, new_vc) || VCEq(m.vc, new_vc);
    assert forall k :: k in p.msg.deps_write ==> VCHappendsBefore(p.msg.deps_write[k], new_vc) || VCEq(p.msg.deps_write[k], new_vc);

    var merged_deps := FoldDependencyFromMetaSet(p.msg.deps_write, local_metas);
    lemma_FoldDependencyFromMetaSet(p.msg.deps_write, local_metas, new_vc);
    assert forall k :: k in FoldDependencyFromMetaSet(p.msg.deps_write, local_metas) ==> VCHappendsBefore(FoldDependencyFromMetaSet(p.msg.deps_write, local_metas)[k], new_vc) || VCEq(FoldDependencyFromMetaSet(p.msg.deps_write, local_metas)[k], new_vc);

    var meta := Meta(p.msg.key_write, new_vc, merged_deps);

    assert forall k :: k in meta.deps ==> VCHappendsBefore(meta.deps[k], meta.vc) || VCEq(meta.deps[k], meta.vc);

    var new_local_metas := local_metas + {meta};

    // // assert forall m :: m in new_local_metas ==> MetaValid(m);

    var new_icache := AddMetasToICache(s.icache, new_local_metas);
    lemma_AddMetasToICache_ensures_contains(s.icache, new_local_metas);

    assert s'.ccache == s.ccache;
    assert forall m :: m in local_metas ==> m in s'.icache[m.key];

    lemma_DepsInPropagationIsInWriteDepsOrLocals_helper(s.icache, s'.ccache, s'.icache, p.msg.deps_write, local_metas, meta);
    assert DepsIsMet(s'.icache, s'.ccache, merged_deps);
    assert sp[|sp|-1].msg.Message_Propagation?;
    assert sp[|sp|-1].msg.meta.deps == merged_deps;
    assert DepsIsMet(s'.icache, s'.ccache, sp[|sp|-1].msg.meta.deps);
}


// prove that if deps is met after serverwrite, then deps is also met after serverwrite
// and local are also in icache, so locals are also met in icache
// then deps merge locals is met
lemma {:axiom} lemma_DepsInPropagationIsInWriteDepsOrLocals_helper(
    icache:ICache,
    ccache:CCache,
    new_icache:ICache,
    deps:Dependency,
    metas:set<Meta>,
    meta:Meta
)
    requires ICacheValid(icache)
    requires ICacheValid(new_icache)
    requires CCacheValid(ccache)
    requires forall k :: k in Keys_domain ==> k in icache && k in ccache && k in new_icache
    requires DependencyValid(deps)
    requires forall m :: m in metas ==> MetaValid(m) && forall k :: k in m.deps ==> k in icache
    requires MetaValid(meta) && forall k :: k in meta.deps ==> k in icache
    requires new_icache == AddMetasToICache(icache, metas + {meta})
    requires DepsIsMet(icache, ccache, deps)
    ensures DepsIsMet(new_icache, ccache, FoldDependencyFromMetaSet(deps, metas))
// {
//     reveal_DepsIsMet();
//     var merged := FoldDependencyFromMetaSet(deps, metas);
//     assert DepsIsMet(icache, ccache, deps);
//     lemma_AddMetasToICache_ensures_contains(icache, metas + {meta});
//     assert forall k :: k in icache ==> k in new_icache && forall m :: m in icache[k] ==> m in new_icache[k];
//     assume DepsIsMet(new_icache, ccache, deps);

//     forall k | k in merged 
//     {
//         // var m1 := FoldMetaSet2(ccache[k], icache[k]);
//         // var m2 := FoldMetaSet2(ccache[k], new_icache[k]);

//         // assert k in icache && k in new_icache;
//         // assert forall m :: m in icache[k] ==> m in new_icache[k];
//         // assume VCHappendsBefore(m1.vc, m2.vc) || VCEq(m1.vc, m2.vc);

        
//         // assert AVersionOfAKeyIsMet(icache, ccache, k, deps[k]);
//         // assert VCEq(deps[k], m1.vc) || VCHappendsBefore(deps[k], m1.vc);
//     }
//     // assert DepsIsMet(new_icache, ccache, deps);
// }



}