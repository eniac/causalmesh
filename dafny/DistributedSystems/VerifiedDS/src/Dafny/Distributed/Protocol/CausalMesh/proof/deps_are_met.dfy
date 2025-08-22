include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "meta_is_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_DepsAreMet_i {
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
import opened CausalMesh_Proof_MetaIsMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s
import opened Collections__Maps2_i

lemma lemma_MergedVCIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc1:VectorClock,
    vc2:VectorClock
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    requires k in Keys_domain
    requires AVersionIsMetOnAllServers(b, i, k, vc1)
    requires AVersionIsMetOnAllServers(b, i, k, vc2)
    ensures AVersionIsMetOnAllServers(b, i, k, VCMerge(vc1, vc2))
{

}

lemma lemma_MergedDepsIsMetOnAllServers(
    b:Behavior<CMState>,
    i:int,
    dep1:Dependency,
    dep2:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires DependencyValid(dep1)
    requires DependencyValid(dep2)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, dep1)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, dep2)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, DependencyMerge(dep1, dep2))
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    var merged := DependencyMerge(dep1, dep2);
    if |dep1.Keys + dep2.Keys| == 0 {
        assert merged == map[];
        assert AllVersionsInDepsAreMetOnAllServers(b, i, merged);
        return;
    }

    var k :| k in dep1.Keys + dep2.Keys;

    if k in dep1 && k !in dep2 {
        assert merged[k] == dep1[k];
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    } else if k in dep2 && k !in dep1 {
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    } else {
        assert merged[k] == VCMerge(dep1[k], dep2[k]);
        lemma_MergedVCIsMetOnAllServers(b, i, k, dep1[k], dep2[k]);
        assert AVersionIsMetOnAllServers(b, i, k, merged[k]);
    }
}

lemma lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(
    b: Behavior<CMState>,
    i: int,
    ccache: CCache,
    metas: map<Key, Meta>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CCacheValid(ccache)
    requires CCacheValid(metas)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, ccache)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, metas)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, MergeCCache(ccache, metas))
{
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    var merged := MergeCCache(ccache, metas);
    forall k | k in merged
        ensures AVersionIsMetOnAllServers(b, i, k, merged[k].vc) 
        // && AllVersionsInDepsAreMetOnAllServers(b, i, merged[k].deps)
    {
        if k in ccache && k !in metas {
            assert merged[k] == ccache[k];
        } else if k !in ccache && k in metas {
            assert merged[k] == metas[k];
        } else {
            assert merged[k] == MetaMerge(ccache[k], metas[k]);
            lemma_MergedVCIsMetOnAllServers(b, i, k, ccache[k].vc, metas[k].vc);
            // lemma_MergedDepsIsMetOnAllServers(b, i, ccache[k].deps, metas[k].deps);
        }
    }
} 

/** this seems not necessary, can be removed later */
lemma {:axiom} lemma_FoldMetasPreservesDepsAreMet(
    b:Behavior<CMState>,
    i:int,
    meta:Meta,
    metas:set<Meta>,
    domain:set<Key>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires MetaValid(meta)
    requires forall kk :: kk in meta.deps ==> kk in domain
    requires AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps)
    requires forall m :: m in metas ==> MetaValid(m) && m.key == meta.key && (forall kk :: kk in m.deps ==> kk in domain) && AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, FoldMetaSet(meta, metas, domain).deps)
    decreases |metas|
// {
//     if |metas| == 0 {
//         var res := FoldMetaSet(meta, metas, domain);
//         assert res == meta;
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, res.deps);
//         return;
//     }

//     var x :| x in metas;

//     var merged := MetaMerge(meta, x);
//     var new_metas := metas - {x};
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, x.deps);
//     // reveal_AllVersionsInDepsAreMetOnAllServers();
//     lemma_MergedDepsIsMetOnAllServers(b, i, meta.deps, x.deps);

//     // assert i > 0;
//     // assert IsValidBehaviorPrefix(b, i);
//     // assert CMNext(b[i-1], b[i]);
//     assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);
//     // assert MetaValid(merged);
//     // assert forall kk :: kk in merged.deps ==> kk in domain;
//     // assert forall m :: m in new_metas ==> MetaValid(m) && m.key == merged.key && (forall kk :: kk in m.deps ==> kk in domain) && AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);

//     lemma_FoldMetasPreservesDepsAreMet(b, i, merged, new_metas, domain);
// }

// lemma lemma_MetaIsMetImpliesMetasBeforeItAreMet(
//     b:Behavior<CMState>,
//     i:int,
//     meta:Meta,
//     metas:set<Meta>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires MetaValid(meta)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires forall m :: m in metas ==> MetaValid(m) && (VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc))
//     ensures forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
//     ensures forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     forall m | m in metas 
//         ensures AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
//     {
//         assert VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc);
//         lemma_MetaIsMetImpliesAllPreviousMetasAreMet(b, i, meta, m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert i > 0;
//         assert IsValidBehaviorPrefix(b, i);
//         assert MetaValid(m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
//         lemma_MetaIsMetImpliesItsDepsAreMet(b, i, m);
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//     }
// }

// lemma lemma_MetaIsMetImpliesMetasBeforeItAreMet2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     meta:Meta,
//     metas:set<Meta>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
    
//     requires MetaValid(meta)
//     requires AVersionIsMetOnAllServers(b, i, meta.key, meta.vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires forall m :: m in metas ==> MetaValid(m) && (VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc))
//     // requires forall m :: m in metas ==> m in b[i].servers[idx].s.icache[m.key]
//     requires forall m :: m in metas ==> AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, m.key, m.vc)
//     ensures forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
//     ensures forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     forall m | m in metas 
//         ensures AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
//     {
//         // lemma_BehaviorValidImpliesOneStepValid()
//         assert VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc);
//         lemma_MetaIsMetImpliesAllPreviousMetasAreMet(b, i, meta, m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert i > 0;
//         assert IsValidBehaviorPrefix(b, i);
//         assert MetaValid(m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
//         lemma_MetaIsMetImpliesItsDepsAreMet2(b, i, idx, m);
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//     }
// }

// lemma lemma_MetaIsMetImpliesMetasBeforeItAreMet3(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     vc:VectorClock,
//     metas:set<Meta>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
    
//     requires VectorClockValid(vc)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires forall m :: m in metas ==> MetaValid(m) && (VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc))
//     // requires forall m :: m in metas ==> AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, m.key, m.vc)
//     ensures forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
//     ensures forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     forall m | m in metas 
//         ensures AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         ensures AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
//     {
//         // lemma_BehaviorValidImpliesOneStepValid()
//         assert VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc);
//         lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, vc, m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert i > 0;
//         assert IsValidBehaviorPrefix(b, i);
//         assert MetaValid(m);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//         assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
//         lemma_MetaIsMetImpliesItsDepsAreMet2(b, i, idx, m);
//         assert AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
//         assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//     }
// }

lemma lemma_MetaIsMetImpliesMetasBeforeItAreMet3(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    vc:VectorClock,
    metas:set<Meta>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    
    requires VectorClockValid(vc)
    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    // requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires forall m :: m in metas ==> MetaValid(m) && (VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc))
    // requires forall m :: m in metas ==> AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, m.key, m.vc)
    ensures forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc)
    ensures forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    forall m | m in metas 
        ensures AVersionIsMetOnAllServers(b, i, m.key, m.vc);
        ensures AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    {
        // lemma_BehaviorValidImpliesOneStepValid()
        assert VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc);
        lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, vc, m.key, m.vc);
        assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
        assert i > 0;
        assert IsValidBehaviorPrefix(b, i);
        assert MetaValid(m);
        assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
        // assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);

        forall k | k in m.deps 
            ensures AVersionIsMetOnAllServers(b, i, k, m.deps[k])
        {
            assert VCHappendsBefore(m.deps[k], m.vc) || VCEq(m.deps[k], m.vc);
            assert VCHappendsBefore(m.deps[k], vc) || VCEq(m.deps[k], vc);
            lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet(b, i, vc, k, m.deps[k]);
            assert AVersionIsMetOnAllServers(b, i, k, m.deps[k]);
        }

        // lemma_MetaIsMetImpliesItsDepsAreMet2(b, i, idx, m);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
        assert AVersionIsMetOnAllServers(b, i, m.key, m.vc);
    }
}

function {:opaque} GetMetasOfAllDepsGlobalView3(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    vc:VectorClock,
    icache:ICache,
    deps:Dependency,
    todos:map<Key, Meta>,
    domain:set<Key>
) : (res:map<Key, Meta>)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    // requires icache == b[i].servers[idx].s.icache
    // requires forall k :: k in icache ==> forall m :: m in icache[k] ==> k in b[i].servers[idx].s.icache && m in b[i].servers[idx].s.icache[k]
    requires VectorClockValid(vc)

    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    requires DependencyValid(deps)
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    requires forall k :: k in deps ==> k in domain && (VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc))

    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    // requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])

    requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

    ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
    decreases |icache.Values|, |deps|
{
    reveal_AllVersionsInDepsAreMetOnAllServers();
    // reveal_AllVersionsInCCacheAreMetOnAllServers();
    
    // assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc); //&& AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
    if |deps| == 0 then 
        todos
    else 
        var k :| k in deps;
        var new_deps := RemoveElt(deps, k);
        if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
            var res := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, icache, new_deps, todos, domain);
            res
        else 
            var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
            if |metas| > 0 then
            
                var initial := EmptyMeta(k);
                var merged := FoldMetaSet(initial, metas, domain);
                var meta := merged.(vc := deps[k]);
                
                lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

                var new_cache := icache[k:= icache[k] - metas];
                assert icache[k] >= metas;
                lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                assert |new_cache.Values| < |icache.Values|;

                assert forall m :: m in metas ==> VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc);
                assert VCHappendsBefore(meta.vc, vc) || VCEq(meta.vc, vc);
                lemma_MetaIsMetImpliesMetasBeforeItAreMet3(b, i, idx, vc, metas);
                assert forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc);
                assert forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);

                assert MetaValid(initial);
                assert forall kk :: kk in initial.deps ==> kk in domain;
                assert AllVersionsInDepsAreMetOnAllServers(b, i, initial.deps);
                lemma_FoldMetasPreservesDepsAreMet(b, i, initial, metas, domain);
                assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);

                var res := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, new_cache, merged.deps, todos, domain);

                assume forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
                assume AVersionIsMetOnAllServers(b, i, k, meta.vc);

                var todos' := AddMetaToMetaMap(res, meta);

                assume AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
                lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
                assume forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

                var res' := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, icache, new_deps, todos', domain);
                res'
            else 
                var initial := EmptyMeta(k);
                var meta := initial.(vc:=deps[k]);

                assume AllVersionsInDepsAreMetOnAllServers(b, i, deps);
                assume forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
                assert AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
                assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
                
                var todos' := AddMetaToMetaMap(todos, meta);
                lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, todos, meta);
                assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);
                
                var res := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, icache, new_deps, todos', domain);
                res
}



lemma lemma_VersionsAfterPullDepsAreMetOnAllServers2(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    vc:VectorClock,
    deps:Dependency
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i], b[i+1])
    requires 0 <= idx < Nodes
    requires DependencyValid(deps)
    requires VectorClockValid(vc)
    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    // requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    requires AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
    ensures var res := PullDeps2(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps);
            AllVersionsInCCacheAreMetOnAllServers(b, i, res.1)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i);
    reveal_AllVersionsInDepsAreMetOnAllServers();
    // reveal_AllDepsInICacheAreMetOnAllServers();
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    
    // assert CMNextCommon(b[i-1], b[i]);
    var icache := b[i].servers[idx].s.icache;
    var ccache := b[i].servers[idx].s.ccache;
    var domain := icache.Keys + deps.Keys;

    var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
    var todos1 := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, icache, deps, map[], domain);
    assert forall k :: k in todos1 ==> AVersionIsMetOnAllServers(b, i, k, todos1[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos1[k].deps);
    lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps3(b, i, idx, vc, icache, deps, map[], domain);
    assert todos == todos1;
    assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);

    var new_cache := MergeCCache(ccache, todos);
    lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(b, i, ccache, todos);
    assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_cache);

    var res := PullDeps2(icache, ccache, deps);
    assert res.1 == new_cache;
    assert AllVersionsInCCacheAreMetOnAllServers(b, i, res.1);
}

// lemma lemma_VersionsAfterPullDepsAreMetOnAllServers(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     deps:Dependency
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i], b[i+1])
//     requires 0 <= idx < Nodes
//     requires DependencyValid(deps)
//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
//     ensures var res := PullDeps2(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps);
//             AllVersionsInCCacheAreMetOnAllServers(b, i, res.1)
// {
//     lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     // reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     // assert CMNextCommon(b[i-1], b[i]);
//     var icache := b[i].servers[idx].s.icache;
//     var ccache := b[i].servers[idx].s.ccache;
//     var domain := icache.Keys + deps.Keys;

//     var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
//     var todos1 := GetMetasOfAllDepsGlobalView2(b, i, idx, icache, deps, map[], domain);
//     assert forall k :: k in todos1 ==> AVersionIsMetOnAllServers(b, i, k, todos1[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos1[k].deps);
//     lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps2(b, i, idx, icache, deps, map[], domain);
//     assert todos == todos1;
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);

//     var new_cache := MergeCCache(ccache, todos);
//     lemma_MergeCCacheEnsuresAllVersionAreMetOnAllServers(b, i, ccache, todos);
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, new_cache);

//     var res := PullDeps2(icache, ccache, deps);
//     assert res.1 == new_cache;
//     assert AllVersionsInCCacheAreMetOnAllServers(b, i, res.1);
// }



lemma lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(
    b:Behavior<CMState>,
    i:int,
    todos:map<Key, Meta>,
    m:Meta
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires MetaValid(m)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc)  && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    requires AVersionIsMetOnAllServers(b, i, m.key, m.vc) && AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    ensures var res := AddMetaToMetaMap(todos, m);
            forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc)  && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
{
    lemma_MetaMapIsMetImpliesInsertedMataMapIsMet1(b, i, todos, m);
    lemma_MetaMapIsMetImpliesInsertedMataMapIsMet2(b, i, todos, m);
}

lemma lemma_MetaMapIsMetImpliesInsertedMataMapIsMet1(
    b:Behavior<CMState>,
    i:int,
    todos:map<Key, Meta>,
    m:Meta
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires MetaValid(m)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) // && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    requires AVersionIsMetOnAllServers(b, i, m.key, m.vc) // && AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    ensures var res := AddMetaToMetaMap(todos, m);
            forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) // && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
{

}


lemma lemma_MetaMapIsMetImpliesInsertedMataMapIsMet2(
    b:Behavior<CMState>,
    i:int,
    todos:map<Key, Meta>,
    m:Meta
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires MetaValid(m)
    requires forall k :: k in todos ==> AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, m.deps)
    ensures var res := AddMetaToMetaMap(todos, m);
            forall k :: k in res ==> AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
{
    // reveal_AllVersionsInDepsAreMetOnAllServers();
    var res := AddMetaToMetaMap(todos, m);
    if m.key !in todos {
        assert res == todos[m.key := m];
        assert forall k :: k in res ==> AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
    } else {
        assert res == todos[m.key := MetaMerge(todos[m.key], m)];
        assert AllVersionsInDepsAreMetOnAllServers(b, i, todos[m.key].deps);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
        lemma_MergedDepsIsMetOnAllServers(b, i, todos[m.key].deps, m.deps);
        assert AllVersionsInDepsAreMetOnAllServers(b, i, DependencyMerge(todos[m.key].deps, m.deps));
        assert AllVersionsInDepsAreMetOnAllServers(b, i, MetaMerge(todos[m.key], m).deps);
        assert forall k :: k in res ==> AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
    }

}



// function {:opaque} GetMetasOfAllDepsGlobalView(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])

//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     // reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     // assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc); //&& AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then
//             // if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
//                 // var m :| m in icache[k] && VCEq(m.vc, deps[k]);
//                 // var meta := m;
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert forall m :: m in metas ==> VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc);
//                 assert forall m :: m in metas ==> m in icache[m.key];
//                 assume AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
//                 lemma_MetaIsMetImpliesMetasBeforeItAreMet(b, i, meta, metas);
//                 assert forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//                 assert forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
//                 // assume forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1]);
//                 // assert MetaValid(meta);
//                 // assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
//                 // lemma_MetaIsMetImpliesItsDepsAreMet(b, i, meta);

//                 assert MetaValid(initial);
//                 assert forall kk :: kk in initial.deps ==> kk in domain;
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, initial.deps);
//                 lemma_FoldMetasPreservesDepsAreMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);

//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assume forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assume AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assume AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assume forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);

//                 assume AllVersionsInDepsAreMetOnAllServers(b, i, deps);
//                 assume forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, todos, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);
                
//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }

// function {:opaque} GetMetasOfAllDepsGlobalView2(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     // requires forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1])
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
//     // requires icache == b[i].servers[idx].s.icache
//     requires forall k :: k in icache ==> forall m :: m in icache[k] ==> k in b[i].servers[idx].s.icache && m in b[i].servers[idx].s.icache[k]

//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])

//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     // reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     // assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc); //&& AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView2(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then
//             // if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
//                 // var m :| m in icache[k] && VCEq(m.vc, deps[k]);
//                 // var meta := m;
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert forall m :: m in metas ==> VCHappendsBefore(m.vc, meta.vc) || VCEq(m.vc, meta.vc);
//                 assert forall m :: m in metas ==> m in icache[m.key];
//                 assert forall m :: m in metas ==> AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, m.key, m.vc);
//                 assume AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
//                 lemma_MetaIsMetImpliesMetasBeforeItAreMet2(b, i, idx, meta, metas);
//                 assert forall m :: m in metas ==> AVersionIsMetOnAllServers(b, i, m.key, m.vc);
//                 assert forall m :: m in metas ==> AllVersionsInDepsAreMetOnAllServers(b, i, m.deps);
//                 // assume forall j :: 0 <= j < i ==> CMNext(b[j], b[j+1]);
//                 // assert MetaValid(meta);
//                 // assert forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j);
//                 // lemma_MetaIsMetImpliesItsDepsAreMet(b, i, meta);

//                 assert MetaValid(initial);
//                 assert forall kk :: kk in initial.deps ==> kk in domain;
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, initial.deps);
//                 lemma_FoldMetasPreservesDepsAreMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);

//                 var res := GetMetasOfAllDepsGlobalView2(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assume forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assume AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assume AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assume forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView2(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);

//                 assume AllVersionsInDepsAreMetOnAllServers(b, i, deps);
//                 assume forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, meta.key, meta.vc);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, meta.deps);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, todos, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);
                
//                 var res := GetMetasOfAllDepsGlobalView2(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }

// function GetMetasOfAllDepsGlobalView(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     // lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
                
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert AllDepsInICacheAreMetOnAllServers(b, i, new_cache);
//                 lemma_AllMeatsAreMetImpliesMergedMetaIsMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);

//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assert forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
                
//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }

// function GetMetasOfAllDepsGlobalView(
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// ) : (res:map<Key, Meta>)
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)

//     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
//     ensures forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps)
//     decreases |icache.Values|, |deps|
// {
//     // lemma_BehaviorValidImpliesOneStepValid(b, i);
//     reveal_AllVersionsInDepsAreMetOnAllServers();
//     reveal_AllDepsInICacheAreMetOnAllServers();
//     reveal_AllVersionsInCCacheAreMetOnAllServers();
    
//     assert forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps);
//     if |deps| == 0 then 
//         todos
//     else 
//         var k :| k in deps;
//         var new_deps := RemoveElt(deps, k);
//         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
//             var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
//             res
//         else 
//             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
//             if |metas| > 0 then 
//                 var initial := EmptyMeta(k);
//                 var merged := FoldMetaSet(initial, metas, domain);
//                 var meta := merged.(vc := deps[k]);
                
                
//                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
//                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

//                 var new_cache := icache[k:= icache[k] - metas];
//                 assert icache[k] >= metas;
//                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
//                 assert |new_cache.Values| < |icache.Values|;

//                 assert AllDepsInICacheAreMetOnAllServers(b, i, new_cache);
//                 lemma_AllMeatsAreMetImpliesMergedMetaIsMet(b, i, initial, metas, domain);
//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, merged.deps);

//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, new_cache, merged.deps, todos, domain);

//                 assert forall k :: k in res ==> AVersionIsMetOnAllServers(b, i, k, res[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, res[k].deps);
//                 assert AVersionIsMetOnAllServers(b, i, k, meta.vc);

//                 var todos' := AddMetaToMetaMap(res, meta);

//                 assert AllVersionsInDepsAreMetOnAllServers(b, i, new_deps);
//                 lemma_MetaMapIsMetImpliesInsertedMataMapIsMet(b, i, res, meta);
//                 assert forall k :: k in todos' ==> AVersionIsMetOnAllServers(b, i, k, todos'[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos'[k].deps);

//                 var res' := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res'
//             else 
//                 var initial := EmptyMeta(k);
//                 var meta := initial.(vc:=deps[k]);
                
//                 var todos' := AddMetaToMetaMap(todos, meta);
                
//                 var res := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
//                 res
// }


// lemma {:axiom} lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps
// (
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i]);
//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
//                         VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
//     requires CausalCut(todos)

//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
//     ensures 
//             var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, deps, todos, domain);
//             var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
//             res1 == res2

// lemma {:axiom} lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps2
// (
//     b:Behavior<CMState>,
//     i:int,
//     idx:int,
//     icache:ICache,
//     deps:Dependency,
//     todos:map<Key, Meta>,
//     domain:set<Key>
// )
//     requires i > 0
//     requires IsValidBehaviorPrefix(b, i)
//     requires CMNext(b[i-1], b[i])
//     requires 0 <= idx < Nodes
//     requires icache == b[i].servers[idx].s.icache

//     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
//                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
//     requires DependencyValid(deps)
//     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
//     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
//     requires forall k :: k in deps ==> k in domain 

//     requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
//                         VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
//     requires CausalCut(todos)

//     requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
//     requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
//     requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
//     requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
//     ensures 
//             var res1 := GetMetasOfAllDepsGlobalView2(b, i, idx, icache, deps, todos, domain);
//             var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
//             res1 == res2

lemma {:axiom} lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps3
(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    vc:VectorClock,
    icache:ICache,
    deps:Dependency,
    todos:map<Key, Meta>,
    domain:set<Key>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires VectorClockValid(vc)

    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    requires DependencyValid(deps)
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    requires forall k :: k in deps ==> k in domain && (VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc))

    requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    requires CausalCut(todos)

    // requires forall j :: 0 < j <= i ==> AllWriteDepsAreMet(b, j)
    // requires forall j :: 0 <= j < i ==> ServerNextDoesNotDecreaseVersions(b[j], b[j+1])
    requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    ensures 
            var res1 := GetMetasOfAllDepsGlobalView3(b, i, idx, vc, icache, deps, todos, domain);
            var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
            res1 == res2
}