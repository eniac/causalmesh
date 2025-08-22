include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
include "properties.dfy"
include "pulldeps.dfy"

module CausalMesh_PullDeps2_i {
import opened Collections__Maps_i
import opened CausalMesh_Types_i
import opened CausalMesh_Message_i
import opened CausalMesh_Properties_i
import opened CausalMesh_PullDeps_i

datatype MergedMetas = MergedMetas(
    meta:Meta,
    metas:set<Meta>
)

predicate MergedMetasValid(m:MergedMetas)
{
    
    && MetaValid(m.meta)
    && (forall mm :: mm in m.metas ==> 
        MetaValid(mm) && mm.key == m.meta.key && (VCHappendsBefore(mm.vc, m.meta.vc) || VCEq(mm.vc, m.meta.vc)))
    && var merged := FoldMetaSet2(EmptyMeta(m.meta.key), m.metas);
    && m.meta.deps == merged.deps
    && (VCHappendsBefore(merged.vc, m.meta.vc) || VCEq(merged.vc, m.meta.vc))
}

// lemma {:axiom} lemma_MergedMetasMergeMeta(m1:Meta, metas1:set<Meta>, m2:Meta, metas2:set<Meta>) 
//     requires MetaValid(m1)
//     requires MetaValid(m2)
//     requires m1.key == m2.key
//     requires forall m :: m in metas1 ==> MetaValid(m) && m.key == m1.key && (VCHappendsBefore(m.vc, m1.vc) || VCEq(m.vc, m1.vc))
//     requires forall m :: m in metas2 ==> MetaValid(m) && m.key == m2.key && (VCHappendsBefore(m.vc, m2.vc) || VCEq(m.vc, m2.vc))
//     requires var merged := FoldMetaSet2(EmptyMeta(m1.key), metas1);
//             m1.deps == merged.deps && (VCHappendsBefore(merged.vc, m1.vc) || VCEq(merged.vc, m1.vc))
//     requires var merged := FoldMetaSet2(EmptyMeta(m2.key), metas2);
//             m2.deps == merged.deps && (VCHappendsBefore(merged.vc, m2.vc) || VCEq(merged.vc, m2.vc))
//     ensures var m := MetaMerge(m1, m2); var metas := metas1 + metas2; var merged := FoldMetaSet2(EmptyMeta(m.key), metas);
//             m.deps == merged.deps && (VCHappendsBefore(merged.vc, m.vc) || VCEq(merged.vc, m.vc))


// lemma {:axiom} lemma_FoldMetaSetEqualsToFoldMetaSet2(
//     acc: Meta, metas: set<Meta>, domain:set<Key>
// )
//     requires MetaValid(acc)
//     requires forall kk :: kk in acc.deps ==> kk in domain
//     requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
//     ensures FoldMetaSet(acc, metas, domain) == FoldMetaSet2(acc, metas)


function AddMetaToMetaMap2(todos:map<Key, MergedMetas>, m:Meta, metas:set<Meta>) : (res:map<Key, MergedMetas>)
    requires forall k :: k in todos ==> MergedMetasValid(todos[k]) && todos[k].meta.key == k 
    // requires forall k :: k in todos ==> MetaValid(todos[k].meta) && todos[k].meta.key == k 
    // requires forall k :: k in todos ==> forall m :: m in todos[k].metas ==> MetaValid(m) && m.key == k
    //             && forall kk :: kk in todos[k].deps ==> 
    //                 VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    requires MetaValid(m)
    requires forall mm :: mm in metas ==> MetaValid(mm) && mm.key == m.key && (VCHappendsBefore(mm.vc, m.vc) || VCEq(mm.vc, m.vc))
    requires var merged := FoldMetaSet2(EmptyMeta(m.key), metas);
            m.deps == merged.deps && (VCHappendsBefore(merged.vc, m.vc) || VCEq(merged.vc, m.vc))

    ensures m.key in res
    ensures forall k :: k in res ==> MergedMetasValid(res[k]) && res[k].meta.key == k
    // ensures forall k :: k in res ==> MetaValid(res[k].meta) && res[k].meta.key == k 
    // ensures forall k :: k in res ==> forall m :: m in res[k].metas ==> MetaValid(m) && m.key == k
    // ensures forall k :: k in res ==> forall kk :: kk in res[k].deps ==> 
    //                 VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
{
    if m.key in todos then
        var merged := todos[m.key];
        var new_merged := merged.(
                meta := MetaMerge(merged.meta, m),
                metas := merged.metas + metas
                );
        lemma_MergedMetasMergeMeta(merged.meta, merged.metas, m, metas);
        assert MergedMetasValid(new_merged);
        todos[m.key := new_merged]
    else 
        var new_merged := MergedMetas(m, metas);
        assert MergedMetasValid(new_merged);
        todos[m.key := new_merged]
}

// lemma {:axiom} lemma_AllMetasInGetMetasOfAllDepsResultAreFromDepsInICache(
//     icache:ICache, res:map<Key, MergedMetas>
// )
//     requires forall k :: k in Keys_domain ==> k in icache
//     requires forall k :: k in res ==> MergedMetasValid(res[k]) && res[k].meta.key == k
//     ensures forall k :: k in res ==> 
//                 forall m :: m in res[k].metas ==> 


function GetMetasOfAllDeps2(icache:ICache, deps:Dependency, todos:map<Key, MergedMetas>, domain:set<Key>) : (res:map<Key, MergedMetas>)
    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    requires DependencyValid(deps)
    requires forall k :: k in todos ==> MergedMetasValid(todos[k]) && todos[k].meta.key == k 
    // requires forall k :: k in todos ==> MetaValid(todos[k].meta) && todos[k].meta.key == k 
    // requires forall k :: k in todos ==> forall m :: m in todos[k].metas ==> MetaValid(m) && m.key == k
    // requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
    //                 VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    // requires CausalCut(todos)
    requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    requires forall k :: k in deps ==> k in domain 

    // ensures forall k :: k in res ==> MetaValid(res[k])
    // ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
    // ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))

    ensures forall k :: k in res ==> MergedMetasValid(res[k]) && res[k].meta.key == k
    // ensures forall k :: k in res ==> MetaValid(res[k].meta) && res[k].meta.key == k 
    // ensures forall k :: k in res ==> forall m :: m in res[k].metas ==> MetaValid(m) && m.key == k
    //                 && forall kk :: kk in res[k].deps ==> 
    //                     VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    // ensures CausalCut(res)
    decreases |icache.Values|, |deps|
{
    if |deps| == 0 then 
        todos
    else 
        var k :| k in deps;
        var new_deps := RemoveElt(deps, k);
        if k in todos && (VCHappendsBefore(deps[k], todos[k].meta.vc) || VCEq(deps[k], todos[k].meta.vc)) then 
            var res := GetMetasOfAllDeps2(icache, new_deps, todos, domain);
            res
        else 
            var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
            if |metas| > 0 then 
                var initial := EmptyMeta(k);
                // assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
                var merged := FoldMetaSet(initial, metas, domain);
                var meta := merged.(vc := deps[k]);

                lemma_FoldMetaSetEqualsToFoldMetaSet2(initial, metas, domain);
                // assume FoldMetaSet(initial, metas, domain) == FoldMetaSet2(initial, metas);
                
                lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));
                assert forall mm :: mm in metas ==> MetaValid(mm) && mm.key == meta.key && (VCHappendsBefore(mm.vc, meta.vc) || VCEq(mm.vc, meta.vc));
                assert meta.deps == merged.deps && (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

                var new_cache := icache[k:= icache[k] - metas];
                assert icache[k] >= metas;
                lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                assert |new_cache.Values| < |icache.Values|;

                var res := GetMetasOfAllDeps2(new_cache, merged.deps, todos, domain);

                var todos' := AddMetaToMetaMap2(res, meta, metas);
                // assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
                // assert merged.deps == meta.deps;
                // lemma_AddMetaToMetaMap(res, meta);
                
                // assert forall k :: k in todos' ==>
                //         forall kk :: kk in todos'[k].deps ==>
                //             kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
                // assert CausalCut(todos');

                var res' := GetMetasOfAllDeps2(icache, new_deps, todos', domain);
                res'
            else 
                // 如果是这样，那就是已经merge到ccache里了，这是是不是应该直接拿ccache里的
                var initial := EmptyMeta(k);
                var meta := initial.(vc:=deps[k]);
                // assert CausalCut(todos);
                
                var todos' := AddMetaToMetaMap2(todos, meta, metas);
                
                var res := GetMetasOfAllDeps2(icache, new_deps, todos', domain);
                res
}
}