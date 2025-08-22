include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
include "properties.dfy"

module CausalMesh_PullDeps_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    import opened CausalMesh_Properties_i

    function AddMetaToMetaMap(todos:map<Key, Meta>, m:Meta) : (res:map<Key, Meta>)
        requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
                    && forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
        requires MetaValid(m)
        ensures m.key in res
        ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
        ensures forall k :: k in res ==> forall kk :: kk in res[k].deps ==> 
                        VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    {
        if m.key in todos then
            todos[m.key := MetaMerge(todos[m.key], m)]
        else 
            todos[m.key := m]
    }

    lemma lemma_AddMetaToMetaMap(todos:map<Key, Meta>, m:Meta)
        requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
                    && forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
        requires CausalCut(todos)
        requires MetaValid(m)
        requires forall k :: k in m.deps ==> k in todos && (VCHappendsBefore(m.deps[k], todos[k].vc) || VCEq(m.deps[k], todos[k].vc))
        ensures var res := AddMetaToMetaMap(todos, m);
                CausalCut(res)
    {

    }

    function GetMetasOfAllDeps(icache:ICache, deps:Dependency, todos:map<Key, Meta>, domain:set<Key>) : (res:map<Key, Meta>)
        requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                    && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
        requires DependencyValid(deps)
        requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
        requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
        requires CausalCut(todos)
        requires forall k :: k in Keys_domain ==> k in icache // should we have this?
        requires forall k :: k in deps ==> k in domain 

        ensures forall k :: k in res ==> MetaValid(res[k])
        ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
        ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
        ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
                        && forall kk :: kk in res[k].deps ==> 
                            VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
        ensures CausalCut(res)
        decreases |icache.Values|, |deps|
    {
        if |deps| == 0 then 
            todos
        else 
            var k :| k in deps;
            var new_deps := RemoveElt(deps, k);
            if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
                var res := GetMetasOfAllDeps(icache, new_deps, todos, domain);
                res
            else 
                var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
                if |metas| > 0 then 
                    var initial := EmptyMeta(k);
                    assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
                    var merged := FoldMetaSet(initial, metas, domain);
                    var meta := merged.(vc := deps[k]);
                    
                    lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                    assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

                    var new_cache := icache[k:= icache[k] - metas];
                    assert icache[k] >= metas;
                    lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                    assert |new_cache.Values| < |icache.Values|;

                    var res := GetMetasOfAllDeps(new_cache, merged.deps, todos, domain);

                    var todos' := AddMetaToMetaMap(res, meta);
                    assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
                    assert merged.deps == meta.deps;
                    lemma_AddMetaToMetaMap(res, meta);
                    
                    assert forall k :: k in todos' ==>
                            forall kk :: kk in todos'[k].deps ==>
                                kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
                    assert CausalCut(todos');

                    var res' := GetMetasOfAllDeps(icache, new_deps, todos', domain);
                    res'
                else 
                    var initial := EmptyMeta(k);
                    var meta := initial.(vc:=deps[k]);
                    assert CausalCut(todos);
                   
                    var todos' := AddMetaToMetaMap(todos, meta);
                    
                    var res := GetMetasOfAllDeps(icache, new_deps, todos', domain);
                    res
    }

    // function GetMetasOfAllDeps(icache:ICache, deps:Dependency, todos:map<Key, Meta>, domain:set<Key>) : (res:map<Key, Meta>)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //     requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
    //                     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     requires CausalCut(todos)
    //     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain 
    //     // requires forall k :: k in deps ==> k in todos
    //     // ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in res ==> MetaValid(res[k])
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
    //     ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
    //     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //                     && forall kk :: kk in res[k].deps ==> 
    //                         VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    //     ensures CausalCut(res)
    //     decreases |icache.Values|, |deps|
    // {
    //     if |deps| == 0 then 
    //         // lemma_MetaMapIsCausalCut(todos);
    //         todos
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
    //             // lemma_MetaMapIsCausalCut(todos);
    //             var res := GetMetasOfAllDeps(icache, new_deps, todos, domain);
    //             res
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             if |metas| > 0 then 
    //                 var initial := EmptyMeta(k);
    //                 assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //                 var merged := FoldMetaSet(initial, metas, domain);
    //                 var meta := merged.(vc := deps[k]);
                    
    //                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));
    //                 // var todos' := AddMetaToMetaMap(todos, merged);
    //                 // var todos' := AddMetaToMetaMap(todos, meta);

    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));

    //                 var new_cache := icache[k:= icache[k] - metas];
    //                 assert icache[k] >= metas;
    //                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
    //                 assert |new_cache.Values| < |icache.Values|;
    //                 // assert k in todos';
    //                 // lemma_MetaMapIsCausalCut(todos);

    //                 var res := GetMetasOfAllDeps(new_cache, merged.deps, todos, domain);
    //                 // lemma_MetaMapIsCausalCut(res);
    //                 var todos' := AddMetaToMetaMap(res, meta);
    //                 assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
    //                 assert merged.deps == meta.deps;
    //                 lemma_AddMetaToMetaMap(res, meta);
    //                 // lemma_MetaMapIsCausalCut(todos');
                    
    //                 assert forall k :: k in todos' ==>
    //                         forall kk :: kk in todos'[k].deps ==>
    //                             kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
    //                 assert CausalCut(todos');
    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));
    //                 // assert k in todos' && (VCHappendsBefore(deps[k], todos'[k].vc) || VCEq(deps[k], todos'[k].vc));

    //                 var res' := GetMetasOfAllDeps(icache, new_deps, todos', domain);
    //                 res'
    //             else 
    //                 var initial := EmptyMeta(k);
    //                 var meta := initial.(vc:=deps[k]);
    //                 assert CausalCut(todos);
                   
    //                 var todos' := AddMetaToMetaMap(todos, meta);
                    
    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));
    //                 var res := GetMetasOfAllDeps(icache, new_deps, todos', domain);
    //                 res
    // }


    // function AddMetaToMetaMap(todos:map<Key, Meta>, m:Meta) : (res:map<Key, Meta>)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //                 && forall kk :: kk in todos[k].deps ==> 
    //                     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     requires MetaValid(m)
    //     ensures m.key in res
    //     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //     ensures forall k :: k in res ==> forall kk :: kk in res[k].deps ==> 
    //                     VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    // {
    //     if m.key in todos then
    //         todos[m.key := MetaMerge(todos[m.key], m)]
    //     else 
    //         todos[m.key := m]
    // }

    // lemma lemma_AddMetaToMetaMap(todos:map<Key, Meta>, m:Meta)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //                 && forall kk :: kk in todos[k].deps ==> 
    //                     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     requires forall k :: k in todos ==> 
    //                 forall kk :: kk in todos[k].deps ==> kk in todos && (VCHappendsBefore(todos[k].deps[kk], todos[kk].vc) || VCEq(todos[k].deps[kk], todos[kk].vc))
    //     requires MetaValid(m)
    //     requires forall k :: k in m.deps ==> k in todos && (VCHappendsBefore(m.deps[k], todos[k].vc) || VCEq(m.deps[k], todos[k].vc))
    //     ensures var res := AddMetaToMetaMap(todos, m);
    //             forall k :: k in res ==> 
    //                 forall kk :: kk in res[k].deps ==> kk in res && (VCHappendsBefore(res[k].deps[kk], res[kk].vc) || VCEq(res[k].deps[kk], res[kk].vc))
    // {

    // }

    // lemma {:axiom} lemma_MetaMapIsCausalCut(metas:map<Key,Meta>)
    //     requires forall k :: k in metas ==> MetaValid(metas[k])
    //     ensures forall k :: k in metas ==>
    //                 forall kk :: kk in metas[k].deps ==> kk in metas && (VCHappendsBefore(metas[k].deps[kk], metas[kk].vc) || VCEq(metas[k].deps[kk], metas[kk].vc))

    // function GetMetasOfAllDeps(icache:ICache, deps:Dependency, todos:map<Key, Meta>, domain:set<Key>) : (res:map<Key, Meta>)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //     requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
    //                     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     // requires forall k :: k in todos ==>
    //     //             forall kk :: kk in todos[k].deps ==>
    //     //                 kk in todos && (VCHappendsBefore(todos[k].deps[kk], todos[kk].vc) || VCEq(todos[k].deps[kk], todos[kk].vc))
    //     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain 
    //     // requires forall k :: k in deps ==> k in todos
    //     // ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in res ==> MetaValid(res[k])
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
    //     ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
    //     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //                     && forall kk :: kk in res[k].deps ==> 
    //                         VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    //     // ensures forall k :: k in res ==>
    //     //             forall kk :: kk in res[k].deps ==>
    //     //                 kk in res && (VCHappendsBefore(res[k].deps[kk], res[kk].vc) || VCEq(res[k].deps[kk], res[kk].vc))
    //     decreases |icache.Values|, |deps|
    // {
    //     if |deps| == 0 then 
    //         // lemma_MetaMapIsCausalCut(todos);
    //         todos
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
    //             // lemma_MetaMapIsCausalCut(todos);
    //             var res := GetMetasOfAllDeps(icache, new_deps, todos, domain);
    //             res
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             if |metas| > 0 then 
    //                 var initial := EmptyMeta(k);
    //                 assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //                 var merged := FoldMetaSet(initial, metas, domain);
    //                 var meta := merged.(vc := deps[k]);
                    
    //                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));
    //                 // var todos' := AddMetaToMetaMap(todos, merged);
    //                 // var todos' := AddMetaToMetaMap(todos, meta);

    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));

    //                 var new_cache := icache[k:= icache[k] - metas];
    //                 assert icache[k] >= metas;
    //                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
    //                 assert |new_cache.Values| < |icache.Values|;
    //                 // assert k in todos';
    //                 // lemma_MetaMapIsCausalCut(todos);

    //                 var res := GetMetasOfAllDeps(new_cache, merged.deps, todos, domain);
    //                 lemma_MetaMapIsCausalCut(res);
    //                 // assert forall k :: k in res ==>
    //                 //     forall kk :: kk in res[k].deps ==>
    //                 //         kk in res;
    //                 var todos' := AddMetaToMetaMap(res, meta);
    //                 assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
    //                 assert merged.deps == meta.deps;
    //                 lemma_AddMetaToMetaMap(res, meta);
    //                 // lemma_MetaMapIsCausalCut(todos');
    //                 assert forall k :: k in todos' ==>
    //                         forall kk :: kk in todos'[k].deps ==>
    //                             kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));
    //                 // assert k in todos' && (VCHappendsBefore(deps[k], todos'[k].vc) || VCEq(deps[k], todos'[k].vc));

    //                 var res' := GetMetasOfAllDeps(icache, new_deps, todos', domain);
    //                 // assert forall k :: k in res' ==>
    //                 //         forall kk :: kk in res'[k].deps ==>
    //                 //             kk in res';
    //                 res'
    //             else 
    //                 var initial := EmptyMeta(k);
    //                 var meta := initial.(vc:=deps[k]);
    //                 lemma_MetaMapIsCausalCut(todos);
    //                 // assert forall k :: k in todos ==>
    //                 //     forall kk :: kk in todos[k].deps ==>
    //                 //         kk in todos;
    //                 var todos' := AddMetaToMetaMap(todos, meta);
    //                 // assert forall k :: k in todos' ==>
    //                 //     forall kk :: kk in todos'[k].deps ==>
    //                 //         kk in todos';
    //                 // assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));
    //                 var res := GetMetasOfAllDeps(icache, new_deps, todos', domain);
    //                 // assert forall k :: k in res ==>
    //                 //         forall kk :: kk in res[k].deps ==>
    //                 //             kk in res;
    //                 res
    // }

    // // worked before proving res is a causal cut
    // function GetMetasOfAllDeps(icache:ICache, deps:Dependency, todos:map<Key, Meta>, domain:set<Key>) : (res:map<Key, Meta>)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //                 && forall kk :: kk in todos[k].deps ==> 
    //                     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     // requires forall k :: k in todos ==>
    //     //             forall kk :: kk in todos[k].deps ==>
    //     //                 kk in todos
    //     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain 
    //     // requires forall k :: k in deps ==> k in todos
    //     // ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in res ==> MetaValid(res[k])
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
    //     ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
    //     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //                     && forall kk :: kk in res[k].deps ==> 
    //                         VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    //     // ensures forall k :: k in res ==>
    //     //             forall kk :: kk in res[k].deps ==>
    //     //                 kk in res
    //     decreases |icache.Values|, |deps|
    // {
    //     if |deps| == 0 then 
    //         todos
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
    //             var res := GetMetasOfAllDeps(icache, new_deps, todos, domain);
    //             res
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             if |metas| > 0 then 
    //                 var initial := EmptyMeta(k);
    //                 assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //                 var merged := FoldMetaSet(initial, metas, domain);
    //                 var meta := merged.(vc := deps[k]);
                    
    //                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //                 assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));
    //                 // var todos' := AddMetaToMetaMap(todos, merged);
    //                 var todos' := AddMetaToMetaMap(todos, meta);

    //                 assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));

    //                 var new_cache := icache[k:= icache[k] - metas];
    //                 assert icache[k] >= metas;
    //                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
    //                 assert |new_cache.Values| < |icache.Values|;
    //                 assert k in todos';

    //                 var res := GetMetasOfAllDeps(new_cache, merged.deps, todos', domain);
    //                 assert k in todos' && (VCHappendsBefore(deps[k], todos'[k].vc) || VCEq(deps[k], todos'[k].vc));

    //                 var res' := GetMetasOfAllDeps(icache, new_deps, res, domain);
    //                 res'
    //             else 
    //                 var initial := EmptyMeta(k);
    //                 var meta := initial.(vc:=deps[k]);
    //                 var todos' := AddMetaToMetaMap(todos, meta);
    //                 assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk].vc, todos'[kk].vc) || VCEq(todos[kk].vc, todos'[kk].vc));
    //                 var res := GetMetasOfAllDeps(icache, new_deps, todos', domain);
    //                 res
    // }

}