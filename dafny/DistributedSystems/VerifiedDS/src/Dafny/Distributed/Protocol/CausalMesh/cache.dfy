include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
include "properties.dfy"
include "pulldeps.dfy"

module CausalMesh_Cache_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    import opened CausalMesh_Properties_i
    import opened CausalMesh_PullDeps_i
    import opened Environment_s

    function Circle(id:int, nodes:int) : (i:int)
        requires 0 <= id < nodes
        ensures 0 <= i < nodes
    {
        if nodes == 1 then 
            id
        else if id == nodes - 1 then
            0
        else
            id + 1
    }

    // function GetDeps(icache:ICache, deps:Dependency, todos:set<(Key, VectorClock)>, domain:set<Key>) : (res:set<(Key, VectorClock)>)
    //     // requires ICacheValid(icache)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in icache ==> k in domain
    //     requires forall k :: k in deps ==> k in domain
    //     requires forall kv :: kv in todos ==> kv.0 in domain && kv.0 in Keys_domain
    //     // requires forall k :: k in deps ==> k in icache
    //     requires forall kv :: kv in todos ==> VectorClockValid(kv.1) // && kv.0 in icache
    //     ensures forall kv :: kv in res ==> VectorClockValid(kv.1) && kv.0 in domain && kv.0 in Keys_domain
    //     decreases |icache|, |deps| 
    // {
    //     if |deps| == 0 then 
    //         todos
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         assert |new_deps| < |deps|;
    //         if (k, deps[k]) in todos then
    //             GetDeps(icache, new_deps, todos, domain)
    //         else if !(k in icache) then // why?
    //             GetDeps(icache, new_deps, todos, domain)
    //         else if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
    //             var m :| m in icache[k] && VCEq(m.vc, deps[k]);
    //             var new_cache := RemoveElt(icache, k); // is this right?
    //             assert |new_cache| < |icache|;
    //             var updatedTodos := todos + {(k, deps[k])};
    //             var recursive := GetDeps(new_cache, m.deps, updatedTodos, domain);
    //             GetDeps(icache, new_deps, recursive, domain)
    //         else
    //             GetDeps(icache, new_deps, todos + {(k, deps[k])}, domain)
    // }

    // function MergeTodos(todos:set<(Key, VectorClock)>, deps:Dependency) : (res:Dependency)
    //     requires forall kv :: kv in todos ==> VectorClockValid(kv.1) && kv.0 in Keys_domain
    //     requires DependencyValid(deps)
    //     ensures DependencyValid(res)
    //     ensures forall k :: k in res ==> (exists kv :: kv in todos && kv.0 == k) || (exists k2 :: k2 in deps && k2 == k)
    //     decreases |todos|
    // {
    //     if |todos| == 0 then 
    //         deps
    //     else
    //         var todo :| todo in todos;
    //         var key := todo.0;
    //         var vc := todo.1;
    //         if key in deps then 
    //             var new_deps := deps[key := VCMerge(deps[key], vc)];
    //             MergeTodos(todos - {todo}, new_deps)
    //         else 
    //             var new_deps := deps[key := vc];
    //             MergeTodos(todos - {todo}, new_deps)
    // } 

    // function RemoveNotLarger(bk:set<Meta>, vc:VectorClock, bk_res:set<Meta>, res:Meta, domain:set<Key>) : (r:(set<Meta>, Meta))
    //     requires forall m :: m in bk ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
    //     requires VectorClockValid(vc)
    //     requires forall m :: m in bk_res ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
    //     requires MetaValid(res)
    //     requires VCHappendsBefore(res.vc, vc) || VCEq(res.vc, vc)
    //     requires exists m :: m in bk ==> m.vc == vc
    //     ensures forall m :: m in r.0 ==> MetaValid(m) && m.key == res.key && (forall kk :: kk in m.deps ==> kk in domain)
    //     ensures MetaValid(r.1)
    //     ensures forall m :: m in bk ==> m.key == r.1.key
    //     ensures VCHappendsBefore(res.vc, r.1.vc) || VCEq(res.vc, r.1.vc)
    //     ensures VCEq(r.1.vc, vc)
    //     decreases |bk|
    // {
    //     if |bk| == 0 then 
    //         lemma_ResEqToVC(vc, res);
    //         (bk_res, res)
    //     else 
    //         var m :| m in bk;
    //         if VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc) then 
    //             var r := RemoveNotLarger(bk - {m}, vc, bk_res, MetaMerge(res, m), domain);
    //             var merged := MetaMerge(res, m);

    //             assert VCHappendsBefore(merged.vc, r.1.vc) || VCEq(merged.vc, r.1.vc);
    //             // assert VCHappendsBefore(r.1.vc, vc) || VCEq(r.1.vc, vc);
    //             // assert VCEq(r.1.vc, vc);
    //             r
    //         else 
    //             var r := RemoveNotLarger(bk - {m}, vc, bk_res + {m}, res, domain);
    //             // assert VCHappendsBefore(r.1.vc, vc) || VCEq(r.1.vc, vc);
    //             r
    // }

    // lemma {:axiom} lemma_ResEqToVC(vc:VectorClock, res:Meta)
    //     requires VectorClockValid(vc)
    //     requires MetaValid(res)
    //     ensures vc == res.vc

    // lemma lemma_MergedVCIsTargetAfterMerge(bk: set<Meta>, vc: VectorClock, acc: Meta, domain: set<Key>)
    //     requires VectorClockValid(vc)
    //     requires forall m :: m in bk ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
    //     requires MetaValid(acc)
    //     requires forall m :: m in bk ==> VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc)
    //     requires VCHappendsBefore(acc.vc, vc) || VCEq(acc.vc, vc)
    //     requires exists m :: m in bk ==> VCEq(m.vc, vc)
    //     ensures VCEq(FoldMetaSet(acc, bk, domain).vc, vc)
    // {
    //     if |bk| == 0 {
    //         assert false; // violates precondition: exists m
    //     } else {
    //         var m :| m in bk;
    //         var rest := bk - {m};
    //         if VCEq(m.vc, vc) {
    //             var merged := MetaMerge(acc, m);
    //             assert VCEq(merged.vc, vc); // 因为 acc.vc <= vc，m.vc == vc
    //             assert VCEq(FoldMetaSet(merged, rest, domain).vc, vc); // inductive
    //         } else {
    //             lemma_MergedVCIsTargetAfterMerge(rest, vc, MetaMerge(acc, m), domain);
    //         }
    //     }
    // }


    // function PullTodos(icache:ICache, ccache:CCache, todos:set<(Key, VectorClock)>) : (ICache, CCache)
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall kv :: kv in todos ==> VectorClockValid(kv.1) && kv.0 in icache && kv.0 in ccache // is this true?
    //     ensures var c := PullTodos(icache, ccache, todos);
    //             && ICacheValid(c.0)
    //             && CCacheValid(c.1)
    //     decreases |todos|
    // {
    //     if |todos| == 0 then 
    //         (icache, ccache)
    //     else 
    //         var kv :| kv in todos;
    //         var vc := kv.1;
    //         var k := kv.0;
    //         var metas := icache[k];
    //         var init := Meta(k, 0, EmptyVC(), map[]);
    //         var pair := RemoveNotLarger(metas, vc, {}, init);
    //         assert MetaValid(pair.1);
    //         assert forall m :: m in metas ==> m.key == pair.1.key;
    //         var updated_icache := icache[k := pair.0];
    //         var updated_ccache := ccache[k := MetaMerge(ccache[k], pair.1)];
    //         PullTodos(updated_icache, updated_ccache, todos - {kv})
    // }

    // function PullTodos(icache:ICache, ccache:CCache, todos:Dependency) : (c:(ICache, CCache))
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires DependencyValid(todos) 
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     requires forall k :: k in todos ==> k in icache 
    //     requires ReadsDepsAreMet(icache, ccache, todos)
    //     // requires forall k :: k in todos ==> k in ccache // is this true?
    //     // ensures var c := PullTodos(icache, ccache, todos);
    //     ensures ICacheValid(c.0)
    //     ensures CCacheValid(c.1)
    //     // ensures forall k :: k in todos ==> k in c.0 && k in c.1
    //     ensures forall k :: k in icache ==> k in c.0
    //     ensures forall k :: k in ccache ==> k in c.1 && (VCHappendsBefore(ccache[k].vc, c.1[k].vc) || VCEq(ccache[k].vc, c.1[k].vc))
    //     ensures forall k :: k in todos ==> k in c.1 && (VCHappendsBefore(todos[k], c.1[k].vc) || VCEq(todos[k], c.1[k].vc))
    //     decreases |todos|
    // {
    //     if |todos| == 0 then 
    //         (icache, ccache)
    //     else
    //         var k :| k in todos;
    //         var vc := todos[k];
    //         if VCHappendsBefore(vc, ccache[k].vc) || VCEq(vc, ccache[k].vc) then 
    //             var todos' := RemoveElt(todos, k);
    //             var res := PullTodos(icache, ccache, todos');
    //             res
    //         else 
    //             // assert VCHappendsBefore(ccache[k].vc, vc);
    //             var metas := icache[k];
    //             var init := Meta(k, EmptyVC(), map[]);
    //             var domain := icache.Keys;
    //             var pair := RemoveNotLarger(metas, vc, {}, init, domain);
    //             assert pair.1.key == k;
    //             assert VCEq(pair.1.vc, vc);
    //             assert MetaValid(pair.1);
    //             assert forall m :: m in metas ==> m.key == pair.1.key;
    //             assert forall kv :: kv in pair.0 ==> forall kk :: kk in kv.deps ==> kk in icache;
    //             var updated_icache := icache[k := pair.0];
    //             // var updated_ccache := ccache[k := MetaMerge(ccache[k], pair.1)];

    //             // assert VCHappendsBefore(todos[k], pair.1.vc) || VCEq(todos[k], pair.1.vc);
    //             var updated_ccache := InsertIntoCCache(ccache, pair.1); // this is different from the TLA+ spec
    //             // assert k in updated_ccache && (VCHappendsBefore(todos[k], updated_ccache[k].vc) || VCEq(todos[k], updated_ccache[k].vc));

    //             assert forall kk :: kk in Keys_domain ==> kk in icache && kk in ccache;
    //             assert forall kk :: kk in icache ==> kk in updated_icache;
    //             assert forall kk :: kk in ccache ==> kk in updated_ccache;
    //             lemma_DomainRemains(icache, ccache, updated_icache, updated_ccache);
    //             assert forall kk :: kk in Keys_domain ==> kk in updated_icache && kk in updated_ccache;

    //             lemma_InsertNotSmallerVCIntoCCache(ccache, pair.1);
    //             assert VCHappendsBefore(vc, updated_ccache[k].vc) || VCEq(updated_ccache[k].vc, vc);

    //             var todos' := RemoveElt(todos, k);
    //             var res := PullTodos(updated_icache, updated_ccache, todos');
    //             assert forall kk :: kk in todos' ==> kk in res.1; //&& (VCHappendsBefore(todos'[kk], res.1[kk].vc) || VCEq(todos'[kk], res.1[kk].vc));
    //             assert todos.Keys == todos'.Keys + {k};
    //             assert forall kk :: kk in updated_ccache ==> kk in res.1 && (VCHappendsBefore(updated_ccache[kk].vc, res.1[kk].vc) || VCEq(updated_ccache[kk].vc, res.1[kk].vc));
    //             assert k in res.1 && (VCHappendsBefore(todos[k], res.1[k].vc) || VCEq(todos[k], res.1[k].vc));
    //             // assert forall kk :: kk in todos' ==> kk in res
    //             res
    // }

    lemma lemma_InsertNotSmallerVCIntoCCache(ccache:CCache, m:Meta)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in ccache
        requires MetaValid(m)
        requires !VCHappendsBefore(m.vc, ccache[m.key].vc) && !VCEq(ccache[m.key].vc, m.vc)
        ensures  VCHappendsBefore(m.vc, InsertIntoCCache(ccache, m)[m.key].vc) || VCEq(InsertIntoCCache(ccache, m)[m.key].vc, m.vc)
    {

    }

    lemma lemma_DomainRemains(icache:ICache, ccache:CCache, icache':ICache, ccache':CCache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in icache ==> k in icache'
        requires forall k :: k in ccache ==> k in ccache'
        ensures forall k :: k in Keys_domain ==> k in icache' && k in ccache'
    {

    }

    // function PullDeps(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall k :: k in ccache ==> k in icache
    //     requires DependencyValid(deps)
    //     requires forall k :: k in deps ==> k in icache && k in ccache
    //     ensures ICacheValid(c.0)
    //     ensures CCacheValid(c.1)
    // {
    //     var domain := icache.Keys + deps.Keys;
    //     var todos := GetDeps(icache, deps, {}, domain);
    //     assert forall kv :: kv in todos ==> kv.0 in icache;
    //     var merged := MergeTodos(todos, map[]);
    //     assert forall k :: k in merged ==> exists kv :: kv in todos && kv.0 == k;
    //     assert forall k :: k in merged ==> k in icache;
    //     PullTodos(icache, ccache, merged)
    // }



    // function GetDeps2(icache:ICache, deps:Dependency, todos:Dependency, domain:set<Key>) : (res:Dependency)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in icache ==> k in domain
    //     // requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain
    //     requires forall k :: k in todos ==> k in domain && k in Keys_domain && VectorClockValid(todos[k])
    //     ensures DependencyValid(res)
    //     ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k], res[k]) || VCEq(todos[k], res[k]))
    //     // ensures forall k :: k in deps ==> k in res
    //     decreases |icache|, |deps|
    // {
    //     if |deps| == 0 then 
    //         todos 
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then 
    //             GetDeps2(icache, new_deps, todos, domain)
    //         else if !(k in icache) then 
    //             GetDeps2(icache, new_deps, todos, domain)
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             var initial := EmptyMeta(k);
    //             assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //             var merged := FoldMetaSet(initial, metas, domain);

    //             lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //             assert VCHappendsBefore(merged.vc, deps[k]) || VCEq(merged.vc, deps[k]);
    //             assert forall kk :: kk in merged.deps ==> kk in domain;
    //             // var updaetd := GetDeps2(icache, merged.deps, )
    //             var todos' := DependencyInsertOrMerge(todos, k, merged.vc);

    //             // assert VCHappendsBefore(todos'[k], deps[k]) || VCEq(todos'[k], deps[k]);

    //             var new_cache := RemoveElt(icache, k); // is this right?
    //             var res := GetDeps2(new_cache, merged.deps, todos', domain);

    //             assert forall k :: k in todos' ==> k in res && (VCHappendsBefore(todos'[k], res[k]) || VCEq(todos'[k], res[k]));

    //             // var final := DependencyMerge(todos', res);
    //             // lemma_DependencyMergeDominatedByTheLargerOne(todos', res);
    //             // assert final == res;
    //             // var final := DependencyInsertOrMerge(added2, k, merged.vc);
    //             GetDeps2(icache, new_deps, res, domain)
    // }

    // function GetDeps2(icache:ICache, deps:Dependency, todos:Dependency, domain:set<Key>) : (res:Dependency)
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     // requires forall k :: k in icache ==> k in domain
    //     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain
    //     requires forall k :: k in todos ==> k in domain && k in Keys_domain && VectorClockValid(todos[k])
    //     ensures DependencyValid(res)
    //     ensures forall k :: k in res ==> k in domain
    //     ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k], res[k]) || VCEq(todos[k], res[k]))
    //     ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k]) || VCEq(deps[k], res[k]))
    //     decreases |icache.Values|, |deps|
    // {
    //     if |deps| == 0 then 
    //         assert forall k :: k in deps ==> k in todos;
    //         todos 
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         assert deps.Keys == new_deps.Keys + {k};
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then 
    //             var res := GetDeps2(icache, new_deps, todos, domain);
    //             assert forall kk :: kk in new_deps ==> kk in res;
    //             assert k in todos;
    //             assert forall kk :: kk in todos ==> kk in res;
    //             assert forall kk :: kk in deps ==> kk in res;
    //             res
    //         // else if !(k in icache) then 
    //         //     GetDeps2(icache, new_deps, todos, domain)
    //         else 
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             if |metas| > 0 then
    //                 var initial := EmptyMeta(k);
    //                 assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //                 var merged := FoldMetaSet(initial, metas, domain);

    //                 lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //                 assert VCHappendsBefore(merged.vc, deps[k]) || VCEq(merged.vc, deps[k]);
    //                 assert forall kk :: kk in merged.deps ==> kk in domain;
    //                 // var updaetd := GetDeps2(icache, merged.deps, )
    //                 // var todos' := DependencyInsertOrMerge(todos, k, merged.vc);
    //                 var todos' := DependencyInsertOrMerge(todos, k, deps[k]); // this is different from TLA+ spec

    //                 assert forall kk :: kk in todos ==> kk in todos' && (VCHappendsBefore(todos[kk], todos'[kk]) || VCEq(todos[kk], todos'[kk]));

    //                 // assert VCHappendsBefore(todos'[k], deps[k]) || VCEq(todos'[k], deps[k]);

    //                 // var new_cache := RemoveElt(icache, k); // is this right?
    //                 var new_cache := icache[k:= icache[k] - metas];
    //                 assert icache[k] >= metas;
    //                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
    //                 assert |new_cache.Values| < |icache.Values|;

    //                 var res := GetDeps2(new_cache, merged.deps, todos', domain);

    //                 // assert forall kk :: kk in merged.deps ==> kk in res;
    //                 assert k in todos' && (VCHappendsBefore(deps[k], todos'[k]) || VCEq(deps[k], todos'[k]));
    //                 assert forall kk :: kk in todos' ==> kk in res;
    //                 assert k in res;
    //                 // assert forall k :: k in deps ==> k in res;

    //                 assert forall k :: k in todos' ==> k in res && (VCHappendsBefore(todos'[k], res[k]) || VCEq(todos'[k], res[k]));

    //                 // var final := DependencyMerge(todos', res);
    //                 // lemma_DependencyMergeDominatedByTheLargerOne(todos', res);
    //                 // assert final == res;
    //                 // var final := DependencyInsertOrMerge(added2, k, merged.vc);
    //                 var res' :=GetDeps2(icache, new_deps, res, domain);

    //                 assert forall kk :: kk in new_deps ==> kk in res';
    //                 assert k in res;
    //                 assert forall kk :: kk in res ==> kk in res';
    //                 assert forall kk :: kk in deps ==> kk in res' && (VCHappendsBefore(deps[k], res'[k]) || VCEq(deps[k], res'[k]));
    //                 res'
    //             else 
    //                 var todos' := DependencyInsertOrMerge(todos, k, deps[k]);
    //                 var res := GetDeps2(icache, new_deps, todos', domain);
    //                 assert forall kk :: kk in new_deps ==> kk in res;
    //                 assert forall kk :: kk in todos ==> kk in res && (VCHappendsBefore(todos[kk], res[kk]) || VCEq(todos[kk], res[kk]));
    //                 assert k in todos' && (VCHappendsBefore(deps[k], res[k]) || VCEq(deps[k], todos'[k]));
    //                 assert forall kk :: kk in todos' ==> kk in res;
    //                 assert forall kk :: kk in deps ==> kk in res && (VCHappendsBefore(deps[k], res[k]) || VCEq(deps[k], res[k]));
    //                 res
    // }
    

    // function PullDeps2(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     requires forall k :: k in ccache ==> k in icache
    //     requires DependencyValid(deps)
    //     requires forall k :: k in deps ==> k in icache // && k in ccache
    //     ensures ICacheValid(c.0)
    //     ensures CCacheValid(c.1)
    //     // ensures forall k :: k in deps ==> k in c.0 && k in c.1
    //     ensures forall k :: k in icache ==> k in c.0
    //     ensures forall k :: k in ccache ==> k in c.1
    // {
    //     var domain := icache.Keys + deps.Keys;
    //     var todos := GetDeps2(icache, deps, map[], domain);
    //     assert forall k :: k in deps ==> k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k]));
    //     lemma_GetDeps2AreMet(icache, ccache, todos);
    //     var res := PullTodos(icache, ccache, todos);
    //     assert ReadsDepsAreMet(res.0, res.1, todos);
    //     assert UponReadsDepsAreMet(res.1, deps);
    //     res
    // }

    // lemma {:axiom} lemma_CacheIsCausalCut(metas:map<Key,Meta>)
    //     requires forall k :: k in metas ==> MetaValid(metas[k])
    //     ensures forall k :: k in metas ==>
    //                 forall kk :: kk in metas[k].deps ==> kk in metas && (VCHappendsBefore(metas[k].deps[kk], metas[kk].vc) || VCEq(metas[k].deps[kk], metas[kk].vc))

    lemma {:axiom} lemma_GetMetasOfAllDeps(vc:VectorClock, todos:map<Key, Meta>)
        requires VectorClockValid(vc)
        requires forall k :: k in todos ==> MetaValid(todos[k])
        ensures forall k :: k in todos ==> VCHappendsBefore(todos[k].vc, vc) || VCEq(todos[k].vc, vc)

    function PullDeps2(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires CausalCut(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in ccache ==> k in icache
        requires DependencyValid(deps)
        requires forall k :: k in deps ==> k in icache // && k in ccache
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
        // ensures forall k :: k in deps ==> k in c.0 && k in c.1
        ensures forall k :: k in icache ==> k in c.0
        ensures forall k :: k in ccache ==> k in c.1
        ensures CausalCut(c.1)
    {
        // assume AllVersionsInCCacheAreMetInICache(icache, ccache);
        var domain := icache.Keys + deps.Keys;
        var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
        // assume forall k :: k in todos ==> 
        //     (VCHappendsBefore(todos[k].vc, deps[k]) || VCEq(todos[k].vc, deps[k]))
        //     ||
        //     (VCHappendsBefore(todos[k].vc, ccache[k].vc) || VCEq(todos[k].vc, ccache[k].vc));
        // assert forall k :: k in deps ==> k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc));
        // lemma_GetDeps2AreMet(icache, ccache, todos);
        // lemma_CacheIsCausalCut(todos);
        // assert CCacheValid(todos);
        // assert UponReadsDepsAreMet(todos, deps);
        // assume AllVersionsInCCacheAreMetInICache(icache, todos);
        var new_cache := MergeCCache(ccache, todos);
        lemma_MergeCCacheRemainsCausalCut(ccache, todos);
        // lemma_MergeCCacheEnsuresUponReadDepsAreMet(icache, ccache, todos, deps);
        // assert ReadsDepsAreMet1(icache, new_cache, todos);
        // assert UponReadsDepsAreMet(new_cache, deps);
        // lemma_MergeCCacheEnsuresAllVersionsInCCacheAreMetInICache(icache, ccache, todos);
        // assert AllVersionsInCCacheAreMetInICache(icache, new_cache);
        (icache, new_cache)
    }

    function PullDeps3(vc:VectorClock, icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires CausalCut(ccache)
        requires VectorClockValid(vc)
        requires forall k :: k in ccache ==> VCHappendsBefore(ccache[k].vc, vc) || VCEq(ccache[k].vc, vc)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in ccache ==> k in icache
        requires DependencyValid(deps)
        requires forall k :: k in deps ==> k in icache // && k in ccache
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
        // ensures forall k :: k in deps ==> k in c.0 && k in c.1
        ensures forall k :: k in icache ==> k in c.0
        ensures forall k :: k in ccache ==> k in c.1
        ensures forall k :: k in c.1 ==> VCHappendsBefore(c.1[k].vc, vc) || VCEq(c.1[k].vc, vc)
        ensures CausalCut(c.1)
    {
        // assume AllVersionsInCCacheAreMetInICache(icache, ccache);
        var domain := icache.Keys + deps.Keys;
        var todos := GetMetasOfAllDeps(icache, deps, map[], domain);
        
        lemma_GetMetasOfAllDeps(vc, todos); // this is proved in GetMetasOfAllDeps2
        assume forall k :: k in todos ==> VCHappendsBefore(todos[k].vc, vc) || VCEq(todos[k].vc, vc);

        var new_cache := MergeCCache(ccache, todos);
        lemma_MergeCCacheRemainsCausalCut(ccache, todos);
        lemma_MergeCCacheSmallerThanPVC(vc, ccache, todos);
        assert forall k :: k in new_cache ==> VCHappendsBefore(new_cache[k].vc, vc) || VCEq(new_cache[k].vc, vc);
        // lemma_MergeCCacheEnsuresUponReadDepsAreMet(icache, ccache, todos, deps);
        // assert ReadsDepsAreMet1(icache, new_cache, todos);
        // assert UponReadsDepsAreMet(new_cache, deps);
        // lemma_MergeCCacheEnsuresAllVersionsInCCacheAreMetInICache(icache, ccache, todos);
        // assert AllVersionsInCCacheAreMetInICache(icache, new_cache);
        (icache, new_cache)
    }

    // lemma {:axiom} lemma_GetDeps2AreMet(icache:ICache, ccache:CCache, todos:map<Key, Meta>)
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall k :: k in todos ==> k in Keys_domain && MetaValid(todos[k])
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     ensures ReadsDepsAreMet1(icache, ccache, todos)

    // lemma {:axiom} lemma_GetDeps2AreMet(icache:ICache, ccache:CCache, todos:Dependency)
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires DependencyValid(todos)
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     ensures ReadsDepsAreMet(icache, ccache, todos)


    function FoldMetaIntoICache(icache: ICache, metas: set<Meta>): ICache
        requires ICacheValid(icache)
        requires forall m :: m in metas ==> MetaValid(m) && (forall kk :: kk in m.deps ==> kk in Keys_domain && kk in icache)
        decreases |metas|
    {
        if metas == {} then 
            icache
        else 
            var m: Meta :| m in metas;
            FoldMetaIntoICache(AddMetaToICache(icache, m), metas - {m})
    }


    function AdvanceVC(vc:VectorClock, i:int) : (res:VectorClock)
        requires VectorClockValid(vc)
        requires 0 <= i < Nodes 
        ensures VectorClockValid(res)
    {
        vc[i:=vc[i]+1]
    }


    


    /** Actions */
    datatype Server = Server(
        id : int,
        gvc : VectorClock,
        next : int,
        icache : ICache,
        ccache : CCache,
        ghost pvc : VectorClock
    )

    predicate ServerValid(s:Server)
    {
        && 0 <= s.id < Nodes
        && 0 <= s.next < Nodes
        && s.next == Circle(s.id, Nodes)
        && VectorClockValid(s.gvc)
        && VectorClockValid(s.pvc)
        && ICacheValid(s.icache)
        && CCacheValid(s.ccache)
        && CausalCut(s.ccache)
        && (forall k :: k in s.ccache ==> VCHappendsBefore(s.ccache[k].vc, s.pvc) || VCEq(s.ccache[k].vc, s.pvc))
        && (forall k :: k in Keys_domain ==> k in s.icache && k in s.ccache)
        && (forall k :: k in s.ccache ==> k in s.icache)
    }


    function InitICache(): ICache
    {
        map k | k in Keys_domain :: {EmptyMeta(k)}
    }

    function InitCCache(): CCache
    {
        map k | k in Keys_domain :: EmptyMeta(k)
    }

    predicate ServerInit(s:Server, id:int)
        requires 0 <= id < Nodes
    {
        && s.id == id
        && s.next == Circle(id, Nodes)
        && s.gvc == EmptyVC()
        && s.pvc == EmptyVC()
        && s.icache == InitICache()
        && s.ccache == InitCCache()
    }

    predicate ReceiveRead(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Read?
        requires ServerValid(s)
        requires PacketValid(p)
        // ensures ServerValid(s')
    {
        assume forall k :: k in s.ccache ==> VCHappendsBefore(s.ccache[k].vc, s.pvc) || VCEq(s.ccache[k].vc, s.pvc);
        var new_pvc := if (VCHappendsBefore(p.msg.pvc_read, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.pvc_read);
        // var (new_icache, new_ccache) := PullDeps2(s.icache, s.ccache, p.msg.deps_read);
        var (new_icache, new_ccache) := PullDeps3(new_pvc, s.icache, s.ccache, p.msg.deps_read);
        assert forall k :: k in new_ccache ==> VCHappendsBefore(new_ccache[k].vc, new_pvc) || VCEq(new_ccache[k].vc, new_pvc);
        && s' == s.(icache := new_icache, ccache := new_ccache, pvc := new_pvc)
        && sp == [LPacket(s.id, p.src, 
                        Message_Read_Reply(
                            p.msg.opn_read,
                            p.msg.key_read,
                            new_ccache[p.msg.key_read].vc,
                            new_ccache[p.msg.key_read].deps,
                            new_pvc
                        )
                    )]
    }

    // predicate ReceiveWrite(s:Server, s':Server, p:Packet, sp:seq<Packet>)
    //     requires p.msg.Message_Write?
    //     requires ServerValid(s)
    //     requires PacketValid(p)
    // {
    //     var new_vc := AdvanceVC(s.gvc, s.id);
    //     var meta := Meta(p.msg.key_write, new_vc, p.msg.deps_write);
    //     var local := set m | m in p.msg.local.Values;
    //     var new_icache := s.icache[p.msg.key_write := s.icache[p.msg.key_write] + local + {meta}];
    //     var wreply := LPacket(s.id, p.src, Message_Write_Reply(p.msg.key_write, new_vc));
    //     var propagate := LPacket(s.id, s.next, Message_Propagation(p.msg.key_write, {meta}, s.id));
    //     && s' == s.(gvc:=new_vc, icache := new_icache)
    //     && sp == [wreply] + [propagate]
    // }

    // function ConstructPropagatePkts(metas:set<Meta>, id:int, dst:int) : (res:seq<Packet>)
    //     requires forall m :: m in metas ==> MetaValid(m)
    //     requires 0 <= id < Nodes
    //     requires 0 <= dst < Nodes
    //     ensures |res| == |metas|
    //     ensures forall p :: p in res ==> p.msg.Message_Propagation? && p.src == id && p.dst == dst
    // {
    //     if |metas| == 0 then
    //         []
    //     else 
    //         var m :| m in metas;
    //         var new_metas := metas - {m};
    //         var propagate := LPacket(id, dst, Message_Propagation(m.key, m, id));
    //         assert propagate.dst == dst;
    //         [propagate] + ConstructPropagatePkts(new_metas, id, dst)
    // }

    predicate ReceiveWrite(s: Server, s': Server, p: Packet, sp: seq<Packet>)
        requires p.msg.Message_Write?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
        var local_metas := set m | m in p.msg.local.Values;
        assert forall m :: m in local_metas ==> MetaValid(m);
        var vcs_local := set m | m in local_metas :: m.vc;
        // assert forall vc :: vc in vcs ==> VectorClockValid(vc);
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

        // assert forall m :: m in new_local_metas ==> MetaValid(m);

        var new_icache := AddMetasToICache(s.icache, new_local_metas);
        
        var new_pvc := if (VCHappendsBefore(p.msg.pvc_write, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.pvc_write);

        var wreply := LPacket(s.id, p.src, Message_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc, new_pvc));
        var propagate := LPacket(s.id, s.next, Message_Propagation(p.msg.key_write, meta, s.id, 1));
        // var old_propagates := ConstructPropagatePkts(local_metas, s.id, s.next);

        
        && s' == s.(gvc := new_vc, icache := new_icache, pvc := new_pvc)
        && sp == [wreply] /*+ old_propagates*/ + [propagate]
    }


    lemma lemma_VCRelationIsTransitive2(deps:Dependency, metas:set<Meta>, vc:VectorClock, vc2:VectorClock)
        requires DependencyValid(deps)
        requires forall m :: m in metas ==> MetaValid(m)
        requires VectorClockValid(vc)
        requires VectorClockValid(vc2)
        requires forall m :: m in metas ==> VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc)
        requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
        requires VCHappendsBefore(vc, vc2) || VCEq(vc, vc2)
        ensures forall m :: m in metas ==> VCHappendsBefore(m.vc, vc2) || VCEq(m.vc, vc2)
        ensures forall k :: k in deps ==> VCHappendsBefore(deps[k], vc2) || VCEq(deps[k], vc2)
    {

    }





    predicate ReceivePropagate(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Propagation?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        if s.next == p.msg.start then
            if p.msg.round == 2 then
                var vcs := p.msg.meta.vc;
                var new_gvc := VCMerge(s.gvc, vcs);
                var new_deps := p.msg.meta.deps;

                assume forall k :: k in s.ccache ==> VCHappendsBefore(s.ccache[k].vc, s.pvc) || VCEq(s.ccache[k].vc, s.pvc);
                var new_pvc := if (VCHappendsBefore(p.msg.meta.vc, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.meta.vc);

                var (new_icache, new_ccache) := PullDeps3(new_pvc, s.icache, s.ccache, new_deps);

                // var merged_meta := FoldMetaSet2(new_ccache[p.msg.key], p.msg.metas);
                // var merged_meta := MetaMerge(new_ccache[p.msg.key], p.msg.meta);

                assert forall k :: k in new_ccache ==> VCHappendsBefore(new_ccache[k].vc, new_pvc) || VCEq(new_ccache[k].vc, new_pvc);

                var new_ccache' := InsertIntoCCache(new_ccache, p.msg.meta);
                var new_icache' := AddMetaToICache(new_icache, p.msg.meta);

                assert forall k :: k in new_ccache' && k != p.msg.meta.key ==> k in new_ccache && VCEq(new_ccache[k].vc, new_ccache'[k].vc);
                assert if p.msg.meta.key in new_ccache then new_ccache'[p.msg.meta.key].vc == VCMerge(p.msg.meta.vc, new_ccache[p.msg.meta.key].vc)  else new_ccache'[p.msg.meta.key].vc == p.msg.meta.vc;

                // assert forall k :: k in new_ccache ==> k in new_ccache' && (VCHappendsBefore(new_ccache[k].vc, new_ccache'[k].vc) || VCEq(new_ccache[k].vc, new_ccache'[k].vc));
                assert VCHappendsBefore(p.msg.meta.vc, new_pvc) || VCEq(p.msg.meta.vc, new_pvc);
                assert forall k :: k in new_ccache' && k != p.msg.meta.key ==> VCHappendsBefore(new_ccache'[k].vc, new_pvc) || VCEq(new_ccache'[k].vc, new_pvc);
                assert new_ccache'[p.msg.meta.key].vc == VCMerge(p.msg.meta.vc, new_ccache[p.msg.meta.key].vc);
                assert VCHappendsBefore(VCMerge(p.msg.meta.vc, new_ccache[p.msg.meta.key].vc), new_pvc) || VCEq(VCMerge(p.msg.meta.vc, new_ccache[p.msg.meta.key].vc), new_pvc);
                assert forall k :: k in new_ccache' ==> VCHappendsBefore(new_ccache'[k].vc, new_pvc) || VCEq(new_ccache'[k].vc, new_pvc);

                && s' == s.(gvc := new_gvc, icache := new_icache', ccache := new_ccache', pvc := new_pvc)
                && sp == []
            else
                var new_icache := AddMetaToICache(s.icache, p.msg.meta);
                && s' == s.(icache := new_icache)
                && sp == [LPacket(s.id, s.next, p.msg.(round := 2))]
        else 
            // var new_icache := FoldMetaIntoICache(s.icache, p.msg.metas);
            var new_icache := AddMetaToICache(s.icache, p.msg.meta);
            && s' == s.(icache := new_icache)
            && sp == [LPacket(s.id, s.next, p.msg)]
    }


    /** Client */
    datatype Client = Client(
        id : int,
        opn : int,
        local : map<Key, Meta>,
        deps : Dependency,
        ghost pvc : VectorClock
    )

    predicate ClientValid(c:Client)
    {
        && Nodes <= c.id < Nodes + Clients
        && (forall k :: k in c.local ==> k in Keys_domain && MetaValid(c.local[k]) && c.local[k].key == k)
        && DependencyValid(c.deps)
        && VectorClockValid(c.pvc)
    }

    predicate ClientInit(c:Client, id:int)
        requires Nodes <= id < Nodes + Clients
    {
        && c.opn == 0
        && c.id == id
        && c.local == map[]
        && c.deps == map[]
        && c.pvc == EmptyVC()
    }

    predicate SendRead(c:Client, c':Client, sp:seq<Packet>)
        requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        
        if k in c.local then 
            && c' == c.(opn := c.opn + 1)
            && sp == []
        else 
            var server :| 0 <= server < Nodes as int;
            && c' == c.(opn := c.opn + 1)
            && sp == [LPacket(c.id, server, Message_Read(c.opn, k, c.deps, c.pvc))]
    }

    predicate ReceiveReadReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires ClientValid(c)
        requires p.msg.Message_Read_Reply?
        requires PacketValid(p)
        // requires p.msg.opn_rreply == c.opn
    {
        var m := Meta(p.msg.key_rreply, p.msg.vc_rreply, p.msg.deps_rreply);
        var new_pvc := if (VCHappendsBefore(p.msg.pvc_rreply, c.pvc)) then c.pvc else VCMerge(c.pvc, p.msg.pvc_rreply);

        && c' == c.(/*local := c.local[p.msg.key_rreply := m],*/ deps := DependencyInsertOrMerge(c.deps, p.msg.key_rreply, p.msg.vc_rreply), pvc := new_pvc)
        && sp == []
    }

    predicate SendWrite(c:Client, c':Client, sp:seq<Packet>)
        // requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        var server :| 0 <= server < Nodes as int;
        && c' == c.(opn := c.opn + 1)
        && sp == [LPacket(c.id, server, Message_Write(c.opn + 1, k, c.deps, c.local, c.pvc))]
    }

    predicate ReceiveWriteReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires ClientValid(c)
        requires p.msg.Message_Write_Reply?
        requires PacketValid(p)
    {
        var k := p.msg.key_wreply;
        var vc := p.msg.vc_wreply;
        var new_pvc := if (VCHappendsBefore(p.msg.pvc_wreply, c.pvc)) then c.pvc else VCMerge(c.pvc, p.msg.pvc_wreply);

        var m := Meta(k, vc, c.deps);
        && c' == c.(local := c.local[k := m], pvc := new_pvc)
        && sp == []
    }

    function ExtractSentPacketsFromIos(ios:seq<CMIo>) : seq<Packet>
        ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
    {
        if |ios| == 0 then
            []
        else if ios[0].LIoOpSend? then
            [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
        else
            ExtractSentPacketsFromIos(ios[1..])
    }

    predicate ServerProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
        requires ServerValid(s)
        requires |ios| >= 1
        requires ios[0].LIoOpReceive?
        requires PacketValid(ios[0].r)
        requires var msg := ios[0].r.msg; 
                msg.Message_Read? || msg.Message_Write? || msg.Message_Propagation?
    {
        && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
        && var sent_packets := ExtractSentPacketsFromIos(ios);
            match ios[0].r.msg 
                case Message_Read(_,_,_,_) => ReceiveRead(s, s', ios[0].r, sent_packets)
                case Message_Write(_,_,_,_,_) => ReceiveWrite(s, s', ios[0].r, sent_packets)
                case Message_Propagation(_,_,_,_) => ReceivePropagate(s, s', ios[0].r, sent_packets)
    }

    // predicate NextProcessPacket(s:Server, s':Server, c:Client, c':Client, ios:seq<CMIo>)
    //     requires ServerValid(s)
    //     requires ClientValid(c)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //         else
    //         (&& ios[0].LIoOpReceive?
    //         && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
    //             ServerProcessPacket(s, s', ios)
    //            else
    //             ClientProcessPacket(c, c', ios)
    //         )
    // }

    predicate ServerNextProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
        requires ServerValid(s)
    {
        && |ios| >= 1
        && if ios[0].LIoOpTimeoutReceive? then
            s' == s && |ios| == 1
           else
            (&& ios[0].LIoOpReceive?
             && PacketValid(ios[0].r)
            && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
                ServerProcessPacket(s, s', ios)
               else
                s' == s && |ios| == 1
            )
    }

    datatype LServer = LServer(s:Server)

    predicate LServerInit(s:LServer, id:int)
        requires 0 <= id < Nodes
    {
        && ServerInit(s.s, id)
        // && s.nextActionIndex == 0
    }

    predicate LServerNext(s:LServer, s':LServer, ios:seq<CMIo>)
    {
        && ServerValid(s.s)
        && ServerNextProcessPacket(s.s, s'.s, ios)
    }


    predicate ClientProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
        requires ClientValid(s)
        requires |ios| >= 1
        requires ios[0].LIoOpReceive?
        requires PacketValid(ios[0].r)
        requires var msg := ios[0].r.msg;
                msg.Message_Read_Reply? || msg.Message_Write_Reply?
    {
        && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
        && var sent_packets := ExtractSentPacketsFromIos(ios);
            match ios[0].r.msg 
                case Message_Read_Reply(_,_,_,_,_) => ReceiveReadReply(s, s', ios[0].r, sent_packets)
                case Message_Write_Reply(_,_,_,_) => ReceiveWriteReply(s, s', ios[0].r, sent_packets)
    }

    predicate ClientNextProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
        requires ClientValid(s)
    {
        && |ios| >= 1
        && if ios[0].LIoOpTimeoutReceive? then
            s' == s && |ios| == 1
           else
            (&& ios[0].LIoOpReceive?
            && PacketValid(ios[0].r)
            && if ios[0].r.msg.Message_Read_Reply? || ios[0].r.msg.Message_Write_Reply? then
                ClientProcessPacket(s, s', ios)
               else
                s' == s && |ios| == 1
            )
    }

    predicate SpontaneousIos(ios:seq<CMIo>, clocks:int)
        requires 0<=clocks<=1
    {
        && clocks <= |ios|
        && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
        && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
    }

    predicate ClientNoReceiveNext(s:Client, s':Client, nextActionIndex:int, ios:seq<CMIo>)
        requires ClientValid(s)
    {
        var sent_packets := ExtractSentPacketsFromIos(ios);

        if nextActionIndex == 1 then 
            && SpontaneousIos(ios, 0)
            && SendRead(s, s', sent_packets)
        else 
            && nextActionIndex == 2
            && SpontaneousIos(ios, 0)
            && SendWrite(s, s', sent_packets)
    }

    datatype LClient = LClient(c:Client, nextActionIndex:int)

    predicate LClientInit(s:LClient, id:int)
        requires Nodes <= id < Nodes + Clients
    {
        && ClientInit(s.c, id)
        && s.nextActionIndex == 0
    }

    predicate LClientNext(s:LClient, s':LClient, ios:seq<CMIo>)
    {
        && ClientValid(s.c)
        && s'.nextActionIndex == (s.nextActionIndex + 1) % 3
        && if s.nextActionIndex == 0 then 
            ClientNextProcessPacket(s.c, s'.c, ios)
           else 
            ClientNoReceiveNext(s.c, s'.c, s.nextActionIndex, ios)
    }

}