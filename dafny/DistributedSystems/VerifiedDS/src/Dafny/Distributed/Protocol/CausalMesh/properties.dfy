include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"

module CausalMesh_Properties_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    
    /** Key Properties */

    predicate CausalCut(ccache: CCache)
        // requires CCacheValid(ccache)
        requires forall k :: k in ccache ==> MetaValid(ccache[k])
    {
        forall k :: k in ccache ==>
            forall kk :: kk in ccache[k].deps ==>
                kk in ccache &&
                (VCHappendsBefore(ccache[k].deps[kk], ccache[kk].vc) || VCEq(ccache[k].deps[kk], ccache[kk].vc))
    }

    predicate AVersionOfAKeyIsMet(icache:ICache, ccache:CCache, k:Key, vc:VectorClock)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires k in Keys_domain
        requires VectorClockValid(vc)
    {
        var m := FoldMetaSet2(ccache[k], icache[k]);
        VCEq(vc, m.vc) || VCHappendsBefore(vc, m.vc)
        // exists m :: m in icache[k] && VCEq(m.vc, vc)
    }

    // lemma lemma_MergedVCIsMet(icache:ICache, ccache:CCache, k:Key, vc1:VectorClock, vc2:VectorClock)
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     requires k in Keys_domain
    //     requires VectorClockValid(vc1)
    //     requires VectorClockValid(vc2)
    //     requires AVersionOfAKeyIsMet(icache, ccache, k, vc1)
    //     requires AVersionOfAKeyIsMet(icache, ccache, k, vc2)
    //     ensures AVersionOfAKeyIsMet(icache, ccache, k, VCMerge(vc1, vc2))
    // {

    // }

    predicate {:opaque} DepsIsMet(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> AVersionOfAKeyIsMet(icache, ccache, k, deps[k])
    }

    predicate VersionIsMetOnAllServers(k:Key, vc:VectorClock)
    {
        true
    }

    lemma lemma_VersionIsMetOnAllServersImpliesAllSmallerVersionsAreMet(k:Key, vc:VectorClock, vc2:VectorClock)
        requires VersionIsMetOnAllServers(k, vc)
        requires VectorClockValid(vc)
        requires VectorClockValid(vc2)
        requires VCHappendsBefore(vc2, vc) || VCEq(vc2, vc)
        ensures VersionIsMetOnAllServers(k, vc2)
    {

    }

    predicate DepsInICacheAreMetOnAllServers(icache:ICache)
    {
        forall k :: k in icache ==>
            forall m :: m in icache[k] ==> 
                forall kk :: kk in m.deps ==> VersionIsMetOnAllServers(kk, m.deps[kk])
    }

    predicate DepsInCCacheAreMetOnAllServers(
        ccache:CCache
    )
    {
        forall k :: k in ccache ==>
            forall kk :: kk in ccache[k].deps ==> VersionIsMetOnAllServers(kk, ccache[k].deps[kk])
    }

    predicate VersionsInDepsAreMetOnAllServers(
        deps:Dependency
    )
    {
        forall k :: k in deps ==> VersionIsMetOnAllServers(k, deps[k])
    }

    predicate ReadsDepsAreMet2(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            var m := FoldMetaSet(ccache[k], icache[k], icache.Keys);
            VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
    }

    predicate ReadsDepsAreMet(icache:ICache, ccache:CCache, deps:Dependency)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            (VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc))
            || (exists m :: m in icache[k] && m.vc == deps[k])
            // var m := FoldMetaSet(ccache[k], icache[k], icache.Keys);
            // VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
    }

    predicate ReadsDepsAreMet1(icache:ICache, ccache:CCache, deps:map<Key, Meta>)
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in deps ==> k in Keys_domain && MetaValid(deps[k])
    {
        forall k :: k in deps ==> 
            (VCEq(deps[k].vc, ccache[k].vc) || VCHappendsBefore(deps[k].vc, ccache[k].vc))
            || (exists m :: m in icache[k] && m.vc == deps[k].vc)
    }

    predicate UponReadsDepsAreMet(ccache:CCache, deps:Dependency)
        requires CCacheValid(ccache)
        // requires forall k :: k in Keys_domain ==> k in ccache
        requires forall k :: k in deps ==> k in ccache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==> 
            VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc)
    }

    predicate DepsAreMetInICache(icache:ICache, deps:Dependency)
        requires forall k :: k in Keys_domain ==> k in icache
        requires DependencyValid(deps)
    {
        forall k :: k in deps ==>
            exists m :: m in icache[k] && m.vc == deps[k]
    }

    predicate AllVersionsInCCacheAreMetInICache(icache:ICache, ccache:CCache)
        requires forall k :: k in Keys_domain ==> k in icache
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
    {
        && (forall k :: k in ccache ==> exists m :: m in icache[k] && ccache[k].vc == m.vc)
        && (forall k :: k in ccache ==> 
                forall kk :: kk in ccache[k].deps ==>
                    exists m :: m in icache[k] && ccache[k].deps[kk] == m.vc)
    }
    
    lemma lemma_MergeCCacheRemainsCausalCut(c1:CCache, c2:CCache)
        requires CCacheValid(c1)
        requires CCacheValid(c2)
        requires CausalCut(c1)
        requires CausalCut(c2)
        ensures CCacheValid(MergeCCache(c1,c2))
        ensures CausalCut(MergeCCache(c1,c2))
    {
        // map k | k in c1.Keys + c2.Keys ::
        //     if k in c1 && k in c2 then
        //         MetaMerge(c1[k], c2[k])
        //     else if k in c1 then
        //         c1[k]
        //     else
        //         c2[k]
    }

    lemma lemma_MergeCCacheSmallerThanPVC(vc:VectorClock, c1:CCache, c2:CCache)
        requires CCacheValid(c1)
        requires CCacheValid(c2)
        requires VectorClockValid(vc)
        requires forall k :: k in c1 ==> VCHappendsBefore(c1[k].vc, vc) || VCEq(c1[k].vc, vc)
        requires forall k :: k in c2 ==> VCHappendsBefore(c2[k].vc, vc) || VCEq(c2[k].vc, vc)
        ensures CCacheValid(MergeCCache(c1,c2))
        ensures var res := MergeCCache(c1,c2);
                forall k :: k in res ==> VCHappendsBefore(res[k].vc, vc) || VCEq(res[k].vc, vc)
    {
        // map k | k in c1.Keys + c2.Keys ::
        //     if k in c1 && k in c2 then
        //         MetaMerge(c1[k], c2[k])
        //     else if k in c1 then
        //         c1[k]
        //     else
        //         c2[k]
    }

    lemma lemma_MergeCCacheEnsuresReadDepsAreMet(icache:ICache, c1:CCache, todos:map<Key, Meta>)
        requires CCacheValid(c1)
        requires CCacheValid(todos)
        requires ICacheValid(icache)
        requires forall k :: k in Keys_domain ==> k in icache && k in c1
        requires forall k :: k in todos ==> k in Keys_domain && MetaValid(todos[k])
        // requires CausalCut(c1)
        // requires CausalCut(c2)
        requires ReadsDepsAreMet1(icache, c1, todos)
        ensures CCacheValid(MergeCCache(c1,todos))
        // ensures CausalCut(MergeCCache(c1,c2))
        ensures ReadsDepsAreMet1(icache, MergeCCache(c1,todos), todos)
        ensures var res := MergeCCache(c1, todos);
                && (forall k :: k in c1 ==> k in res && (VCHappendsBefore(c1[k].vc, res[k].vc) || VCEq(c1[k].vc, res[k].vc)))
                && (forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc)))
    {
        // map k | k in c1.Keys + c2.Keys ::
        //     if k in c1 && k in c2 then
        //         MetaMerge(c1[k], c2[k])
        //     else if k in c1 then
        //         c1[k]
        //     else
        //        jfakj
    }

    lemma lemma_MergeCCacheEnsuresUponReadDepsAreMet(icache:ICache, ccache:CCache, todos:map<Key, Meta>, deps:Dependency)
        requires CCacheValid(ccache)
        requires CCacheValid(todos)
        requires ICacheValid(icache)
        requires DependencyValid(deps)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in deps ==> k in todos
        requires forall k :: k in todos ==> k in Keys_domain && MetaValid(todos[k])
        requires UponReadsDepsAreMet(todos, deps)
        ensures var res := MergeCCache(ccache, todos);
                && (forall k :: k in ccache ==> k in res && (VCHappendsBefore(ccache[k].vc, res[k].vc) || VCEq(ccache[k].vc, res[k].vc)))
                && (forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc)))
                && UponReadsDepsAreMet(res, deps)
    {

    }

    // lemma lemma_MergeCCacheEnsuresAllVersionsInCCacheAreMetInICache(icache:ICache, ccache:CCache, todos:map<Key, Meta>)
    //     requires CCacheValid(ccache)
    //     requires CCacheValid(todos)
    //     requires ICacheValid(icache)
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     requires AllVersionsInCCacheAreMetInICache(icache, ccache)
    //     requires AllVersionsInCCacheAreMetInICache(icache, todos)
    //     // ensures AllVersionsInCCacheAreMetInICache(icache, MergeCCache(ccache, todos))
    // {
    //     var new_cache := MergeCCache(ccache, todos);
    //     assert forall k :: k in ccache ==> exists m :: m in icache[k] && ccache[k].vc == m.vc;
    //     assert forall k :: k in todos ==> exists m :: m in icache[k] && todos[k].vc == m.vc;
    // }


}