include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
// include "deps_are_met.dfy"
// include "monotonic_read.dfy"
include "../../../Common/Collections/Seqs.s.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module CausalMesh_Proof_AllwaysMet_i {
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
// import opened CausalMesh_Proof_DepsAreMet_i
// import opened CausalMesh_Proof_Monotonic_Read_i
// import opened CausalMesh_Proof_Environment_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s
import opened Collections__Sets_i

lemma lemma_AVersionIsMetWillAlwaysMet(
    i1:ICache,
    i2:ICache,
    c1:CCache,
    c2:CCache,
    k:Key,
    vc:VectorClock
)
    requires ICacheValid(i1)
    requires ICacheValid(i2)
    requires CCacheValid(c1)
    requires CCacheValid(c2)
    requires ICacheDoesNotDecrease(i1, i2)
    requires CCacheDoesNotDecrease(c1, c2)
    requires forall k :: k in Keys_domain ==> k in i1 && k in i2 && k in c1 && k in c2
    requires k in Keys_domain
    requires VectorClockValid(vc)
    requires AVersionOfAKeyIsMet(i1, c1, k, vc)
    ensures AVersionOfAKeyIsMet(i2, c2, k, vc)
{
    assert forall k :: k in i1 ==> k in i2 && forall m :: m in i1[k] ==> m in i2[k];
    assert i1[k] <= i2[k];
    assert forall k :: k in c1 ==> k in c2 && (VCHappendsBefore(c1[k].vc, c2[k].vc) || VCEq(c1[k].vc, c2[k].vc));
    var m1 := FoldMetaSet2(c1[k], i1[k]);
    var m1b := FoldMetaSet2(c2[k], i1[k]);
    var m2 := FoldMetaSet2(c2[k], i2[k]);

    lemma_FoldMetaSet2_AccMonotonicity(c1[k], c2[k], i1[k]);
    lemma_FoldMetaSet2_MetasMonotonicity2(c2[k], i1[k], i2[k]);
    assert VCEq(m1.vc, m1b.vc) || VCHappendsBefore(m1.vc, m1b.vc);
    assert VCEq(m1b.vc, m2.vc) || VCHappendsBefore(m1b.vc, m2.vc);

    assert VCEq(m1.vc, m2.vc) || VCHappendsBefore(m1.vc, m2.vc);
}





lemma lemma_FoldMetaSet2_MetasMonotonicity2(
    acc: Meta,
    metas1: set<Meta>,
    metas2: set<Meta>
)
    requires MetaValid(acc)
    requires forall m :: m in metas1 ==> MetaValid(m) && m.key == acc.key
    requires forall m :: m in metas2 ==> MetaValid(m) && m.key == acc.key
    requires metas1 <= metas2
    ensures var r1 := FoldMetaSet2(acc, metas1);
            var r2 := FoldMetaSet2(acc, metas2);
            VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc)
    decreases |metas2 - metas1|
{
    var r1 := FoldMetaSet2(acc, metas1);
    var r2 := FoldMetaSet2(acc, metas2);
    if metas2 == metas1 {
        assert VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc);
    } 
    else if |metas2 - metas1| == 1 
    {
        var x :| x in metas2 - metas1;
        var rr2 := FoldMetaSet2(acc, metas1 + {x});
        lemma_AddSingletonRestoresSet(metas2, metas1, x);
        assert metas1 + {x} == metas2;
        assert r2 == rr2;
        lemma_FoldMetaSet2_OneMoreMeta(acc, metas1, x);
        assert VCEq(r1.vc, rr2.vc) || VCHappendsBefore(r1.vc, rr2.vc);
        assert VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc);
    }
    else {
        var x :| x in metas2 - metas1;
        var rr2 := FoldMetaSet2(acc, metas1 + {x});
        assert metas1 <= metas1 + {x};
        assert forall m :: m in metas1 ==> MetaValid(m) && m.key == acc.key;
        assert forall m :: m in metas1+{x} ==> MetaValid(m) && m.key == acc.key;
        // assert |metas1 + {x}| > |metas1|;
        // assert metas1+{x} <= metas2;
        assert |metas1+{x} - metas1| < |metas2 - metas1|;
        // assert |metas2 - metas1+{x}| < |metas2 - metas1|;

        lemma_FoldMetaSet2_MetasMonotonicity2(acc, metas1, metas1+{x});
        assert VCEq(r1.vc, rr2.vc) || VCHappendsBefore(r1.vc, rr2.vc);

        assert rr2 == FoldMetaSet2(acc, metas1+{x});
        assert r2 == FoldMetaSet2(acc, metas2);
        lemma_FoldMetaSet2_MetasMonotonicity2(acc, metas1 + {x}, metas2);
        assert VCEq(FoldMetaSet2(acc, metas1+{x}).vc, FoldMetaSet2(acc, metas2).vc) ||
                VCHappendsBefore(FoldMetaSet2(acc, metas1+{x}).vc, FoldMetaSet2(acc, metas2).vc);
        assert VCEq(rr2.vc, r2.vc) || VCHappendsBefore(rr2.vc, r2.vc);

        assert VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc);
    }
}


// lemma lemma_MeteMergeDoesNotDecreaseVC(
//     m1:Meta,
//     m2:Meta
// )
//     requires MetaValid(m1)
//     requires MetaValid(m2)
//     requires m1.key == m2.key
//     ensures var r := MetaMerge(m1, m2);
//             (VCHappendsBefore(m1.vc, r.vc) || VCEq(m1.vc, r.vc))
//             && (VCHappendsBefore(m2.vc, r.vc) || VCEq(m2.vc, r.vc))
// {

// }

lemma lemma_FoldMetaSet2_OneMoreMeta(
    acc:Meta,
    metas:set<Meta>,
    m:Meta
)
    requires MetaValid(acc)
    requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key
    requires MetaValid(m) && m.key == acc.key
    ensures var r1 := FoldMetaSet2(acc, metas);
            var r2 := FoldMetaSet2(acc, metas + {m});
            VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc)
    decreases |metas|
{
    var r1 := FoldMetaSet2(acc, metas);
    var r2 := FoldMetaSet2(r1, {m});
    lemma_FoldMetaSet2_Decompose(acc, metas, m);
    assert r2 == FoldMetaSet2(acc, metas + {m});
    // if |metas| == 0 {
    //     var r1 := FoldMetaSet2(acc, metas);
    //     assert r1 == acc;

    //     assert metas + {m} == {m};
    //     var r2 := FoldMetaSet2(acc, metas + {m});
    //     assume r2 == MetaMerge(acc, m);
    //     assert VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc);
    // } else {
    //     var x :| x in metas;
    //     var metas' := metas - {x};
    //     var acc' := MetaMerge(acc, x);

    //     lemma_FoldMetaSet2_OneMoreMeta(acc', metas', m);
    //     var rec_r1 := FoldMetaSet2(acc', metas');
    //     var rec_r2 := if m in metas' then rec_r1 else FoldMetaSet2(acc', metas' + {m});
    //     assert VCEq(rec_r1.vc, rec_r2.vc) || VCHappendsBefore(rec_r1.vc, rec_r2.vc);
    // }
}


lemma lemma_FoldMetaSet2_AccMonotonicity(
    acc1: Meta,
    acc2: Meta,
    metas: set<Meta>
)
    requires MetaValid(acc1)
    requires MetaValid(acc2)
    requires acc1.key == acc2.key
    requires forall m :: m in metas ==> MetaValid(m) && m.key == acc1.key
    requires VCEq(acc1.vc, acc2.vc) || VCHappendsBefore(acc1.vc, acc2.vc)
    ensures var r1 := FoldMetaSet2(acc1, metas);
            var r2 := FoldMetaSet2(acc2, metas);
            VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc)
    decreases |metas|
{
    if |metas| == 0 {
        // Base case: FoldMetaSet2(acc, {}) = acc
        assert VCEq(acc1.vc, acc2.vc) || VCHappendsBefore(acc1.vc, acc2.vc);
    } else {
        var x :| x in metas;
        // Induction
        lemma_FoldMetaSet2_AccMonotonicity(
            MetaMerge(acc1, x),
            MetaMerge(acc2, x),
            metas - {x}
        );
    }
}


// lemma lemma_FoldMetaSet2_AccMonotonicity(
//     acc1: Meta,
//     acc2: Meta,
//     metas: set<Meta>
// )
//     requires MetaValid(acc1)
//     requires MetaValid(acc2)
//     requires acc1.key == acc2.key
//     requires forall m :: m in metas ==> MetaValid(m) && m.key == acc1.key
//     requires VCEq(acc1.vc, acc2.vc) || VCHappendsBefore(acc1.vc, acc2.vc)
//     ensures var r1 := FoldMetaSet2(acc1, metas);
//             var r2 := FoldMetaSet2(acc2, metas);
//             VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc)
//     decreases |metas|
// {
//     var r1 := FoldMetaSet2(acc1, metas);
//     var r2 := FoldMetaSet2(acc2, metas);

//     if |metas| == 0 {
//         assert VCEq(acc1.vc, acc2.vc) || VCHappendsBefore(acc1.vc, acc2.vc);
//         assert VCEq(r1.vc, r2.vc) || VCHappendsBefore(r1.vc, r2.vc);
//     } 
//     else {
//         var x :| x in metas;
//         // Induction
//         lemma_FoldMetaSet2_AccMonotonicity(
//             MetaMerge(acc1, x),
//             MetaMerge(acc2, x),
//             metas - {x}
//         );
//         // var rr1 := FoldMetaSet2(acc1, metas-{x});
//         // var rr2 := FoldMetaSet2(acc2, metas-{x});
//     }
// }




lemma lemma_DepsIsMetWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    deps:Dependency
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires 0 <= idx < Nodes
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires DependencyValid(deps)
    requires DepsIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, deps)
    ensures DepsIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, deps)
{
    reveal_DepsIsMet();
    forall k | k in deps 
        ensures AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, k, deps[k])
    {
        assert AVersionOfAKeyIsMet(b[i-1].servers[idx].s.icache, b[i-1].servers[idx].s.ccache, k, deps[k]);
        lemma_AVersionIsMetWillAlwaysMet(
            b[i-1].servers[idx].s.icache,
            b[i].servers[idx].s.icache,
            b[i-1].servers[idx].s.ccache,
            b[i].servers[idx].s.ccache,
            k, deps[k]
        );
        assert AVersionOfAKeyIsMet(b[i].servers[idx].s.icache, b[i].servers[idx].s.ccache, k, deps[k]);
    }
}

lemma lemma_AVersionIsMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    k:Key,
    vc:VectorClock
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    requires CMNext(b[i-2], b[i-1])
    requires k in Keys_domain
    requires VectorClockValid(vc)
    requires AVersionIsMetOnAllServers(b, i-1, k, vc)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    ensures AVersionIsMetOnAllServers(b, i, k, vc)
{
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
    forall j | 0 <= j < |b[i].servers| 
        ensures AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc)
    {
        assert AVersionOfAKeyIsMet(b[i-1].servers[j].s.icache, b[i-1].servers[j].s.ccache, k, vc);
        assert CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache);
        assert ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
        assert ServerValid(b[i-1].servers[j].s);
        assert ServerValid(b[i].servers[j].s);
        lemma_AVersionIsMetWillAlwaysMet(
            b[i-1].servers[j].s.icache,
            b[i].servers[j].s.icache,
            b[i-1].servers[j].s.ccache,
            b[i].servers[j].s.ccache,
            k,
            vc
        );
        assert AVersionOfAKeyIsMet(b[i].servers[j].s.icache, b[i].servers[j].s.ccache, k, vc);
    }
}

lemma lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    deps:Dependency
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires CMNext(b[i-2], b[i-1])
    requires DependencyValid(deps)
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInDepsAreMetOnAllServers(b, i-1, deps)
    ensures AllVersionsInDepsAreMetOnAllServers(b, i, deps)
{
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInDepsAreMetOnAllServers();
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);
    
    forall k | k in deps 
        ensures AVersionIsMetOnAllServers(b, i, k, deps[k])
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, deps[k]);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, deps[k]);
        assert AVersionIsMetOnAllServers(b, i, k, deps[k]);
    }
}

lemma lemma_AllVersionsInCCacheAreMetOnAllServersWillAlwaysMet(
    b:Behavior<CMState>,
    i:int,
    idx:int
)
    requires 1 < i
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i])
    // requires CMNext(b[i-2], b[i-1])
    requires 0 <= idx < Nodes
    requires ServerNextDoesNotDecreaseVersions(b[i-1], b[i])
    requires AllVersionsInCCacheAreMetOnAllServers(b, i-1, b[i].servers[idx].s.ccache)
    ensures AllVersionsInCCacheAreMetOnAllServers(b, i, b[i].servers[idx].s.ccache)
{
    assert i-1 > 0;
    assert IsValidBehaviorPrefix(b, i-1);
    lemma_BehaviorValidImpliesOneStepValid(b, i-1);
    reveal_AllVersionsInCCacheAreMetOnAllServers();
    assert forall j :: 0 <= j < |b[i-1].servers| ==> 
        CCacheDoesNotDecrease(b[i-1].servers[j].s.ccache, b[i].servers[j].s.ccache) 
        && ICacheDoesNotDecrease(b[i-1].servers[j].s.icache, b[i].servers[j].s.icache);

    var ccache := b[i].servers[idx].s.ccache;

    forall k | k in ccache
        ensures AVersionIsMetOnAllServers(b, i, k, ccache[k].vc)
        // ensures AllVersionsInDepsAreMetOnAllServers(b, i, ccache[k].deps)
    {
        assert AVersionIsMetOnAllServers(b, i-1, k, ccache[k].vc);
        lemma_AVersionIsMetOnAllServersWillAlwaysMet(b, i, k, ccache[k].vc);
        // lemma_AllVersionsInDepsAreMetOnAllServersWillAlwaysMet(b, i, ccache[k].deps);
    }
}

}