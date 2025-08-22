include "../distributed_system.dfy"
// include "causalcut.dfy"
include "packet_sending.dfy"
include "properties.dfy"
include "deps_are_met.dfy"
include "../../../Common/Collections/Seqs.s.dfy"

module CausalMesh_Proof_Test_i {
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
import opened CausalMesh_Proof_DepsAreMet_i
import opened Collections__Seqs_s
import opened Collections__Maps_i
import opened Collections__Maps2_s

lemma {:axiom} lemma_TwoMetaMapAreEqual(m1:map<Key, Meta>, m2:map<Key, Meta>)
    ensures m1 == m2

lemma lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps
(
    b:Behavior<CMState>,
    i:int,
    idx:int,
    icache:ICache,
    deps:Dependency,
    todos:map<Key, Meta>,
    domain:set<Key>
)
    requires i > 0
    requires IsValidBehaviorPrefix(b, i)
    requires CMNext(b[i-1], b[i]);
    requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    requires DependencyValid(deps)
    requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    requires forall k :: k in deps ==> k in domain 

    requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
                        VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    requires CausalCut(todos)

    requires AllDepsInICacheAreMetOnAllServers(b, i, icache)
    requires AllVersionsInDepsAreMetOnAllServers(b, i, deps)
    requires forall k :: k in todos ==> AVersionIsMetOnAllServers(b, i, k, todos[k].vc) && AllVersionsInDepsAreMetOnAllServers(b, i, todos[k].deps)
    // ensures 
    //         var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, deps, todos, domain);
    //         var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
    //         res1 == res2
{
    if |deps| == 0 {
        var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, deps, todos, domain);
        var res2 := GetMetasOfAllDeps(icache, deps, todos, domain);
        assert res1 == res2;
    } else {
        var k :| k in deps;
        var new_deps := RemoveElt(deps, k);
        if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) {
            var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos, domain);
            var res2 := GetMetasOfAllDeps(icache, new_deps, todos, domain);
            lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps(b, i, idx, icache, new_deps, todos, domain);
            // assume res1 == res2;
            lemma_TwoMetaMapAreEqual(res1, res2);
            assert res1 == res2;
        } else {
            var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
            if |metas| > 0 {

            } else {
                // var initial := EmptyMeta(k);
                // var meta := initial.(vc:=deps[k]);
                // assert CausalCut(todos);
                // var todos' := AddMetaToMetaMap(todos, meta);

                // // // var res1 := GetMetasOfAllDepsGlobalView(b, i, idx, icache, new_deps, todos', domain);
                // var res2 := GetMetasOfAllDeps(icache, new_deps, todos', domain);
                // lemma_GetMetasOfAllDepsGlobalViewEqualsToGetMetasOfAllDeps(b, i, idx, icache, new_deps, todos', domain);
                // assume res1 == res2;
                // assert res1 == res2;
            }
        }
    }
}

}