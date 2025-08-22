include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
include "cache.dfy"


module CausalMesh_Test_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    import opened CausalMesh_Cache_i
    import opened Environment_s

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
}