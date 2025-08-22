
module Collections__Maps_i {

// TODO_MODULE: module Collections__Maps_i {

predicate eq_map<A(!new), B>(x:map<A, B>, y:map<A, B>)
    ensures eq_map(x, y) ==> x == y;
{
  && (forall a :: a in x <==> a in y)
  && (forall a :: a in x ==> x[a] == y[a])
}

function method domain<U(!new), V>(m: map<U,V>): set<U>
  ensures forall i :: i in domain(m) <==> i in m;
{
  set s | s in m
}

function union<U(!new), V>(m: map<U,V>, m': map<U,V>): map<U,V>
  requires m.Keys !! m'.Keys
  ensures forall i :: i in union(m, m') <==> i in m || i in m'
  ensures forall i :: i in m ==> union(m, m')[i] == m[i]
  ensures forall i :: i in m' ==> union(m, m')[i] == m'[i]
{
  map i{:auto_trigger} | i in (domain(m) + domain(m')) :: if i in m then m[i] else m'[i]
}

function method RemoveElt<U(!new),V(!new)>(m:map<U,V>, elt:U) : map<U,V>
  requires elt in m
  decreases |m|
  ensures |RemoveElt(m, elt)| == |m| - 1
  ensures !(elt in RemoveElt(m, elt))
  ensures forall elt' :: elt' in RemoveElt(m, elt) <==> elt' in m && elt' != elt
{
  var m' := map elt' | elt' in m && elt' != elt :: m[elt'];
  lemma_map_remove_one(m, m', elt);
  m'
}

lemma lemma_non_empty_map_has_elements<S(!new),T(!new)>(m:map<S,T>)
  requires |m| > 0
  ensures exists x :: x in m
{
  var dom := domain(m);
  var empty_map:map<S,T> := map [];
  assert m.Keys !! empty_map.Keys;
  assert m.Keys != empty_map.Keys;
  assert |dom| > 0;
}

lemma lemma_MapSizeIsDomainSize<S(!new),T(!new)>(dom:set<S>, m:map<S,T>)
  requires dom == domain(m)
  ensures |m| == |dom|
{
  if |m| == 0 {
    assert |dom| == 0;
  } else {
    lemma_non_empty_map_has_elements(m);
    var x :| x in m;
    assert x in m;
    assert x in dom;
    var m' := map y | y in m && y != x :: m[y];
    var dom' := dom - { x };
    lemma_MapSizeIsDomainSize(dom', m');
    assert |dom'| == |m'|;
    assert |dom| == |dom'| + 1;
    assert m == m'[x := m[x]];
    assert |m| == |m'| + 1;
  }
}

lemma lemma_maps_decrease<S(!new),T(!new)>(before:map<S,T>, after:map<S,T>, item_removed:S)
  requires item_removed in before
  requires after == map s | s in before && s != item_removed :: before[s]
  ensures  |after| < |before|
{
  assert !(item_removed in after);
  forall i | i in after
    ensures i in before;
  {
    assert i in before;
  }

  var domain_before := set s | s in before;
  var domain_after  := set s | s in after;

  lemma_MapSizeIsDomainSize(domain_before, before);
  lemma_MapSizeIsDomainSize(domain_after, after);

  if |after| == |before| {
    if domain_before == domain_after {
      assert !(item_removed in domain_after);
      assert false;
    } else {
      assert |domain_after| == |domain_before|;
      var diff := domain_after - domain_before;
      assert forall i :: i in domain_after ==> i in domain_before;
      assert |diff| == 0;
      var diff2 := domain_before - domain_after;
      assert item_removed in diff2;
      assert |diff2| >= 1;
      assert false;
    }
  } else if |after| > |before|{
    //var extra :| extra in domain_after && !(extra in domain_before);
    var diff := domain_after - domain_before;
    assert |domain_after| > |domain_before|;
    if |diff| == 0 {
      assert |diff| == |domain_after| - |domain_after*domain_before|;
      assert |domain_after*domain_before| <= |domain_before|;
      assert |domain_after| == |domain_after*domain_before|;
      assert |domain_after| <= |domain_before|;
      assert false;
    } else {
      assert |diff| >= 1;
      var diff_item :| diff_item in diff;
      assert diff_item in domain_after;
      assert !(diff_item in domain_before);
      assert false;
    }
    assert false;
  }
}


lemma lemma_map_remove_one<S(!new),T(!new)>(before:map<S,T>, after:map<S,T>, item_removed:S)
  requires item_removed in before
  requires after == map s | s in before && s != item_removed :: before[s]
  ensures  |after| + 1 == |before|
{
  lemma_maps_decrease(before, after, item_removed);
  var domain_before := domain(before);
  var domain_after  := domain(after);

  lemma_MapSizeIsDomainSize(domain_before, before);
  lemma_MapSizeIsDomainSize(domain_after, after);
  
  assert domain_after + { item_removed } == domain_before;
}

lemma Lemma_map2equiv<K1, V>(f:map<K1, V>, g:map<K1, V>)
  requires forall k1 :: k1 in f <==> k1 in g
  requires forall k1 :: k1 in f ==> f[k1] == g[k1]
  ensures  f == g
{
}

// TODO_MODULE: } import opened Collections__Maps_i_ = Collections__Maps_i

} 
