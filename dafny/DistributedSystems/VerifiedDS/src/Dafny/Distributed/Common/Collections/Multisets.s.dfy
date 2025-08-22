
module Collections__Multisets_s {
function RestrictMultiset<S(!new)>(m:multiset<S>, f:S->bool):multiset<S>
  reads f.reads
  requires forall x :: f.requires(x)
  ensures RestrictMultiset(m, f) <= m
  ensures forall x :: RestrictMultiset(m, f)[x] == if f(x) then m[x] else 0
{
  if |m| == 0 then
    multiset{}
  else
    var x :| x in m;
    var m_without_x := m[x := 0];
    if f(x) then
      RestrictMultiset(m_without_x, f)[x := m[x]]
    else
      RestrictMultiset(m_without_x, f)
}

lemma MultisetContains(ss: seq<int>, res: seq<int>)
  requires multiset(ss) == multiset(res)
  ensures forall j :: 0 <= j < |res| ==> res[j] in ss
{
  assert forall j :: 0 <= j < |res| ==> multiset(ss)[res[j]] > 0;
  forall j | 0 <= j < |res|
    ensures res[j] in ss
  {
    assert multiset(ss)[res[j]] > 0; // res[j] must be in ss because their multisets are equal
  }
}

} 
