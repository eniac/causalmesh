include "Seqs.s.dfy"
include "Multisets.s.dfy"
module Collections__Seqs_i {
import opened Collections__Seqs_s 
import opened Collections__Multisets_s
lemma SeqAdditionIsAssociative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
  ensures a+(b+c) == (a+b)+c;
{
}

predicate ItemAtPositionInSeq<T>(s:seq<T>, v:T, idx:int)
{
  0 <= idx < |s| && s[idx] == v
}

predicate method CItemAtPositionInSeq<T(==)>(s:seq<T>, v:T, idx:int)
{
  0 <= idx < |s| && s[idx] == v
}


lemma Lemma_ItemInSeqAtASomePosition<T>(s:seq<T>, v:T)
  requires v in s
  ensures  exists idx :: ItemAtPositionInSeq(s, v, idx)
{
  var idx :| 0 <= idx < |s| && s[idx] == v;
  assert ItemAtPositionInSeq(s, v, idx);
}

// function FindIndexInSeq<T>(s:seq<T>, v:T):int
//   ensures var idx := FindIndexInSeq(s, v);
//           if idx >= 0 then
//             idx < |s| && s[idx] == v
//           else
//             v !in s
// {
//   if v in s then
//     Lemma_ItemInSeqAtASomePosition(s, v);
//     var idx :| ItemAtPositionInSeq(s, v, idx);
//     idx
//   else
//     -1
// }

function method FindIndexInSeq<T(==)>(s:seq<T>, v:T) : int
    ensures var r := FindIndexInSeq(s, v);
            if r >= 0 then
              r < |s| && s[r] == v
            else
              v !in s
  {
    if |s| == 0 then
      -1
    else if s[0] == v
    then 0
    else
      var r := FindIndexInSeq(s[1..], v);
      if r == -1 then
        -1
      else
        r + 1
  }

lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x:T, y:T)
  requires [x] == [y]
  ensures  x == y
{
  calc {
    x;
    [x][0];
    [y][0];
    y;
  }
}

//////////////////////////////////////////////////////////
//  Combining sequences of sequences
//////////////////////////////////////////////////////////
function SeqCat<T>(seqs:seq<seq<T>>) : seq<T>
{
  if |seqs| == 0 then []
  else seqs[0] + SeqCat(seqs[1..])
}

function SeqCatRev<T>(seqs:seq<seq<T>>) : seq<T>
{
  if |seqs| == 0 then []
  else SeqCatRev(all_but_last(seqs)) + last(seqs)
}

lemma lemma_SeqCat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B)
{
  if |A| == 0 {
    assert A+B == B;
  } else {
    calc {
      SeqCat(A + B);
        { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
      A[0] + SeqCat(A[1..] + B);
      A[0] + SeqCat(A[1..]) + SeqCat(B);
      SeqCat(A) + SeqCat(B);
    }
  }
}

lemma lemma_SeqCatRev_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
  ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B)
{
  if |B| == 0 {
    assert SeqCatRev(B) == [];
    assert A+B == A;
  } else {
    calc {
      SeqCatRev(A + B);
        { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
      SeqCatRev(A + all_but_last(B)) + last(B);
      SeqCatRev(A) + SeqCatRev(all_but_last(B)) + last(B);
      SeqCatRev(A) + SeqCatRev(B);
    }
  }
}

lemma lemma_SeqCat_equivalent<T>(seqs:seq<seq<T>>)
  ensures SeqCat(seqs) == SeqCatRev(seqs)
{
  if |seqs| == 0 {
  } else {
    calc {
      SeqCatRev(seqs);
      SeqCatRev(all_but_last(seqs)) + last(seqs);
        { lemma_SeqCat_equivalent(all_but_last(seqs)); }
      SeqCat(all_but_last(seqs)) + last(seqs);
      SeqCat(all_but_last(seqs)) + SeqCat([last(seqs)]);
        { lemma_SeqCat_adds(all_but_last(seqs), [last(seqs)]); 
      assert seqs == all_but_last(seqs) + [last(seqs)]; }
      SeqCat(seqs);
    }
  }
}

/********* sort sequence  ***********/
  
predicate Sorted_COperationNumber_seq(a: seq<int>, low: int, high: int)
  requires 0 <= low <= high <= |a|
{
  forall i, j :: low <= i < j < high ==> a[i] <= a[j]
}

predicate NeighborSorted_COperationNumber_seq(a: seq<int>, low: int, high: int)
  requires 0 <= low <= high <= |a|
{
  forall i {:trigger a[i-1], a[i]} :: low < i < high ==> a[i-1] <= a[i]
}

method InsertSort(a: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures Sorted_COperationNumber_seq(sorted, 0, |sorted|)
  ensures |a| == |sorted|
  ensures multiset(a) == multiset(sorted)
{
  if |a| <= 1 {
    sorted := a;
    assert |a| == |sorted|;
    assert multiset(a) == multiset(sorted);
  } else {
    var last := a[|a| - 1];
    var rest := a[..|a| - 1];
    assert rest + [last] == a;
    assert multiset(a) == multiset([last]) + multiset(rest);
    var sortedRest := InsertSort(rest);
    assert multiset(sortedRest) == multiset(rest);
    assert |sortedRest| == |rest|;

    sorted := Insert(sortedRest, last);
    assert multiset(sorted) == multiset(sortedRest) + multiset([last]);
  }
}

method Insert(sortedSeq: seq<int>, value: int) returns (newSeq: seq<int>)
  requires forall i, j :: 0 <= i < j < |sortedSeq| ==> sortedSeq[i] <= sortedSeq[j]
  ensures forall i, j :: 0 <= i < j < |newSeq| ==> newSeq[i] <= newSeq[j]
  ensures |newSeq| == |sortedSeq| + 1
  ensures multiset(newSeq) == multiset(sortedSeq) + multiset([value])
  ensures |newSeq| > 0
{
  if |sortedSeq| == 0 {
    newSeq := [value];
    // assert newSeq == sortedSeq[..] + [value];
    // assert forall i, j :: 0 <= i < j < |newSeq| ==> newSeq[i] <= newSeq[j];
    // assert multiset(newSeq) == multiset(sortedSeq) + multiset([value]);
  }else {
    if value <= sortedSeq[0] {
      newSeq := [value] + sortedSeq;
      // assert newSeq == sortedSeq[..] + [value];
      // assert forall i, j :: 0 <= i < j < |newSeq| ==> newSeq[i] <= newSeq[j];
      // assert multiset(newSeq) == multiset(sortedSeq) + multiset([value]);
    } else {
      var res := Insert(sortedSeq[1..], value);
      assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
      assert forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j];
      newSeq := [sortedSeq[0]] + res;
      assert multiset(newSeq) == multiset([sortedSeq[0]]) + multiset(res);
      assert multiset(newSeq) == multiset([sortedSeq[0]]) + multiset(sortedSeq[1..]) + multiset([value]);
      assert sortedSeq == [sortedSeq[0]] + sortedSeq[1..];
      assert multiset(sortedSeq) == multiset([sortedSeq[0]]) + multiset(sortedSeq[1..]);
      // assert newSeq == sortedSeq[..] + [value];
      // assert newSeq == [sortedSeq[0]] + res;
      // assert sortedSeq[0] <= value;
      // assert forall j :: 0 < j < |sortedSeq| ==> sortedSeq[0] <= sortedSeq[j];
      // assume sortedSeq[0] <= res[0];
      assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
      // assert forall i, j :: 0 <= i < j < |sortedSeq| ==> sortedSeq[i] <= sortedSeq[j];
      // assert forall j :: 1 <= j < |sortedSeq| ==> sortedSeq[0] <= sortedSeq[j];
      // ghost var subSeq := sortedSeq[1..];
      // assert forall j :: 0 <= j < |subSeq| ==> sortedSeq[0] < subSeq[j];
      // assert forall j :: 0 <= j < |sortedSeq[1..]| ==> sortedSeq[0] <= sortedSeq[1..][j];
      // assert sortedSeq[0] <= value;
      assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
      ghost var ss := sortedSeq[1..] + [value];
      // assert forall j :: 0 <= j < |ss| ==> sortedSeq[0] <= ss[j];
      assert multiset(ss) == multiset(res);
      MultisetContains(ss, res);
      // assert forall j :: 0 <= j < |res| ==> res[j] in ss;
      // assert forall j :: 0 <= j < |res| ==> sortedSeq[0] <= res[j];
      // assert forall i, j :: 0 <= i < j < |newSeq| ==> newSeq[i] <= newSeq[j];
      // assert multiset(newSeq) == multiset(sortedSeq) + multiset([value]);
    }
  }
}

}
