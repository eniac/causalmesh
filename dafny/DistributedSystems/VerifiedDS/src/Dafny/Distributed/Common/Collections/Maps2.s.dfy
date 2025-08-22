// TODO eliminate redundancy between these two libraries we've accreted.

module Collections__Maps2_s {

function method mapdomain<KT,VT>(m:map<KT,VT>) : set<KT>
{
  set k | k in m :: k
}

function method mapremove<KT,VT>(m:map<KT,VT>, k:KT) : map<KT,VT>
{
  map ki | ki in m && ki != k :: m[ki]
}

predicate imaptotal<KT(!new),VT>(m:imap<KT,VT>)
{
  forall k {:trigger m[k]}{:trigger k in m} :: k in m
}
} 
