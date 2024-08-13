predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method binSearch(a:array<int>, K:int) returns (b:bool)
  requires sorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
{
  var lo: nat := 0 ;
  var hi: nat := a.Length ;
  while (lo < hi)
    decreases hi - lo
    invariant  0 <= lo <= hi <= a.Length
    invariant forall i:nat :: (i < lo || hi <= i < a.Length) ==> a[i] != K
  {
    var mid: nat := (lo + hi) / 2 ;
    if (a[mid] < K) {
      lo := mid + 1 ;
    } else if (a[mid] > K) {
      hi := mid;
    } else {
      return true;
    }
  }
  return false ;
}

