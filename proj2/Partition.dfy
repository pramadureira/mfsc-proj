/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
  ===============================================*/


  /* Write your implementation here */
  method Partition(a: array<int>, s: nat, l: nat, X: int) returns (m: nat, n: nat)
    modifies a
    requires s < l < a.Length
    ensures m <= n <= a.Length
    ensures old(a[..s]) == a[..s]
    ensures forall x :: s <= x < m ==> a[x] < X
    ensures forall x :: m <= x < n ==> a[x] == X
    ensures forall x :: n <= x < l ==> a[x] > X
    ensures old(a[l..]) == a[l..]
  {
    m := s;
    n := s;
    var k := l;

    while n < k
    decreases k - n
      invariant s <= m <= n <= k <= l <= a.Length
      invariant forall x :: s <= x < m ==> a[x] < X
      invariant forall x :: m <= x < n ==> a[x] == X
      invariant forall x :: k <= x < l ==> a[x] > X
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant a[..s] == old(a[..s])
      invariant a[l..] == old(a[l..])
    {

      if a[n] < X
      {
        a[m], a[n] := a[n], a[m];
        m := m+1;
        n := n+1;
      }
      else if a[n] > X
      {
        a[n], a[k-1] := a[k-1], a[n];
        k := k-1;
      }
      else
      {
        n := n+1;
      }
    }
  }