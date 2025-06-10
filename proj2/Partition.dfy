/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
  Afonso Osório - 202108700
  Pedro Madureira - 202108866
  Sofia Pinto - 202108682
  ===============================================*/


  /* Write your implementation here */
  method Partition(A: array<int>, s: nat, l: nat, X: int) returns (m: nat, n: nat)
    modifies A
    requires s <= l < A.Length
    ensures s <= m <= n <= l < A.Length
    ensures old(A[..s]) == A[..s]
    ensures forall x :: s <= x < m ==> A[x] < X
    ensures forall x :: m <= x < n ==> A[x] == X
    ensures forall x :: n <= x < l ==> A[x] > X
    ensures old(A[l..]) == A[l..]
  {
    m := s;
    n := s;
    var k := l;

    while n < k
    decreases k - n
      invariant s <= m <= n <= k <= l <= A.Length
      invariant forall x :: s <= x < m ==> A[x] < X
      invariant forall x :: m <= x < n ==> A[x] == X
      invariant forall x :: k <= x < l ==> A[x] > X
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant A[..s] == old(A[..s])
      invariant A[l..] == old(A[l..])
    {

      if A[n] < X
      {
        A[m], A[n] := A[n], A[m];
        m := m+1;
        n := n+1;
      }
      else if A[n] > X
      {
        A[n], A[k-1] := A[k-1], A[n];
        k := k-1;
      }
      else
      {
        n := n+1;
      }
    }
  }