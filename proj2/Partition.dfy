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
    requires s <= l <= A.Length
    ensures m <= n <= A.Length
    ensures old(A[..s]) == A[..s]
    ensures forall x :: s <= x < m ==> A[x] < X
    ensures forall x :: m <= x < n ==> A[x] == X
    ensures forall x :: n <= x < l ==> A[x] > X
    ensures old(A[l..]) == A[l..]
    ensures multiset(A[..]) == multiset(old(A[..]))
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

method TestPartitionMultipleCases() {
  var a1 := new int[8];
  a1[0], a1[1], a1[2], a1[3], a1[4], a1[5], a1[6], a1[7] := 3, 2, 5, 1, 2, 5, 3, 4;
  var oldA1 := a1[..];
  var m1, n1 := Partition(a1, 2, 7, 3);
  assert m1 <= n1 <= a1.Length;
  assert forall x :: 2 <= x < m1 ==> a1[x] < 3;
  assert forall x :: m1 <= x < n1 ==> a1[x] == 3;
  assert forall x :: n1 <= x < 7 ==> a1[x] > 3;
  assert a1[..2] == oldA1[..2];
  assert a1[7..] == oldA1[7..];
  assert multiset(a1[..]) == multiset(oldA1[..]);

  var a2 := new int[5];
  a2[0], a2[1], a2[2], a2[3], a2[4] := 1, 2, 3, 4, 5;
  var oldA2 := a2[..];
  var m2, n2 := Partition(a2, 0, 5, 3);
  assert m2 <= n2 <= a2.Length;
  assert forall x :: 0 <= x < m2 ==> a2[x] < 3;
  assert forall x :: m2 <= x < n2 ==> a2[x] == 3;
  assert forall x :: n2 <= x < 5 ==> a2[x] > 3;
  assert a2[..0] == oldA2[..0];
  assert a2[5..] == oldA2[5..];
  assert multiset(a2[..]) == multiset(oldA2[..]);

  var a3 := new int[4];
  a3[0], a3[1], a3[2], a3[3] := 4, 4, 4, 4;
  var oldA3 := a3[..];
  var m3, n3 := Partition(a3, 0, 4, 4);
  assert m3 <= n3 <= a3.Length;
  assert forall x :: 0 <= x < m3 ==> a3[x] < 4;
  assert forall x :: m3 <= x < n3 ==> a3[x] == 4;
  assert forall x :: n3 <= x < 4 ==> a3[x] > 4;
  assert a3[..0] == oldA3[..0];
  assert a3[4..] == oldA3[4..];
  assert multiset(a3[..]) == multiset(oldA3[..]);

  var a4 := new int[5];
  a4[0], a4[1], a4[2], a4[3], a4[4] := 5, 4, 3, 2, 1;
  var oldA4 := a4[..];
  var m4, n4 := Partition(a4, 0, 5, 3);
  assert m4 <= n4 <= a4.Length;
  assert forall x :: 0 <= x < m4 ==> a4[x] < 3;
  assert forall x :: m4 <= x < n4 ==> a4[x] == 3;
  assert forall x :: n4 <= x < 5 ==> a4[x] > 3;
  assert a4[..0] == oldA4[..0];
  assert a4[5..] == oldA4[5..];
  assert multiset(a4[..]) == multiset(oldA4[..]);

  var a5 := new int[9];
  a5[0], a5[1], a5[2], a5[3], a5[4], a5[5], a5[6], a5[7], a5[8] := 3, 3, 3, 2, 2, 2, 4, 4, 4;
  var oldA5 := a5[..];
  var m5, n5 := Partition(a5, 0, 9, 3);
  assert m5 <= n5 <= a5.Length;
  assert forall x :: 0 <= x < m5 ==> a5[x] < 3;
  assert forall x :: m5 <= x < n5 ==> a5[x] == 3;
  assert forall x :: n5 <= x < 9 ==> a5[x] > 3;
  assert a5[..0] == oldA5[..0];
  assert a5[9..] == oldA5[9..];
  assert multiset(a5[..]) == multiset(oldA5[..]);
}

