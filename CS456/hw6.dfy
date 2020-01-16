/* Provide an implementation that satisfies the given post-condition */
method M (x0 : int) returns (x : int)
  ensures (x0 < 3 ==> x == 1) && (x0 >= 3 ==> x < x0);
  {
      if (x0 < 3) {
          return 1;
      }
    else {
        return 2;
    }
}

/* Provide an implementation that satisfies the given post-condition */	
method M2(a : int, b : int, c : int) returns (m : int)
  ensures (m == a || m == b || m == c);
  ensures (m <= a && m <= b && m <= c) ;
  {
      // return the min of a, b, c
      if (a <= b && a <= c) { return a; }
      else if (b <= a && b <= c) { return b; }
      else if (c <= a && c <= b) { return c;}
}


/* Specify a meaningful post-condition and supply necessary
   loop invariants to verify the implementation */
method reverse (a : array<int>) returns (res : array<int>)

    requires a.Length > 0
    ensures a.Length > 0 ==> res.Length == a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[k] == res[res.Length - k - 1]
 {
	var i := 0;
  res := new int[a.Length];
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> res[j] == a[a.Length - j - 1]
    decreases (a.Length - i)
    {
		res[i] := a[a.Length - 1 - i];
        i := i + 1;
	}
}

function Count(a: seq<int>, k:int):nat
decreases(a)
decreases(k)
{
  if |a| == 0 then 0 else
    (if a[0] == k then 1 else 0) + Count(a[1..], k)
}


/* Take a sequence of integers and return the unique elements of that */
/* list. There is no requirement on the ordering of the returned */
/* values. */

/* Supply meaningful post-conditions and loop invariants to verify 
   the implementation */

method Unique(a: seq<int>) returns (b: seq<int>)
  requires |a| > 0
  ensures forall k :: 0 <= k < |a| ==> a[k] in b
  ensures forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
{
  var index := 0;
  b := [];
  while index < |a|
    decreases (|a| - index)
    invariant 0 <= index <= |a|
    invariant forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j]
    invariant forall k :: 0 <= k < index ==> a[k] in b
    //invariant forall k :: 0 <= k < index ==> Count(b, a[k]) == 1
    {
      if (a[index] !in b) {
        b := b + [a[index]];
      }
      assert a[index] in b;
      index := index + 1;
    }
  return b;
}

method Main()
{
  var out := Unique([1, 2, 0, 2, 9, 9, 1]);
  print out;
}

