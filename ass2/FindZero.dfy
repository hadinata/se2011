//FindZero.dfy
//SENG2011 2016 Ass2 
//Author: Clinton Hadinata

method FindZero(a:array<int>) returns (r:int)
requires a!=null
requires a.Length >= 1
ensures -1<=r<=a.Length-1
//ensures forall i:: r+1<=i<=a.Length-1 ==> a[i] != 0
ensures nozero(a, r+1) //this replaces the above postcondition
ensures 0<=r<=a.Length-1 ==> a[r] == 0
{
  r := a.Length-1;
  while (r != -1 && a[r] != 0)
  //invariant -1<=r<=a.Length-1 && forall i:: r+1<=i<=a.Length-1 ==> a[i] != 0
  invariant -1<=r<=a.Length-1 && nozero(a,r+1) //this replaces the original invariant above
  decreases r
  {
    r := r-1;
  }
  assert r == -1 || (0<=r<=a.Length && a[r] == 0);
}

predicate nozero(a:array<int>, from:int)
requires a != null
requires 0 <= from <= a.Length
reads a
{
  forall i:: from<=i<a.Length ==> a[i] != 0
}

method Main()
{
  var a:array<int> := new int[7];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6] := 3, 2, 1, 0, -1, -2, -3;
  
  print "Testcase 1: ";
  print a[..], '\n';
  
  var result1 := FindZero(a);
  if result1 < 0 { print "No 0 in array",'\n'; }
  else {
    print "Found 0 at index ";
    print result1, '\n';
  }
  
  
  a[0], a[1], a[2], a[3], a[4], a[5], a[6] :=  3, 2, 1, 9, -1, -2, -3;
  
  print "Testcase 2: ";
  print a[..], '\n';
  
  var result2 := FindZero(a);
  if result2 < 0 { print "No 0 in array",'\n'; }
  else {
    print "Found 0 at index ";
    print result2, '\n';
  }
  
  
  var b:array<int> := new int[1];
  b[0] := 0;
  
  print "Testcase 3: ";
  print b[..], '\n';
  
  var result3 := FindZero(b);
  if result3 < 0 { print "No 0 in array",'\n'; }
  else {
    print "Found 0 at index ";
    print result3, '\n';
  }
  
}