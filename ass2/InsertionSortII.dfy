//InsertionSortII.dfy
//SENG2011 2016 Ass2 
//Author: Clinton Hadinata

method InsertionSortII(a: array<int>)
requires a!=null && a.Length > 1
ensures sorted(a,0,a.Length)
modifies a
{
  var up:=1;
  while (up < a.Length)
  decreases a.Length - up
  invariant 1 <= up <= a.Length
  invariant sorted(a,0,up);
  {
    var down := up; 
    while (down >= 1 && a[down-1] > a[down])
    decreases down
    invariant 0 <= down <= up
    invariant sortedExcept(a,0,up+1,down)                             //Everything from 0 to up (inclusive) is sorted, excluding a[down]
    invariant (down == 0) ==> sorted(a,0,up+1)                        //If down == 0 then everything from 0 to up (inclusive) is sorted as
                                                                      //  a[down] = a[0] would have the lowest number (from 0 to up)
    invariant (down >= 1 && a[down-1] < a[down]) ==> sorted(a,0,up+1) //If down>=1 && a[down-1]<a[down] then the while loop will exit after this
                                                                      //  iteration and everything from 0 to up (inclusive) will be sorted as the 
                                                                      //  element originally at up is now in the correct position.
    {
      a[down-1], a[down] := a[down], a[down-1];
      down:=down-1;
    }
    assert sorted(a,0,up+1);
    up:=up+1;
  }
  assert up == a.Length;
  assert sorted(a,0,a.Length);
}

predicate sorted(a:array<int>, from:int, to:int)
requires a!=null
requires 0 <= from <= to <= a.Length
reads a
{
  forall i,j:: from<=i<j<to ==> a[i] <= a[j]
}

predicate sortedExcept(a:array<int>, from:int, to:int, exception:int)
requires a!=null
requires 0 <= from <= to <= a.Length
reads a
{
  forall i,j:: from<=i<j<to && i!=exception && j!=exception ==> a[i] <= a[j]
}