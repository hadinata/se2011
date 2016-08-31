//Unique.dfy
//SENG2011 2016 Ass2 
//Author: Clinton Hadinata

predicate unique(a:array<char>)
requires a != null
reads a
{
  forall i,j:: 0<=i<a.Length && 0<=j<a.Length && i!=j ==> a[i] != a[j]
}