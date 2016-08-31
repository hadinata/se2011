//QueueEnd.dfy
//SENG2011 2016 Ass3 Q3
//Author: Clinton Hadinata

class {:autocontracts} QueueEnd<Data> {
   ghost var shadow: seq<Data>;
   var a: array<Data>;
   var m:int, n:int;

   predicate Valid()
   {
      a!=null && a.Length!=0 && 0<=m<=n<=a.Length && shadow==a[m..n]
   }

   constructor()
   ensures shadow==[];
   {
      a, m, n := new Data[10], 0, 0;
      shadow:=[];
   }

   method Empty () returns (e:bool)
   ensures e <==> shadow==[]
   {
     e := m==n;
   }
  
   method Pop() returns (d: Data) 
   requires shadow != [];
   ensures      d == old(shadow)[0]
   ensures shadow == old(shadow)[1..]
   { 
     d, m := a[m], m+1;
     shadow := shadow[1..];
   }
 
   method Push(d: Data)
   ensures shadow == old(shadow) + [d];
   {
       if n == a.Length
       {
         var b := a;
         if m == 0
            { b := new Data[2*a.Length]; }
         forall (i | 0<=i<n-m )
            { b[i] := a[m+i]; }
         a, m, n := b, 0, n-m;
       }
       a[n], n := d, n+1;
       shadow := shadow + [d];
   }
   
    method PopEnd() returns (c: Data)
    requires shadow != []
    ensures      c == old(shadow)[|old(shadow)|-1]
    ensures shadow == old(shadow)[..|old(shadow)|-1]
    { 
      c := a[n-1];
      n := n-1;
      shadow := shadow[..|shadow|-1];
    }
    
    method SwapEnds()
    requires |shadow| >= 2
    ensures shadow == [old(shadow)[|old(shadow)|-1]] + old(shadow)[1..|old(shadow)|-1] + [old(shadow)[0]]
    {
      a[m], a[n-1] := a[n-1], a[m];
      shadow := [shadow[|shadow|-1]] + shadow[1..|shadow|-1] + [shadow[0]];
    }
} // end of QueueEnd class

method Main()
{
      var q := new QueueEnd<char>();
      q.Push('e'); q.Push('n'); q.Push('o'); q.Push('d');
      var letter:char;
      letter := q.PopEnd(); assert letter=='d';  print letter;
      q.SwapEnds();
      letter := q.Pop();    assert letter=='o';  print letter;
      q.SwapEnds();
      letter := q.PopEnd(); assert letter=='n';  print letter;
      letter := q.Pop();    assert letter=='e';  print letter;           
      print '\n';
      
      var e:bool := q.Empty();
      if e {print "test1 okay\n";} else {print "queue1 not empty\n";}

      var q2 := new QueueEnd<int>();
      q2.Push(1); q2.Push(2); q2.Push(3); q2.Push(4);
      var num:int;
      q2.SwapEnds();
      num := q2.PopEnd(); assert num==1;  print num;
      num := q2.Pop();    assert num==4;  print num;
      q2.SwapEnds();
      num := q2.PopEnd(); assert num==2;  print num;
      num := q2.PopEnd(); assert num==3;  print num;
      print '\n';
      
      var e2:bool := q2.Empty();
      if e2 {print "test2 okay\n";} else {print "queue2 not empty\n";}
}