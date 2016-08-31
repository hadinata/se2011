//Reverse.dfy
//SENG2011 2016 Ass2 
//Author: Clinton Hadinata

function method revstring(s:string) : string
{
  if s==[] then s else s[|s|-1..|s|] + revstring(s[0..|s|-1])
}

method Main() 
{
  var a:string := "dekrowti";
  print revstring(a);
}
