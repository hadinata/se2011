//MauritiusFlag.dfy
//SENG2011 2016 Ass3 Q2
//Author: Clinton Hadinata

datatype Colour = RED | BLUE | YELLOW | GREEN

method FlagSort(flag: array<Colour>)
requires flag!=null
//Postconditions are:
//(1) If a ball is red, then all balls to the left of it must also be red
//(2) If a ball is green, then all balls to the right of it must also be green
//(3) If a ball is blue, then all balls to the left of it must not be yellow or green, and all balls to the right must not be red.
//(4) If a ball is yellow, then all balls to the left of it must not be green, and all balls to the right must not be blue or red.
//These postconditions form a specification that captures the requirement of the program completely. 
//Because there are only 4 colours (as defined in the datatype declaration of Colour), accounting for there not being a yellow/green to the left of a blue (3)
//is sufficient as this means blues cannot be to the right of a yellow/green and only reds can be to the left of all the blues due to (1). 
//Likewise for accounting for there not being a blue/red to the right of a yellow (4), meaning that yellows cannot be to the left of a blue/red
//and only greens can be to the right of all yellows due to (2). 
ensures forall i:: 0<=i<flag.Length && flag[i]==RED ==> (forall j:: 0<=j<i ==> flag[j]==RED)
ensures forall i:: 0<=i<flag.Length && flag[i]==GREEN ==> (forall j:: i<=j<flag.Length ==> flag[j]==GREEN)
ensures forall i:: 0<=i<flag.Length && flag[i]==BLUE ==> (forall j:: 0<=j<i ==> flag[j]!=YELLOW && flag[j]!=GREEN) && (forall j::i<=j<flag.Length ==> flag[j]!= RED)
ensures forall i:: 0<=i<flag.Length && flag[i]==YELLOW ==> (forall j:: 0<=j<i ==> flag[j]!=GREEN) && (forall j::i<=j<flag.Length ==> flag[j]!=BLUE && flag[j]!= RED)
modifies flag
{
    var blue := 0;
    var yellow := 0;
    var next := 0;
    var green := flag.Length;
    
    while (next != green)
    invariant 0 <=blue<=yellow<=next<=green <= flag.Length
    invariant forall i:: 0      <=i<blue        ==> flag[i]==RED
    invariant forall i:: blue   <=i<yellow      ==> flag[i]==BLUE
    invariant forall i:: yellow <=i<next        ==> flag[i]==YELLOW
    invariant forall i:: green  <=i<flag.Length ==> flag[i]==GREEN
    {
      match (flag[next])
      {
        case YELLOW =>  next:=next+1;
        case GREEN  =>  green:=green-1;
                        flag[next], flag[green] := flag[green], flag[next];
        case RED    =>  flag[yellow], flag[next] := flag[next], flag[yellow]; //swap next and yellow - a yellow ball is now in the "next"" position and the red ball is now in the "yellow" position
                        flag[yellow], flag[blue] := flag[blue], flag[yellow]; //swap yellow and blue - the red ball is now in the "blue" position and a blue ball is now in the "yellow" position
                        yellow := yellow+1;                                   //increment yellow,
                        blue := blue+1;                                       //increment blue
                        next := next+1;                                       //increment next and everything is now shuffled along and our pointers are pointing correctly
        case BLUE   =>  flag[next], flag[yellow] := flag[yellow], flag[next];
                        next := next+1;
                        yellow := yellow+1;
      }
    }
}

method Main()
{
  var flag: array<Colour> := new Colour[8];
  
  //four colours
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5], flag[6], flag[7]
   := GREEN, YELLOW, YELLOW, BLUE, RED, BLUE, YELLOW, GREEN;
  FlagSort(flag);
  print flag[..], '\n';
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5], flag[6], flag[7]
   := BLUE, GREEN, YELLOW, BLUE, RED, BLUE, RED, GREEN;
  FlagSort(flag);
  print flag[..], '\n';
  
  //three colours
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5], flag[6], flag[7]
   := YELLOW, YELLOW, YELLOW, BLUE, YELLOW, BLUE, YELLOW, GREEN;
  FlagSort(flag);
  print flag[..], '\n';
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5], flag[6], flag[7]
   := RED, YELLOW, BLUE, YELLOW, BLUE, BLUE, YELLOW, RED;
  FlagSort(flag);
  print flag[..], '\n';
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5], flag[6], flag[7]
   := BLUE, GREEN, BLUE, RED, BLUE, BLUE, GREEN, RED;
  FlagSort(flag);
  print flag[..], '\n';
  
  //two colours
  var flag1: array<Colour> := new Colour[4];
  flag1[0], flag1[1], flag1[2], flag1[3]
   := GREEN, GREEN, GREEN, BLUE;
  FlagSort(flag1);
  print flag1[..], '\n';
  flag1[0], flag1[1], flag1[2], flag1[3]
   := YELLOW, BLUE, YELLOW, BLUE;
  FlagSort(flag1);
  print flag1[..], '\n';
  flag1[0], flag1[1], flag1[2], flag1[3]
   := RED, BLUE, BLUE, BLUE;
  FlagSort(flag1);
  print flag1[..], '\n';
}