//DutchFlag.dfy
//SENG2011 2016 Ass3 Q1
//Author: Clinton Hadinata

datatype Colour = RED | WHITE | BLUE

method FlagSort(flag: array<Colour>) 
requires flag!=null
//Postconditions are:
//(1) If a ball is red, then all balls to the left of it must also be red
//(2) If a ball is blue, then all balls to the right of it must also be blue
//(3) If a ball is white, then all balls to the left of it must not be blue, and all balls to the right must not be red.
//These postconditions form a specification that captures the requirement of the program completely. 
//It is enough to say that all balls to the left of all white balls must not be blue. Because there are only 3 colours (defined in datatype declaration of Colour),
//balls to the left of a white ball can only be either white or red, and because of postcondition (1), all the red balls would be to the left of all the white balls.
//The same appplies to the statement that all balls to the right of white balls must not be red. Hence reds will always be to the left of whites which will always be to the left of blues.
//This also covers cases where there are only two colours - if it's red/blue only, (1)&(2) will mean all reds are to the left of blues and vice versa.
//If it is white/blue then (3) will mean that all balls to the left of whites aren't blue and hence they would stay separated with whites to the left of blues.
//The same applies for white/red except in reverse.
ensures forall i:: 0<=i<flag.Length && flag[i] == RED ==> (forall j:: 0<=j<i ==> flag[j] == RED)
ensures forall i:: 0<=i<flag.Length && flag[i] == BLUE ==> (forall j:: i<=j<flag.Length ==> flag[j] == BLUE)
ensures forall i:: 0<=i<flag.Length && flag[i] == WHITE ==> (forall j:: 0<=j<i ==> flag[j] != BLUE) && (forall j:: i<=j<flag.Length ==> flag[j] != RED)
modifies flag;
{
    var white := 0;
    var next := 0;
    var blue := flag.Length;    // colours between next and blue unsorted
    while (next != blue)    // when next==blue, no colours left to sort
    invariant 0 <= white<=next<=blue <= flag.Length
    invariant forall i:: 0    <=i<white       ==> flag[i]==RED
    invariant forall i:: white<=i<next        ==> flag[i]==WHITE
    invariant forall i:: blue <=i<flag.Length ==> flag[i]==BLUE
    {
            match (flag[next])
            {
            case WHITE => next:=next+1;
            case BLUE  => blue:=blue-1;
                          flag[next], flag[blue] := flag[blue], flag[next];
            case RED   => flag[next], flag[white] := flag[white], flag[next];
                          next:=next+1;
                          white:=white+1;
            }
    }
}

method Main()
{
  var flag: array<Colour> := new Colour[6];

  //three colours
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5]
   := BLUE, RED, WHITE, BLUE, RED, BLUE;
  FlagSort(flag);
  print flag[..], '\n';
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5]
   := RED, RED, WHITE, BLUE, WHITE, RED;
  FlagSort(flag);
  print flag[..], '\n';
  flag[0], flag[1], flag[2], flag[3], flag[4], flag[5]
   := WHITE, RED, WHITE, BLUE, BLUE, WHITE;
  FlagSort(flag);
  print flag[..], '\n';

  //two colours
  var flag1: array<Colour> := new Colour[4];
  flag1[0], flag1[1], flag1[2], flag1[3]
   := BLUE, RED, BLUE, RED;
  FlagSort(flag1);
  print flag1[..], '\n';
  flag1[0], flag1[1], flag1[2], flag1[3]
   := WHITE, RED, WHITE, RED;
  FlagSort(flag1);
  print flag1[..], '\n';
  flag1[0], flag1[1], flag1[2], flag1[3]
   := BLUE, WHITE, BLUE, BLUE;
  FlagSort(flag1);
  print flag1[..], '\n';
}