function Dup<A>(xs: seq<A>): seq<A>
{
  if xs == [] then
    []
  else
    [xs[0]] + [xs[0]] + Dup(xs[1..])
}

//This is the map that proves the subsequence property
function DupMap<A>(xs: seq<A>):map<int,int>
{
 map i | 0<=i<|xs| :: 2*i
}


function DupRev<A>(xs: seq<A>): seq<A>
  ensures 2*|xs| == |DupRev(xs)|
{
  if xs == [] then
    []
  else
    DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]]
}

lemma DupDupRev<A>(xs: seq<A>)
  ensures Dup(xs) == DupRev(xs)
 {
   if |xs| <=1 {
   } else
    {
     calc == {
       Dup(xs);
       [xs[0]] + [xs[0]] + Dup(xs[1..]);
       [xs[0]] + [xs[0]] + DupRev(xs[1..]);
       {assert |xs[1..]|==|xs|-1 >=1; 
       assert xs[1..][|xs|-2]== xs[|xs|-1];
       assert xs[1..][..|xs|-2]== xs[1..|xs|-1];}
       [xs[0]] + [xs[0]]  + (DupRev(xs[1..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]]);
       DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]];
       DupRev(xs);
     }
   }
 }




lemma {:induction xs} setDup<A>(xs: seq<A>)
ensures forall x :: x in xs <==> x in Dup(xs)
ensures |Dup(xs)|==2*|xs|
ensures forall i | 0<=i<|xs| :: xs[i]==Dup(xs)[2*i]==Dup(xs)[2*i+1]
{}

 lemma {:induction xs} dupElsAux<A>(xs: seq<A>,x:A)
 requires x in xs
 ensures multiset(Dup(xs))[x]==2*multiset(xs)[x]
{
    if (xs==[]){}
    else{
      if (x==xs[0]){
          if (xs[0] in xs[1..]){
            calc=={
              multiset(Dup(xs))[xs[0]];
              2+multiset(Dup(xs[1..]))[xs[0]];
              2+2*multiset(xs[1..])[xs[0]];
              2*(1+multiset(xs[1..])[xs[0]]);{assert xs==[xs[0]]+xs[1..];}
              2*multiset(xs)[xs[0]];
            }
        }
        else {
            assert xs[0] !in xs[1..];
            calc=={
              multiset(Dup(xs))[xs[0]];
              2+multiset(Dup(xs[1..]))[xs[0]];
              {setDup(xs[1..]);
              assert xs[0] !in xs[1..] ==> xs[0] !in Dup(xs[1..]);
              assert multiset(Dup(xs[1..]))[xs[0]]==0;}
              2;{assert xs==[xs[0]]+xs[1..];
                assert multiset(xs)[xs[0]]==1;}
              2*multiset(xs)[xs[0]];
            }
      }
      }
      else {
        calc=={
         multiset(Dup(xs))[x];
         multiset(Dup(xs[1..]))[x];{assert x in xs[1..];}
         2*multiset(xs[1..])[x];{assert xs==[xs[0]]+xs[1..];}
         2*multiset(xs)[x];
       }


      }    


    }

}


lemma {:induction xs} dupEls<A>(xs: seq<A>)
 ensures forall x | x in xs :: multiset(Dup(xs))[x]==2*multiset(xs)[x]
{ forall x | x in xs 
  ensures multiset(Dup(xs))[x]==2*multiset(xs)[x]{
   dupElsAux(xs,x);

  }
}


function dup(i:int,j:int):int
ensures i==j==> dup(i,j)==2*i
ensures i!=j ==> dup(i,j)==2*i+1
{if (i==j) then 2*i
 else 2*i+1}
 

function fdup(j:int):(int -> int) 
{ i => dup(i,j)}


function dupInvariant(i:int,j:int):int
ensures i<j==> dupInvariant(i,j)==2*i+1
ensures i>=j ==> dupInvariant(i,j)==j+i
{if (i < j) then 2*i+1
 else i+j}


function fdupInvariant(j:int):(int -> int) 
{ i => dupInvariant(i,j) }

function dupMap<A>(xs:seq<A>,i:int):map<int,int>
{map it | 0<=it<=|xs| :: if (it < i) then 2*it+1 else i+it}
