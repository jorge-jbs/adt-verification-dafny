  module Seq {
    
    ghost function First<A>(xs: seq<A>): A
     requires xs != []
    { xs[0] } 
    
    ghost function Last<A>(xs: seq<A>): A
     requires xs != []
    { xs[|xs|-1] } 
    
    ghost function Rev<A>(xs: seq<A>): seq<A>
      ensures |xs| == |Rev(xs)|
    {
      if |xs| == 0 then
        []
      else
        Rev(xs[1..]) + [xs[0]]
    }

   
    lemma LastRev<A>(xs: seq<A>)
      requires |xs| > 0
      ensures Rev(xs) == [xs[|xs|-1]] + Rev(xs[..|xs|-1])
    {
      if |xs| == 0 {
      } else if |xs| == 1 {
      } else {
        calc == {
          Rev(xs);
          Rev([xs[0]] + xs[1..]);
          Rev(xs[1..]) + [xs[0]];
          { LastRev(xs[1..]); }
          [xs[|xs|-1]] + Rev(xs[1..][..|xs[1..]|-1]) + [xs[0]];
          { assert xs[1..][..|xs[1..]|-1] == xs[1..|xs|-1]; }
          [xs[|xs|-1]] + Rev(xs[1..|xs|-1]) + [xs[0]];
          [xs[|xs|-1]] + Rev([xs[0]] + xs[1..|xs|-1]);
          [xs[|xs|-1]] + Rev(xs[..|xs|-1]);
        }
      }
    }


  lemma ConsRev<A>(x: A, xs: seq<A>)
    ensures [x] + Rev(xs) == Rev(xs + [x])
    {LastRev(xs+[x]);}

    lemma LeRev(xs: seq<int>)
      requires forall i | 0 <= i < |xs|-1 :: xs[i] >= xs[i+1]
      ensures forall i | 0 <= i < |xs|-1 :: Rev(xs)[i] <= Rev(xs)[i+1]
    {}

    ghost function Map<A,B>(f: A -> B, xs: seq<A>): seq<B>
      reads (set x: A, o: object | x in xs && o in f.reads(x) :: o)
    {
      if xs == [] then
        []
      else
        [f(xs[0])] + Map(f, xs[1..])
    }

    ghost function Elems<A>(xs: seq<A>): set<A>
    {
      set x | x in xs
    }

    lemma ElemsRev<A>(l: seq<A>)
      ensures Elems(Rev(l)) == Elems(l)
      ensures forall x | x in Rev(l) :: x in l
      ensures forall x | x in l :: x in Rev(l)
    {
      if |l| == 0 {
      } else {
        ElemsRev(l[1..]);
        assert Elems(Rev(l[1..])) == Elems(l[1..]);
        calc == {
          Elems(Rev(l));
          { assert [l[0]] + l[1..] == l; }
          Elems(Rev([l[0]] + l[1..]));
          Elems(Rev(l[1..]) + [l[0]]);
          Elems(Rev(l[1..])) + Elems([l[0]]);
          Elems(l);
        }
      }
    }

    lemma MElemsRev<A>(l: seq<A>)
      ensures MElems(Rev(l)) == MElems(l)
    {
      if |l| == 0 {
      } else {
        MElemsRev(l[1..]);
        assert [l[0]] + l[1..] == l;
      }
    }

    ghost function MElems<A>(xs: seq<A>): multiset<A>
    {
      multiset(xs)
    }

    lemma InEquivInMultiset<A>(xs: seq<A>)
      ensures forall x :: x in xs <==> x in multiset(xs)
    {}

    ghost function Insert<A>(x: A, xs: seq<A>, i: nat): seq<A>
      requires 0 <= i <= |xs|
      ensures |xs| + 1 == |Insert(x, xs, i)|
      ensures i == 0 ==> Insert(x, xs, i) == [x] + xs
      ensures i == |xs| ==> Insert(x, xs, i) == xs + [x]
      ensures Insert(x, xs, i)[i] == x
      ensures forall k | 0 <= k < i :: xs[k] == Insert(x, xs, i)[k]
      ensures forall k | i <= k < |xs| :: xs[k] == Insert(x, xs, i)[k+1]
    {
      xs[..i] + [x] + xs[i..]
    }

    ghost function Remove<A>(xs: seq<A>, i: nat): seq<A>
      requires 0 <= i < |xs|
      ensures i == 0 ==> Remove(xs, i) == xs[1..]
      ensures i == |xs| ==> Remove(xs, i) == xs[..|xs|-1]
    {
      xs[..i] + xs[i+1..]
    }
  }
