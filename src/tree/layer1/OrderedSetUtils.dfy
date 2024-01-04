include "../../../src/Collections/Seq.dfy"

module {:options "--function-syntax:3"} OrderedSetUtils {
  import Seq

  function Pick<A>(s: set<A>): A
    requires s != {}
  {
    var x :| x in s; x
  }

  lemma sizeOfSet(s:set<int>,x:int)
    requires x in s
    ensures (s-{x})+{x}==s
  {}

  lemma sizes(s1:set<int>,s2:set<int>)
    requires s1==s2
    ensures |s1|==|s2|
  {}

  lemma sizesrev(s1:set<int>,s2:set<int>)
    requires s1 <= s2
    requires |s1| < |s2|
    ensures s1 < s2
  {assert |s1|+1 <= |s2|;
   if (s1=={}){}
   else {
     var x:| x in s1;
     if (x !in s2){ assert s1 < s2;}
     else {
       assert |s1-{x}|<|s2-{x}|==|s2|-1;
       sizesrev(s1-{x},s2-{x});
     }}
  }

  lemma sizesContained<A>(s1: set<A>, s2: set<A>)
    requires s1 <= s2
    ensures |s1| <= |s2|
  {
    if s1 == {} {
    } else {
      assert forall x | x in s1 :: x in s1;
      var z := Pick(s1);
      calc  {
        |s1|; ==
        1+|s1-{z}|; <=
        { sizesContained(s1-{z}, s2-{z}); assert z in s2; }
        1 + |s2-{z}|; ==
        |s2|;
      }
    }
  }

  lemma sizesStrictContained(xs: set<int>, ys: set<int>)
    requires xs < ys
    ensures |xs| < |ys|
  {
    if |xs| == 0 {
    } else {
      var x :| x in xs;
      sizesStrictContained(xs - {x}, ys - {x});
    }
  }
  //MINIMUM DEFINITION:

  function {:induction s} minimum(s:set<int>):int
    requires s != {}
    ensures minimum(s) in s
    //ensures forall x | x in s :: minimum(s)<=x
  {
    //var x :| x in s;
    var x:=Pick(s);
    if (s-{x}=={}) then x
    else if (x < minimum(s-{x})) then x
    else minimum(s-{x})

  }

  // Minimum is smaller or equal than all the set elements
  lemma lmin(s: set<int>, x: int)
    requires s != {} && x in s
    ensures x >= minimum(s)
  {
    var y:=Pick(s);
    if (s-{y} == {}){assert s=={y};assert x==y;}
    else if (minimum(s-{y})==minimum(s)){}
    else{}
  }


  lemma lminimum(s:set<int>)
    requires s != {}
    ensures minimum(s) in s && forall x | x in s :: minimum(s) <= x
  {forall x | x in s
     ensures minimum(s) <= x {lmin(s,x);}}

  //An element smaller than the rest of elements is the minimum
  lemma lminimumrev(s:set<int>,x:int)
    requires x in s && forall z | z in s && z != x :: x < z
    ensures x == minimum(s)
  {
    lminimum(s);
    assert minimum(s) in s;
    if (x==minimum(s)){}
    else {assert x < minimum(s);
          assert false;}//contradiction
  }

  //MAXIMUM DEFINITION:
  function {:induction s} maximum(s:set<int>):int
    requires s != {}
  {
    var x:=Pick(s);
    if (s-{x}=={}) then x
    else if (x > maximum(s-{x})) then x
    else maximum(s-{x})

  }

  //Maximum is bigger or equal than all the set elements
  lemma lmax(s:set<int>,x:int)
    requires s != {} && x in s
    ensures x <= maximum(s)
  {
    var y:=Pick(s);
    if (s-{y} == {}){assert s=={y};assert x==y;}
    else if (maximum(s-{y})==maximum(s)){}
    else{}
  }


  //maximum belongs to the set
  lemma lmaximum(s:set<int>)
    requires s != {}
    ensures maximum(s) in s && forall x | x in s :: maximum(s) >= x
    ensures forall x | x in s && s-{x}!={} && x > maximum(s-{x}) :: x == maximum(s)
    ensures forall x | x in s && s-{x}!={} && x <= maximum(s-{x}) :: maximum(s) == maximum(s-{x})
  {forall x | x in s
     ensures maximum(s) >= x {lmax(s,x);}}

  lemma lmaximumOne(s:set<int>,x:int)
    requires s != {} && x in s && s-{x} != {}
    ensures if (x <= maximum(s-{x})) then maximum(s) == maximum(s-{x}) else maximum(s)==x
  {
    lmaximum(s);
  }

  //Any element of the set bigger tahn the rest is the maximum
  lemma lmaximumrev(s:set<int>,x:int)
    requires x in s && forall z | z in s && z != x :: x > z
    ensures x == maximum(s)
  {
    lmaximum(s);
    assert maximum(s) in s;
    if (x==maximum(s)){}
    else {assert x > maximum(s);
          assert false;}//contradiction
  }

  lemma lmaximum2(s:set<int>,x:int)
    requires s != {} && x in s && s-{x} != {} && x < maximum(s-{x})
    ensures maximum(s)!=x
  {lmaximum(s-{x});
   assert maximum(s-{x}) in s;
   lmax(s,maximum(s-{x}));
   assert maximum(s-{x})<= maximum(s);
   assert exists z | z in s :: z < maximum(s);
  }


  //If the set has two elements, if I remove the minimun, the maximum is the same: needed to prove First and Last
  lemma max2Elems(s:set<int>)
    requires |s|>=2
    ensures s-{minimum(s)} != {} && maximum(s)==maximum(s-{minimum(s)})
  {
    lminimum(s);
    assert |s-{minimum(s)}|==|s|-1>=1;
    //assert s-{minimum(s)} != {};
    lmax(s,minimum(s));
    assert minimum(s) in s && minimum(s) < maximum(s-{minimum(s)});
    lmaximumOne(s,minimum(s));

  }

  lemma {:verify true} lMaxMinOne(s:set<int>)
    requires s != {} && |s|==1
    ensures maximum(s)==minimum(s)
  {}

  function smaller(s:set<int>,x:int):set<int>
    ensures forall z | z in smaller(s,x) :: z in s && z < x
    ensures forall z | z in s && z < x :: z in smaller(s,x)
  {set z | z in s && z < x}



  lemma {:verify true} smallerMin(s:set<int>)
    requires s != {}
    ensures smaller(s,minimum(s)) == {} && |smaller(s,minimum(s))| == 0
  {}


  lemma {:verify true} smallerMax(s:set<int>)
    requires s != {}
    ensures smaller(s,maximum(s)) == s-{maximum(s)} && |smaller(s,maximum(s))| == |s|-1
  { sizes(smaller(s,maximum(s)),s-{maximum(s)});
    assert |smaller(s,maximum(s))|==|s-{maximum(s)}|;
    lmaximum(s);
    sizeOfSet(s,maximum(s));
  }


  lemma smallerElem(s:set<int>,x:int)
    requires s!={} && x in s && x != minimum(s)
    ensures smaller(s-{minimum(s)},x) == smaller(s,x)-{minimum(s)}
    ensures |smaller(s-{minimum(s)},x)| == |smaller(s,x)|-1
  { lminimum(s);
    sizeOfSet(s,minimum(s));}

  function elemth(s: set<int>, k: int): int
    requires 0 <= k < |s|
    ensures elemth(s,k) in s //&& |smaller(s,elemth(s,k))|==k
    //ensures elemth(s,k) in s && |smaller(s,elemth(s,k))|==k
  {
    var minim:=minimum(s);
    if (k==0) then minim
    else elemth(s-{minim},k-1)
  }

  lemma {:induction s,k} {:verify true} lelemth(s:set<int>,k:int)
    requires 0<=k<|s|
    ensures elemth(s,k) in s && |smaller(s,elemth(s,k))| == k
    ensures forall y | y in s && y < elemth(s,k) :: y in smaller(s,elemth(s,k))
  { lminimum(s);
    if (k==0) { }
    else {
      lelemth(s-{minimum(s)},k-1);
      assert elemth(s,k) in s;
      calc =={
        |smaller(s,elemth(s,k))|;
        |set z | z in s && z < elemth(s,k)|;{assert k>0;}
        |set z | z in s && z < elemth(s-{minimum(s)},k-1)|;
        {assert s==(s-{minimum(s)})+{minimum(s)};
         assert minimum(s)<elemth(s-{minimum(s)},k-1);
         assert (set z | z in s && z < elemth(s-{minimum(s)},k-1))==(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)};
        }
        |(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)}|;
        |(set z | z in s-{minimum(s)} && z < elemth(s-{minimum(s)},k-1)) + {minimum(s)}|;

      }
    }
  }


  lemma {:induction s} lelemthrev(s:set<int>,x:int,k:int)
    requires 0 <= k < |s| && x in s && |smaller(s,x)| == k
    ensures x == elemth(s,k)
  {
    if (k==0){
      assert smaller(s,x)=={};
      assert forall z | z in s && z!=x :: z>x;
      lminimumrev(s,x);
      assert x==minimum(s);
    }
    else{
      var minim:=minimum(s);
      if (minim==x){smallerMin(s);}
      else{
        smallerElem(s,x);
        assert |smaller(s-{minim},x)|==k-1;
        lelemthrev(s-{minim},x,k-1);
      }
    }

  }



  lemma elemthSmaller(s:set<int>,ss:set<int>, y:int)
    requires s > ss && |s| > |ss|
    requires y in s - ss
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures y >= elemth(s,|ss|)
  {  lelemth(s,|ss|);
     assert elemth(s,|ss|) in s;
     assert forall z | z in ss :: z < y;
     if (y < elemth(s,|ss|))
     { assert y in smaller(s,elemth(s,|ss|));
       assert ss <= smaller(s,elemth(s,|ss|));
       // assert y !in ss;
       assert ss+{y} <= smaller(s,elemth(s,|ss|));
       assert |ss+{y}|==|ss|+1;
       sizesContained(ss+{y},smaller(s,elemth(s,|ss|)));
       assert |ss+{y}| <= |smaller(s,elemth(s,|ss|))|;
       assert false;
     }
  }



  lemma elemthSmallerAll(s:set<int>,ss:set<int>)
    requires s > ss && |s| > |ss|
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures forall y | y in s - ss :: y >= elemth(s,|ss|)
    ensures forall y | y in s - ss && y != elemth(s,|ss|)  :: y > elemth(s,|ss|)
  { forall y | y in s - ss
      ensures y >= elemth(s,|ss|) {elemthSmaller(s,ss,y);}

  }


  lemma elemthBigger1(s:set<int>,ss:set<int>, y:int)
    requires s > ss && |s| > |ss|
    requires y in s && y < elemth(s,|ss|)
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures y in ss
  {
    if (y !in ss)
    {elemthSmaller(s,ss,y);
     assert y >= elemth(s,|ss|);
     assert false;}
  }



  lemma elemthBigger2(s:set<int>,ss:set<int>, y:int)
    requires s > ss && |s| > |ss|
    requires y in ss
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures y < elemth(s,|ss|)
  {
    if (y >= elemth(s,|ss|))
    { assert y !in smaller(s,elemth(s,|ss|));
      smallerSubset(s,ss);
      assert smaller(s,elemth(s,|ss|)) < ss;
      sizesStrictContained(smaller(s,elemth(s,|ss|)),ss);
      sizesStrictContained(ss,s);
      assert |smaller(s,elemth(s,|ss|))| < |ss|;
      lelemth(s,|ss|);}
  }


  lemma elemthBiggerAll(s:set<int>,ss:set<int>)
    requires s > ss && |s| > |ss|
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures forall y | y in ss :: y < elemth(s,|ss|)
  {
    forall y | y in ss
      ensures y < elemth(s,|ss|){
      elemthBigger2(s,ss,y);
    }
  }


  lemma smallerSubset(s:set<int>,ss:set<int>)
    requires s > ss && |s| > |ss|
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures smaller(s,elemth(s,|ss|)) <= ss
  {forall y | y in smaller(s,elemth(s,|ss|))
     ensures y in ss
   {elemthBigger1(s,ss,y);
   }
  }

  lemma smallerSet(s:set<int>,ss:set<int>)
    requires s > ss && |s| > |ss|
    requires forall x,z | x in ss && z in s-ss :: x < z
    ensures smaller(s,elemth(s,|ss|)) == ss
  {
    smallerSubset(s,ss);
    forall y | y in ss
      ensures y in smaller(s,elemth(s,|ss|))
    {elemthBigger2(s,ss,y);
    }

  }

  lemma elemthSet(s:set<int>,ss:set<int>)
    requires s > ss
    requires forall x,y | x in ss && y in s-ss :: x < y
    ensures |ss| < |s| && elemth(s,|ss|) in s && elemth(s, |ss|) !in ss
  { sizesStrictContained(ss,s);
    assert 0 <= |ss| < |s|;
    lelemth(s,|ss|);
    if (elemth(s, |ss|) in ss)
    {  elemthBigger2(s,ss,elemth(s, |ss|));
       assert elemth(s, |ss|) < elemth(s, |ss|);
       assert false;
    }
  }



  lemma {:verify true} firstAndLast(s:set<int>)
    requires s!={}
    ensures minimum(s)==elemth(s,0)
    ensures maximum(s)==elemth(s,|s|-1)
  {
    if (|s|==1) {
      lMaxMinOne(s);
      assert |s|-1==0;
      assert maximum(s)==minimum(s)==elemth(s,0);}
    else{
      var minim:=minimum(s);
      lminimum(s);
      assert |s| >= 2;
      calc ==
      { elemth(s,|s|-1);{assert |s|-1 != 0;}
        elemth(s-{minim},|s|-2);
        { assert s-{minim}<s;
          assert |s-{minim}|==|s|-1 >= 1;
          assert s-{minim}!={};
          firstAndLast(s-{minim});}
        maximum(s-{minim});{max2Elems(s);}
        maximum(s);
      }
    }}

  //Sorted seqs

  function isSortedSeq(xs: seq<int>):bool
  {
    forall i,j::0<=i<j<|xs| ==> xs[i]<xs[j]
  }

  function seq2Set (xs: seq<int>):set<int>
  {
    set x | x in xs :: x
  }

  function isSet(xs: seq<int>):bool
  {
    forall i, j | 0 <= i < j < |xs| :: xs[i] != xs[j]
  }


  lemma emptyset(xs:seq<int>)
    ensures xs == [] <==> seq2Set(xs)=={}
  {
    if xs == [] {
    }
    if seq2Set(xs) == {} {
      assert forall x :: x !in seq2Set(xs);
      if xs != [] {
        assert xs[0] in seq2Set(xs);
        assert false;
      }
    }
  }

  lemma existsOne(xs:seq<int>,i:int,j:int)
    requires isSet(xs) && |xs| > 0
    requires 0<=i<=j<=|xs| && j-i < |xs|
    ensures exists k | 0 <= k < |xs| :: xs[k] !in xs[i..j]
  {
    assert i>0 || j<|xs|;
    assert (i>0) ==> xs[0] !in xs[i..j];
    assert j<|xs| ==> xs[|xs|-1] !in xs[i..j];
  }


  //function lemma
  lemma seq2SetContained(xs:seq<int>, i:int,j:int)
    requires isSet(xs)
    requires |xs| > 0 && 0<=i<=j<=|xs| && j-i < |xs|
    ensures seq2Set(xs[i..j]) < seq2Set(xs)
  {

    if (i==j)
    {sizesSeq2Set(xs); }
    else
    {
      forall x | x in xs[i..j]
        ensures x in xs {}
      existsOne(xs,i,j);
      assert exists k | 0 <= k < |xs| ::
          xs[k] in  xs && xs[k] !in  seq2Set(xs[i..j]);
      assert exists k | 0 <= k < |xs| ::
          xs[k] in  seq2Set(xs) && xs[k] !in  seq2Set(xs[i..j]);
    }
  }


  function set2Seq(s:set<int>):seq<int>
    decreases s
  {
    if s == {} then
      []
    else
      var y := Pick(s);
      [y] + set2Seq(s - {y})
  }

  lemma set2SeqIsSet(s: set<int>)
    ensures seq2Set(set2Seq(s)) == s
    ensures isSet(set2Seq(s))
  {
    if s == {} {
    } else {
      var y := set2Seq(s)[0];
      set2SeqIsSet(s - {y});
      calc == {
        seq2Set(set2Seq(s));
        seq2Set([y] + set2Seq(s - {y}));
        seq2Set(set2Seq(s - {y})) + {y};
        s;
      }
    }
  }

  lemma unionseq2Set(xs: seq<int>, x: int)
    requires isSet(xs) && x !in xs
    ensures seq2Set([x] + xs) == {x} + seq2Set(xs)
  {}

  lemma removeseq2Set(xs: seq<int>, i: int)
    requires isSet(xs) && 0 <= i < |xs|
    ensures isSet(xs[..i] + xs[i+1..])
    ensures seq2Set(xs[..i] + xs[i+1..]) == seq2Set(xs) - {xs[i]}
  {}

  lemma decomposeSeq2Set(xs: seq<int>, i: int)
    requires isSet(xs) && 0 <= i < |xs|
    ensures seq2Set(xs) == seq2Set(xs[..i]) + {xs[i]} + seq2Set(xs[i+1..])
  {}

  lemma sizesSet2Seq(s:set<int>)
    ensures |set2Seq(s)|==|s|
  {}

  lemma  sizesSeq2Set(xs:seq<int>)
    requires isSet(xs)//forall i,j|0 <= i < j < |xs| :: xs[i] != xs[j]
    ensures |seq2Set(xs)| == |xs|
  {if (xs==[]) {}
   else {sizesSeq2Set(xs[1..]);
         assert xs==[xs[0]]+xs[1..];
         assert xs[0] !in xs[1..];
         unionseq2Set(xs[1..],xs[0]);
         assert seq2Set(xs)=={xs[0]}+seq2Set(xs[1..]);
         assert |seq2Set(xs)|==1+|seq2Set(xs[1..])|;}
  }

  lemma idem(s:set<int>)
    ensures seq2Set(set2Seq(s)) == s
  {  if s != {} {
       var y := Pick(s);
       assert y !in s - {y};
       assert y !in  set2Seq(s - {y});
       set2SeqIsSet(s-{y});
       assert isSet(set2Seq(s - {y}));
       unionseq2Set(set2Seq(s - {y}),y);
       assert seq2Set([y] + set2Seq(s - {y})) == seq2Set([y]) + seq2Set(set2Seq(s - {y}));
     }
  }

  function insert(x: int, xs: seq<int>): seq<int>
    requires isSortedSeq(xs)
    ensures seq2Set(insert(x, xs)) == {x} + seq2Set(xs)
    ensures isSortedSeq(insert(x, xs))
    ensures |insert(x, xs)| <= 1 + |xs|
  {
    if xs == [] then
      [x]
    else if x == xs[0] then
      xs
    else if x < xs[0] then
      [x] + xs
    else
      calc == {
        seq2Set([xs[0]] + insert(x, xs[1..]));
        seq2Set([xs[0]]) + seq2Set(insert(x, xs[1..]));
        seq2Set([xs[0]]) + {x} + seq2Set(xs[1..]);
        seq2Set([xs[0]] + xs[1..]) + {x};
        { assert [xs[0]] + xs[1..] == xs; }
        seq2Set(xs) + {x};
      }
      assert isSortedSeq(xs);
      assert isSortedSeq(xs[1..]);
      assert isSortedSeq(insert(x, xs[1..]));
      assert xs[0] <= x;
      assert forall j | 0 <= j < |xs|-1 :: xs[0] <= xs[1..][j];
      assert forall j | 0 <= j < |insert(x, xs[1..])| ::
          insert(x, xs[1..])[j] in {x} + seq2Set(xs[1..]);
      [xs[0]] + insert(x, xs[1..])
  }

  function {:opaque} sort(xs: seq<int>): seq<int>
    ensures seq2Set(xs) == seq2Set(sort(xs))
    ensures isSortedSeq(sort(xs))
    ensures |sort(xs)| <= |xs|
  {
    if xs == [] then
      []
    else
      calc == {
        seq2Set(insert(xs[0], sort(xs[1..])));
        seq2Set(sort(xs[1..])) + {xs[0]};
        seq2Set(xs[1..]) + {xs[0]};
        seq2Set([xs[0]] + xs[1..]);
        { assert [xs[0]] + xs[1..] == xs; }
        seq2Set(xs);
      }
      insert(xs[0], sort(xs[1..]))
  }

  function set2SortedSeq(s:set<int>):seq<int>
    ensures set2SortedSeq(s) == sort(set2Seq(s))
  {
    sort(set2Seq(s))
  }

  lemma sortedSeq(s:set<int>)
    ensures isSortedSeq(set2SortedSeq(s))
    ensures seq2Set(set2SortedSeq(s)) == s
    ensures |set2SortedSeq(s)| <= |s|
  {
    idem(s);
    sizesSet2Seq(s);
  }

  lemma subseq2SetRemoveElems(xs:seq<int>,i:int,s:int)
    requires isSet(xs) && 0 <= i< |xs| && 0 <= s <|xs|
    ensures |Seq.Remove(xs,i)| == |xs|-1
    ensures |xs| > s > i >=0 ==>  Seq.Remove(xs,i)[s-1] == xs[s]
    ensures 0 <= s < i < |xs|==> Seq.Remove(xs,i)[s] == xs[s]
  {}

  lemma subseq2SetRemove(xs:seq<int>,i:int,s:int)
    requires 0 <= i < s <= |xs| && isSet(xs)
    ensures |Seq.Remove(xs,i)| == |xs|-1 && seq2Set(Seq.Remove(xs,i)[..s-1])==seq2Set(xs[..s])-{xs[i]}
  {
    if (i+1 == s){
      assert Seq.Remove(xs,i)[..s-1] == Seq.Remove(xs[..s],s-1);
      assert seq2Set(Seq.Remove(xs,i)[..s-1]) == seq2Set(Seq.Remove(xs[..s],s-1));
      removeseq2Set(xs[..s],s-1);
    }
    else
    {
      assert i+1 < s;
      calc =={
        seq2Set(Seq.Remove(xs,i)[..s-1]);
        seq2Set((xs[..i]+xs[i+1..])[..s-1]);
        {assert (xs[..i]+xs[i+1..])[..s-1]==xs[..i]+xs[i+1..s];}
        seq2Set((xs[..i]+xs[i+1..s]));
        {assert xs[..i]+xs[i+1..s] == xs[..s][..i]+xs[..s][i+1..];}
        seq2Set(xs[..s][..i]+xs[..s][i+1..]);
        {removeseq2Set(xs[..s],i);}
        seq2Set(xs[..s])-{(xs[..s])[i]};
      }
    }
  }

  lemma subseq2SetRemoveL(xs:seq<int>,i:int,s:int)
    requires 0 <= i <= s <|xs| && isSet(xs)
    ensures |Seq.Remove(xs,i)| == |xs|-1 >=s && seq2Set(Seq.Remove(xs,i)[..s])==seq2Set(xs[..s])+{xs[s]}-{xs[i]}
  {
    assert |Seq.Remove(xs,i)| == |xs|-1 >=s;
    if (i==s){}
    else{
      calc =={
        seq2Set(Seq.Remove(xs,i)[..s]);
        seq2Set((xs[..i]+xs[i+1..])[..s]);
        {assert (xs[..i]+xs[i+1..])[..s]==xs[..i]+xs[i+1..s+1];}
        seq2Set( xs[..i]+xs[i+1..s+1]);
        {assert xs[..s+1]==xs[..i]+[xs[i]]+xs[i+1..s+1];
         assert xs[..i] == xs[..s+1][..i] && xs[i+1..s+1] == xs[..s+1][i+1..s+1] && xs[i]==xs[..s+1][i];
         decomposeSeq2Set(xs[..s+1],i);
         assert seq2Set(xs[..s+1]) == seq2Set(xs[..i])+seq2Set(xs[i+1..s+1])+{xs[i]};
         assert xs[i] !in seq2Set(xs[..i]+xs[i+1..s+1]);
         removeseq2Set(xs[..s+1],i);
         assert seq2Set(xs[..i]+xs[i+1..s+1])==seq2Set(xs[..s+1])-{xs[i]};}
        seq2Set(xs[..s+1])-{xs[i]};
        {decomposeSeq2Set(xs[..s+1],s);}
        (seq2Set(xs[..s+1][..s])+{xs[..s+1][s]}+seq2Set(xs[..s+1][s+1..]))-{xs[i]};
        { assert xs[..s+1][..s] == xs[..s];}
        (seq2Set(xs[..s])+{xs[s]})-{xs[i]};
      }
    }
  }
}
