include "../../../src/Utils.dfy"
include "../../../src/linear/interface/Stack.dfy"

lemma {:verify false} lemma1(v: array<int>, i: int)
  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
  requires 0 <= i <= v.Length
  ensures forall j | 0 <= j < i :: abs(v[j]) <= abs(v[i])
{}

method {:verify false} Reverse(st: Stack)
  modifies st, st.Repr()
  requires st.Valid()
  ensures st.Valid()
  ensures st.Model() == Seq.Rev(old(st.Model()))
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
{}

method {:verify false} split(v: array<int>, neg: Stack, pos: Stack)
  modifies pos, pos.Repr(), neg, neg.Repr()

  requires v !in neg.Repr() && v !in pos.Repr()
  ensures v !in neg.Repr() && v !in pos.Repr()
  ensures v[..] == old(v[..])

  requires neg.Valid()
  requires neg.Empty()
  requires pos.Valid()
  requires pos.Empty()
  requires pos.Repr() !! neg.Repr()

  ensures pos.Valid()
  ensures neg.Valid()
  ensures pos.Repr() !! neg.Repr()

  ensures forall x | x in neg.Repr() - old(neg.Repr()) :: fresh(x)
  ensures forall x | x in neg.Model() :: x < 0
  ensures forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])

  ensures forall x | x in pos.Repr() - old(pos.Repr()) :: fresh(x)
  ensures forall x | x in pos.Model() :: x >= 0
  ensures forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) >= abs(pos.Model()[i+1])

  ensures Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..])

  requires forall x | x in neg.Repr() :: allocated(x)
  requires forall x | x in pos.Repr() :: allocated(x)
  ensures forall x | x in neg.Repr() :: allocated(x)
  ensures forall x | x in pos.Repr() :: allocated(x)
{
  var i := 0;
  while i < v.Length
    invariant i <= v.Length

    invariant forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])

    invariant neg.Repr() !! pos.Repr()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)
    // invariant neg != pos

    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant neg.Valid()
    invariant forall x | x in neg.Model() :: x < 0
    invariant forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])
    // invariant forall i | 0 <= i < |neg.Model()| - 1 :: neg.Model()[i] <= neg.Model()[i+1]

    invariant forall x | x in pos.Repr() :: fresh(x)
    invariant pos.Valid()
    invariant forall x | x in pos.Model() :: x >= 0
    invariant forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) >= abs(pos.Model()[i+1])
    // invariant forall i | 0 <= i < |neg.Model()| - 1 :: neg.Model()[i] >= neg.Model()[i+1]

    invariant Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())
      == Seq.MElems(v[..i])

  {
    lemma1(v, i);
    assert forall j | 0 <= j < i :: abs(v[j]) <= abs(v[i]);
    if v[i] < 0 {
      assert Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())
        == Seq.MElems(v[..i]);
      assert Seq.MElems(neg.Model())
        == Seq.MElems(v[..i]) - Seq.MElems(pos.Model());
      assert forall x | x in Seq.MElems(neg.Model()) :: x in Seq.MElems(v[..i]) - Seq.MElems(pos.Model());
      assert forall x | x in Seq.MElems(neg.Model()) :: x in Seq.MElems(v[..i]);
      // assert forall x | x in Seq.MElems(neg.Model()) :: x in neg.Model();
      assert forall x | x in neg.Model() :: x in Seq.MElems(neg.Model());
      assert forall x | x in neg.Model() :: x in v[..i];
      assert forall x | x in neg.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in neg.Model() :: abs(v[i]) >= x;
      assert |neg.Model()| > 0 ==> neg.Model()[0] in neg.Model();
      assert |neg.Model()| > 0 ==> abs(v[i]) >= neg.Model()[0];
      // assert forall j | 0 <= j < |neg.Model()| :: neg.Model()[j] in v[..i];
      // assert forall j | 0 <= j < |neg.Model()| :: abs(neg.Model()[j]) <= abs(v[i]);
      // assert forall j | 0 <= j < |neg.Model()| :: neg.Model()[j] <= v[i];
      neg.Push(v[i]);
    } else {
      assert Seq.MElems(pos.Model()) + Seq.MElems(neg.Model())
        == Seq.MElems(v[..i]);
      assert Seq.MElems(pos.Model())
        == Seq.MElems(v[..i]) - Seq.MElems(neg.Model());
      assert forall x | x in Seq.MElems(pos.Model()) :: x in Seq.MElems(v[..i]) - Seq.MElems(neg.Model());
      assert forall x | x in Seq.MElems(pos.Model()) :: x in Seq.MElems(v[..i]);
      // assert forall x | x in Seq.MElems(pos.Model()) :: x in pos.Model();
      assert forall x | x in pos.Model() :: x in Seq.MElems(pos.Model());
      assert forall x | x in pos.Model() :: x in v[..i];
      assert forall x | x in pos.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in pos.Model() :: abs(v[i]) >= x;
      assert |pos.Model()| > 0 ==> pos.Model()[0] in pos.Model();
      assert |pos.Model()| > 0 ==> abs(v[i]) >= pos.Model()[0];
      assert forall x | x in pos.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in pos.Model() :: abs(v[i]) >= x;
      assert |pos.Model()| > 0 ==> pos.Model()[0] in pos.Model();
      assert |pos.Model()| > 0 ==> abs(v[i]) >= pos.Model()[0];
      pos.Push(v[i]);
    }
    i := i + 1;
  }
}

method {:verify false} FillFromStack(r: array<int>, i: nat, st: Stack) returns (l: nat)
  modifies r, st, st.Repr()
  requires st.Valid()
  requires i + |st.Model()| <= r.Length
  ensures st.Valid()
  ensures st.Empty()
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures forall x | x in st.Repr() :: allocated(x)
  ensures r[i..i+old(|st.Model()|)] == old(st.Model())
  ensures forall j | j < i || i+old(|st.Model()|) <= j :: r[j] == old(r[j])
  ensures Seq.MElems(r[i..i+old(|st.Model()|)]) == Seq.MElems(old(st.Model()))
  ensures l == i + old(|st.Model()|)
{
  if !st.Empty() {
    r[i] := 0;
  }
}

method {:verify true} reordenandoLaCola(neg: Stack, pos: Stack, v: array<int>) returns (r: array<int>)
  modifies neg, neg.Repr()
  modifies pos, pos.Repr()
  modifies v
  requires v !in neg.Repr() && v !in pos.Repr()
  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
  requires neg.Valid() && neg.Empty()
  requires pos.Valid() && pos.Empty()
  requires neg != pos && neg.Repr() !! pos.Repr() && neg !in pos.Repr() && pos !in neg.Repr()
  requires forall x | x in neg.Repr() :: allocated(x)
  requires forall x | x in pos.Repr() :: allocated(x)
  ensures r !in neg.Repr()
  ensures r !in pos.Repr()
  ensures v !in neg.Repr()
  ensures v !in pos.Repr()
  ensures v.Length == r.Length
  ensures old(Array.melems(v)) == Array.melems(r)
  ensures forall i | 0 <= i < r.Length - 1 :: r[i] <= r[i+1]
{
  ghost var ovd := v[..];
  assert ovd == old(v[..]);
  assert v[..] == old(v[..]);
  assert v == old(v);
  split(v, neg, pos);
  assert v == old(v);
  assert v[..] == old(v[..]);
  assert Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..]);
  calc == {
    |neg.Model()| + |pos.Model()|;
    |Seq.MElems(neg.Model())| + |Seq.MElems(pos.Model())|;
    |Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())|;
    |Seq.MElems(v[..])|;
    |v[..]|;
    v.Length;
  }
  assert allocated(v);
  assert forall x | x in v[..] :: allocated(x);
  assert |neg.Model()| + |pos.Model()| == |v[..]| == v.Length;
  var i := 0;
  r := new int[v.Length];
  assert allocated(v);
  assert forall x | x in v[..] :: allocated(x);
  ghost var onegmodel := neg.Model();
  ghost var oposmodel := pos.Model();
  assert ovd == old(v[..]);
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == Seq.MElems(v[..]);
  assert |onegmodel| + |oposmodel| == v.Length;
  assert neg.Repr() !! pos.Repr();
  assert pos !in neg.Repr();
  assert pos != neg;
  assert v != r;
  assert v !in neg.Repr();
  assert r !in neg.Repr();
  i := FillFromStack(r, i, neg);
  // assert v[..] == old(v[..]);
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == old(Seq.MElems(v[..]));
  var j := i;
  assert r[..j] == onegmodel;
  assert |onegmodel| + |oposmodel| == v.Length;
  assert i == |onegmodel|;
  assert pos.Valid();
  Reverse(pos);
  // assert v[..] == old(v[..]);
  assert ovd == old(v[..]);
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == old(Seq.MElems(v[..]));
  assert pos.Model() == Seq.Rev(oposmodel);
  assert |pos.Model()| == |oposmodel|;
  assert i + |pos.Model()| == i + |oposmodel| == |onegmodel| + |oposmodel| == v.Length == r.Length;
  i := FillFromStack(r, i, pos);
  // assert v[..] == old(v[..]);
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == old(Seq.MElems(v[..]));
  assert i == v.Length;
  assert r[..j] == onegmodel;
  assert r[j..] == Seq.Rev(oposmodel);
  assert Seq.MElems(r[..j]) == Seq.MElems(onegmodel);
  Seq.MElemsRev(oposmodel);
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == Seq.MElems(ovd);
  assert Seq.MElems(r[j..]) == Seq.MElems(Seq.Rev(oposmodel)) == Seq.MElems(oposmodel);
  assert Seq.MElems(r[..j]) + Seq.MElems(r[j..]) == Seq.MElems(onegmodel) + Seq.MElems(oposmodel);
  assert Seq.MElems(r[..j] + r[j..]) == Seq.MElems(onegmodel) + Seq.MElems(oposmodel);
  assert r[..j] + r[j..] == r[..];
  assert onegmodel + Seq.Rev(oposmodel) == r[..];
  assert forall i | 0 <= i < |onegmodel|-1 :: abs(onegmodel[i]) >= abs(onegmodel[i+1]);
  assert forall i | 0 <= i < |onegmodel| :: onegmodel[i] in onegmodel && onegmodel[i] < 0;
  assert forall i | 0 <= i < |onegmodel|-1 :: onegmodel[i] <= onegmodel[i+1];
  assert forall i | 0 <= i < |oposmodel|-1 :: abs(oposmodel[i]) >= abs(oposmodel[i+1]);
  assert forall i | 0 <= i < |oposmodel| :: oposmodel[i] in oposmodel && oposmodel[i] >= 0;
  assert forall i | 0 <= i < |oposmodel|-1 :: oposmodel[i] >= oposmodel[i+1];
  Seq.LeRev(oposmodel);
  assert forall i | 0 <= i < |Seq.Rev(oposmodel)|-1 :: Seq.Rev(oposmodel)[i] <= Seq.Rev(oposmodel)[i+1];
  if 0 <= j-1 {
    assert r[j-1] < 0;
  }
  if j < r.Length {
    assert r[j] == Seq.Rev(oposmodel)[0];
    Seq.MElemsRev(oposmodel);
    assert forall i | 0 <= i < |Seq.Rev(oposmodel)| ::
      && Seq.Rev(oposmodel)[i] in Seq.MElems(Seq.Rev(oposmodel))
      && Seq.Rev(oposmodel)[i] in Seq.MElems(oposmodel)
      && Seq.Rev(oposmodel)[i] in oposmodel
      && Seq.Rev(oposmodel)[i] >= 0;
    assert r[j] >= 0;
  }
  assert 0 <= j-1  && j < r.Length ==> r[j-1] <= r[j];
  assert |onegmodel| == j;
  assert forall i | 0 <= i < j :: r[i] == onegmodel[i];
  assert forall i | 0 <= i < j-1 :: r[i] <= r[i+1];
  assert forall i | j <= i < r.Length-1 :: r[i] <= r[i+1];
  assert Seq.MElems(onegmodel) + Seq.MElems(oposmodel) == Seq.MElems(ovd);
  assert Array.melems(r) == Seq.MElems(r[..]) == old(Seq.MElems(v[..])) == old(Array.melems(v));
  /*
  while !neg.Empty()
    decreases neg.Model()

    invariant 0 <= i <= r.Length

    invariant neg.Valid()
    invariant pos.Valid()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)

    invariant r[..i] + neg.Model() == onegmodel
    invariant forall j | 0 <= j < i-1 :: r[j] <= r[j+1]
  {
    var x := neg.Pop();
    r[i] := x;
    i := i + 1;
  }

  Reverse(pos);
  // pos.Reverse();
  ghost var oposmodel := pos.Model();
  assert r[..i] == onegmodel;
  assert pos.Model() == oposmodel;
  while !pos.Empty()
    decreases pos.Model()

    invariant 0 <= i <= r.Length

    invariant neg.Valid()
    invariant pos.Valid()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)

    invariant r[..i] + pos.Model() == onegmodel + oposmodel
    invariant forall j | 0 <= j < i-1 :: r[j] <= r[j+1]
  {
    var x := pos.Pop();
    r[i] := x;
    i := i + 1;
  }
  assert i == r.Length;
     */
}
