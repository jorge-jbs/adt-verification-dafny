include "Utils.dfy"
include "EquivClass.dfy"
include "Tree.dfy"

predicate ValidTree(t: Tree<EquivClass>)
  decreases t
  reads set c | c in elemsTree(t) :: c`parent
{
  (forall c | c in t.children ::
    assert elemsTree(c) <= elemsTree(t);
    c.root.parent == t.root
    && t.root !in elemsTree(c)
    && ValidTree(c))
  && (forall r, s | r != s && r in t.children && s in t.children ::
      elemsTree(r) !! elemsTree(s))
}

class Partition {
  var classes: array<EquivClass>;

  function ValidReads(): set<object>
    reads this, classes, elems(classes)
  {
    BigUnion(set e: EquivClass | e in classes[..] :: e.repr)
  }

  predicate Valid()
    reads this, classes, elems(classes), ValidReads()
  {
    (forall e: EquivClass | e in classes[..] ::
      e.Valid()
    )
    && (forall e: EquivClass, p: EquivClass | e in classes[..] && p in e.repr ::
        p in classes[..]
      )
    && (forall j, k | 0 <= j < k < classes.Length :: classes[j] != classes[k])
  }

  constructor(size: nat)
    ensures Valid()
  {
    new;
    var i := 0;
    var temp := new EquivClass?[size](_ => null);
    while i < size
      modifies temp
      invariant 0 <= i <= size
      invariant forall j | 0 <= j < i :: temp[j] != null
      invariant forall j, k | 0 <= j < k < i :: temp[j] != temp[k]
      invariant forall j | 0 <= j < i :: temp[j].parent == null && temp[j].Valid()
    {
      temp[i] := new EquivClass();
      i := i + 1;
    }
    classes := new EquivClass[size](
      i requires 0 <= i < size reads temp => temp[i]
    );
  }

  function Descendants(p: EquivClass): set<EquivClass>
    reads this, classes, elems(classes), ValidReads()
    requires p in classes[..]
  {
    set c | c in classes[..] && c.IsDescOf(p)
  }

  function Children(p: EquivClass): set<EquivClass>
    reads this, classes, elems(classes), ValidReads()
    requires p in classes[..]
  {
    set c | c in classes[..] && c.IsChildOf(p)
  }

  lemma ChildDesc(c: EquivClass, p: EquivClass)
    decreases c.repr
    requires c in classes[..]
    requires p in classes[..]
    requires Valid()
    ensures c.IsDescOf(p)
      <==> c == p || exists d: EquivClass | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p)
  {
    assert c.Valid();
    assert p.Valid();
    if c.IsDescOf(p) {
      assert p in c.repr;
      if c.parent == null {
        assert c == p;
      } else {
        ChildDesc(c.parent, p);
      }
    }
    if c == p {
    }
    if exists d | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p) {
      var d: EquivClass; d :| d in classes[..] && c.IsDescOf(d) && d.IsChildOf(p);
      assert d.IsDescOf(p);
      EquivClass.IsDescOfTrans(c, d, p);
    }
  }

  lemma ChildrenDescendants(p: EquivClass)
    requires p in classes[..]
    requires Valid()
    ensures Descendants(p)
      == {p} + BigUnion(set c
        | c in classes[..] && c.IsChildOf(p)
        :: Descendants(c))
  {
    calc == {
      Descendants(p);
      set c | c in classes[..] && c.IsDescOf(p);
      { forall c | c in classes[..]
          ensures c.IsDescOf(p)
            <==> c == p
            || exists d: EquivClass | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p)
        {
          ChildDesc(c, p);
        }
      }
      set c
        | c in classes[..]
        && ( c == p
          || exists d: EquivClass | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p)
          );
      (set c | c in classes[..] && c == p)
      + (set c
          | c in classes[..]
          && exists d: EquivClass | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p)
          );
      {
        assert (set c | c in classes[..] && c == p) == {p};
      }
      ({p} + set c
        | c in classes[..]
        && exists d: EquivClass | d in classes[..] :: c.IsDescOf(d) && d.IsChildOf(p));
      ({p} + set c, d: EquivClass
        | c in classes[..] && d in classes[..]
        && d.IsDescOf(c) && c.IsChildOf(p)
        :: d);
      {
        assert forall c, d: EquivClass
          | c in classes[..]
          :: d in Descendants(c)
          <==> d in classes[..] && d.IsDescOf(c);
      }
      ({p} + set c, d | c in classes[..] && c.IsChildOf(p) && d in Descendants(c) :: d);
      ({p} + BigUnion(set c
        | c in classes[..] && c.IsChildOf(p)
        :: Descendants(c)));
    }
  }

  lemma DisjointDescendantsAux(
      p: EquivClass, c: EquivClass, d: EquivClass, x: EquivClass
    )
    decreases x.repr
    requires Valid()
    requires p in classes[..]
    requires c in classes[..]
    requires c.IsChildOf(p)
    requires d in classes[..]
    requires d.IsChildOf(p)
    requires c != d
    requires x in Descendants(c)
    ensures x !in Descendants(d)
  {
    if x == c {
    } else {
      DisjointDescendantsAux(p, c, d, x.parent);
    }
  }

  lemma DisjointDescendants(p: EquivClass, c: EquivClass, d: EquivClass)
    requires Valid()
    requires p in classes[..]
    requires c in classes[..]
    requires c.IsChildOf(p)
    requires d in classes[..]
    requires d.IsChildOf(p)
    requires c != d
    ensures Descendants(c) !! Descendants(d)
  {
    forall x | x in Descendants(c)
      ensures x !in Descendants(d)
    {
      DisjointDescendantsAux(p, c, d, x);
    }
  }

  lemma AllDisjointDescendants(p: EquivClass)
    requires Valid()
    requires p in classes[..]
    ensures forall c, d
      | c != d && c in classes[..] && d in classes[..] && c.IsChildOf(p) && d.IsChildOf(p)
      :: Descendants(c) !! Descendants(d)
  {
    forall c, d
      | c != d && c in classes[..] && d in classes[..] && c.IsChildOf(p) && d.IsChildOf(p)
      ensures Descendants(c) !! Descendants(d)
    {
      DisjointDescendants(p, c, d);
    }
  }

  function DescendantsTree(p: EquivClass): Tree<EquivClass>
    decreases elems(classes) - p.repr
    reads this, classes, elems(classes), ValidReads()
    requires Valid()
    requires p in classes[..]
    ensures elemsTree(DescendantsTree(p)) == Descendants(p)
    ensures ValidTree(DescendantsTree(p))
  {
    ChildrenDescendants(p);
    AllDisjointDescendants(p);
    Node(
      p,
      set c: EquivClass | c in classes[..] && c.IsChildOf(p) ::
        DescendantsTree(c)
    )
  }

  ghost method RepairDescendants(dt: Tree<EquivClass>)
    modifies elemsTree(dt) - {dt.root}
    requires forall c | c in elemsTree(dt) :: c in classes[..]
    requires dt.root.Valid()
    requires ValidTree(dt)
    requires forall c | c != dt.root && c in elemsTree(dt) :: c !in dt.root.repr
    ensures forall c | c in elemsTree(dt) :: c.Valid()
    ensures ValidTree(dt)
    ensures forall c | c in elemsTree(dt) :: c.repr <= elemsTree(dt) + dt.root.repr
  {
    var p := dt.root;
    var cs := dt.children;
    var children := {};
    while cs - children != {}
      decreases cs - children
      invariant children <= cs
      invariant dt.root.Valid()
      invariant ValidTree(dt)
      invariant forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid()
      invariant forall c, d | c != d && c in children && d in children ::
        elemsTree(c) !! elemsTree(d)
      invariant forall c, d: EquivClass | c in children && d in elemsTree(c) ::
        d.repr <= elemsTree(c) + dt.root.repr
    {
      var ct: Tree<EquivClass>; ct :| ct in cs - children;
      ct.root.repr := {ct.root} + p.repr;
      RepairDescendants(ct);
      children := children + {ct};
    }
    assert cs - children == {};
    assert children <= cs;
    assert cs - children + children == {} + children;
    assert cs == children;
  }

  method FindAux(c: EquivClass) returns (res: EquivClass)
    decreases c.repr
    modifies elems(classes)
    requires c in classes[..]
    requires Valid()
    requires c.Valid()
    ensures res in old(c.repr)
    ensures res.parent == null
    ensures res.Valid()
    ensures c.Valid()
    ensures c.parent == null || c.parent == res
    ensures Valid()
    ensures forall e | e in old(classes[..]) :: e in classes[..]
  {
    if c.parent == null {
      return c;
    } else {
      res := FindAux(c.parent);
      ghost var dt := DescendantsTree(c);
      c.parent := res;
      // c.height := 1;
      ghost var orepr := c.repr;
      c.repr := {c, res};
      ghost var cs: set<EquivClass> := Descendants(c);
      forall e, d
        | e in classes[..]
        && e !in (elemsTree(dt) - {dt.root})
        && d in e.repr
        && d in elemsTree(dt)
        ensures e in elemsTree(dt);
      {
        EquivClass.IsDescOfTrans(e, d, c);
      }
      RepairDescendants(dt);
    }
  }

  method Find(i: nat) returns (res: EquivClass)
    modifies elems(classes)
    requires Valid()
    requires 0 <= i < classes.Length
    ensures res.parent == null
    ensures res.Valid()
    ensures Valid()
  {
    res := FindAux(classes[i]);
  }
}
