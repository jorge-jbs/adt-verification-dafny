include "Tree.dfy"

class EquivClass {
  ghost var repr: set<EquivClass>;
  // var height: nat;
  var parent: EquivClass?;

  predicate Valid()
    reads this, repr
  {
    if parent == null then
      repr == {this}
      // && height == 0
    else
      parent in repr
      && this !in parent.repr
      // && height == 1 + parent.height  // MAL
      && repr == {this} + parent.repr
      // && repr >= {this} + parent.repr
      && parent.Valid()
  }

  constructor()
    ensures Valid()
    ensures parent == null
    ensures fresh(repr)
  {
    // height := 0;
    parent := null;
    repr := {this};
  }

  predicate IsChildOf(p: EquivClass)
    reads this, repr
    // requires Valid()
  {
    parent == p
  }

  // The reflexive-transitive closure of `IsChildOf` (on valid EquivClasses)
  predicate IsDescOf(p: EquivClass)
    reads this, repr
    // requires Valid()
  {
    p in repr
  }

  static lemma IsDescOfRefl(a: EquivClass)
    requires a.Valid()
    ensures a.IsDescOf(a)
  {}

  // static lemma IsDescOfWeakenRight(a: EquivClass, b: EquivClass)
  //   requires a.Valid() && b.Valid()
  //   requires b.parent != null
  //   requires a.IsDescOf(b)
  //   ensures a.IsDescOf(b.parent)

  // static lemma IsDescOfWeakenLeft(a: EquivClass, b: EquivClass)
  //   requires a.Valid() && b.Valid()
  //   requires a.parent != null
  //   requires a.IsDescOf(b)
  //   ensures a.parent.IsDescOf(b)

  // static lemma IsDescOfWeakenLeftPrime(a: EquivClass, b: EquivClass)
  //   requires a.Valid() && b.Valid()
  //   requires a.parent != null
  //   requires !a.parent.IsDescOf(b)
  //   ensures !a.IsDescOf(b)
  // {
  //   if a.IsDescOf(b) {
  //     IsDescOfWeakenLeft(a, b);
  //   }
  // }

  static lemma IsDescOfTrans(a: EquivClass, b: EquivClass, c: EquivClass)
    decreases a.repr
    requires a.Valid() && b.Valid() && c.Valid()
    requires a.IsDescOf(b) && b.IsDescOf(c)
    ensures a.IsDescOf(c)
  {
    if a.parent != null && a != b {
      IsDescOfTrans(a.parent, b, c);
    }
  }

  // static lemma IsDescOfAntisym(a: EquivClass, b: EquivClass)
  //   decreases b.repr
  //   requires a.Valid() && b.Valid()
  //   requires a != b
  //   requires a.IsDescOf(b)
  //   ensures !b.IsDescOf(a)
  // {
  //   if b.parent != a && b.parent != null {
  //     IsDescOfWeakenRight(a, b);
  //     IsDescOfAntisym(a, b.parent);
  //   }
  // }

  // static lemma IsDescOfTransPrime(a: EquivClass, b: EquivClass, c: EquivClass)
  //   decreases a.repr
  //   requires a.Valid() && b.Valid() && c.Valid()
  //   requires !a.IsDescOf(b) && b.IsDescOf(c)
  //   ensures !a.IsDescOf(c)
  // {
  //   if a.parent != null && a != b {
  //     if a != c {
  //       IsDescOfTransPrime(a.parent, b, c);
  //     } else {
  //       assert !a.IsDescOf(b);
  //       assert b.IsDescOf(a);
  //       IsDescOfAntisym(b, a);
  //       // assert a.IsDescOf(b);
  //       assert !a.IsDescOf(a);
  //       assert !a.IsDescOf(c);
  //     }
  //   }
  // }
}

function method BigUnion<A>(S: set<set<A>>): set<A>
{
  set X, x | X in S && x in X :: x
}

function method elems<A>(l: array<A>): set<A>
  reads l
{
  set x | x in l[..]
}

// class Tree {
//   var root: EquivClass;
//   var children: set<Tree>;

//   constructor Node(r: EquivClass, cs: set<Tree>)
//   {
//     root := r;
//     children := cs;
//   }

//   function method Elems(): set<EquivClass>
//     reads this
//   {
//     {root} + set y, c | c in children && y in c.Elems() :: y
//   }

//   predicate Valid()
//     decreases this
//     // reads elemsTree(t)
//     // reads set c | c in children :: c.root
//     // reads set c | c in children :: c.root.parent
//   {
//     forall c | c in children ::
//       c.root.parent == root
//       // && c.root.height == p.height + 1
//       && c.Valid()
//   }
// }

predicate ValidTree(t: Tree<EquivClass>)
  decreases t
  reads set c | c in elemsTree(t) :: c`parent
{
  forall c | c in t.children ::
    assert elemsTree(c) <= elemsTree(t);
    c.root.parent == t.root
    && t.root !in elemsTree(c)
    && ValidTree(c)
}

predicate ValidTreeRepr(t: Tree<EquivClass>)
  decreases t
{
  (forall c | c in t.children ::
    ValidTreeRepr(c))
  && (forall r, s | r != s && r in t.children && s in t.children ::
    elemsTree(r) !! elemsTree(s))
}

// predicate ValidTreeRepr(t: Tree<EquivClass>)
//   decreases t
//   reads t.root, t.root.repr
//   requires t.root.Valid()
// {
//   (forall c | c != t.root && c in elemsTree(t) ::
//     c !in t.root.repr)
//   && (forall r, s | r != s && r in t.children && s in t.children ::
//     elemsTree(r) !! elemsTree(s))
// }

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

  // constructor(size: nat)
  //   ensures Valid()
  // {
  //   new;  // ¿¿¿¿qué hace esto???? .-.
  //   var i := 0;
  //   var temp := new EquivClass?[size](_ => null);
  //   while i < size
  //     modifies temp
  //     invariant 0 <= i <= size
  //     invariant forall j | 0 <= j < i :: temp[j] != null
  //     invariant forall j, k | 0 <= j < k < i :: temp[j] != temp[k]
  //     invariant forall j | 0 <= j < i :: temp[j].parent == null && temp[j].Valid()
  //   {
  //     temp[i] := new EquivClass();
  //     i := i + 1;
  //   }
  //   classes := new EquivClass[size](
  //     i requires 0 <= i < size reads temp => temp[i]
  //   );
  // }

  // lemma ReprSubSet(e: EquivClass)
  //   requires e in classes[..]
  //   requires Valid()
  //   ensures multiset(e.repr) <= multiset(classes[..])

  function Descendants(p: EquivClass): set<EquivClass>
    reads this, classes, elems(classes), ValidReads()
    // requires Valid()
    requires p in classes[..]
    // ensures Descendants(p)
    //   == (set c: EquivClass | c in classes[..] && c.IsChildOf(p) :: c)
  {
    set c | c in classes[..] && c.IsDescOf(p)
  }

  function Children(p: EquivClass): set<EquivClass>
    reads this, classes, elems(classes), ValidReads()
    // requires Valid()
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

  lemma ForallDisjointDescendants(p: EquivClass)
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
    // ensures forall c | c != p && c in elemsTree(DescendantsTree(p)) :: c !in p.repr
    ensures ValidTreeRepr(DescendantsTree(p))
    // ensures forall c, d
    //   | c in elemsTree(DescendantsTree(p))
    //   && d in elemsTree(DescendantsTree(p))
    //   && c.IsDescOf(d)
    //   :: c !in d.repr
  {
    ChildrenDescendants(p);
    ForallDisjointDescendants(p);
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
    requires ValidTreeRepr(dt)
    requires forall c | c != dt.root && c in elemsTree(dt) :: c !in dt.root.repr
    ensures forall c | c in elemsTree(dt) :: c.Valid()
    ensures ValidTree(dt)
    ensures ValidTreeRepr(dt)
    ensures forall c | c in elemsTree(dt) :: c.repr <= elemsTree(dt) + dt.root.repr
    ensures forall e: EquivClass | e in classes[..] :: old(e.Valid()) ==> e.Valid()
  {
    var p := dt.root;
    var cs := dt.children;
    var children := {};
    while cs - children != {}
      decreases cs - children
      invariant children <= cs
      invariant dt.root.Valid()
      invariant ValidTree(dt)
      invariant ValidTreeRepr(dt)
      invariant forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid()
      invariant forall c, d | c != d && c in children && d in children ::
        elemsTree(c) !! elemsTree(d)
      invariant forall c, d: EquivClass | c in children && d in elemsTree(c) ::
        d.repr <= elemsTree(c) + dt.root.repr
    {
      var ct: Tree<EquivClass>; ct :| ct in cs - children;
      assert forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid();
      assert ct.root !in dt.root.repr;
      assert forall c | c in children :: elemsTree(c) !! elemsTree(ct);
      assert forall c, d: EquivClass | c in children && d in elemsTree(c) :: ct.root !in d.repr;
      ct.root.repr := {ct.root} + p.repr;
      assert forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid();
      assert forall c, d: EquivClass, e: EquivClass
        | c in children && d in elemsTree(c) && e in elemsTree(ct) && e != ct.root
        :: e !in d.repr;
      RepairDescendants(ct);
      assert forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid();
      children := children + {ct};
      assert forall c, d: EquivClass | c in children && d in elemsTree(c) :: d.Valid();
    }
    assert cs - children == {};
    assert children <= cs;
    assert cs - children + children == {} + children;
    assert cs == children;
  }

  // ghost method RepairDescendants(p: EquivClass, dt: Tree<EquivClass>)
  //   modifies p, elemsTree(dt)
  //   requires p in classes[..]
  //   requires p.Valid()
  //   requires elemsTree(dt) == Descendants(p)
  //   ensures forall c | c in elemsTree(dt) :: c.Valid()
  // {
  //   match dt {
  //     case Node(p_, cs) => {
  //       // assert p_ == p;
  //       var children := {};
  //       while cs - children != {}
  //         decreases cs - children
  //         modifies BigUnion(set c | c in cs :: elemsTree(c))
  //         invariant forall c | c in children ::
  //           c.root.Valid() && forall d | d in elemsTree(dt) :: d.Valid()
  //       {
  //         var c;
  //         c :| c in (cs - children);
  //         c.root.repr := {c.root} + p.repr;
  //         RepairDescendants(c.root, c);
  //         children := children + {c};
  //       }
  //     }
  //   }
  // }

  // ghost method RepairChild(p: EquivClass, dt: Tree<EquivClass>)
  //   modifies elemsTree(dt)
  //   requires dt.root.IsChildOf(p)
  //   ensures ValidTree(dt)

  // ghost method RepairDescendants(dt: Tree<EquivClass>)
  //   modifies dt.root, elemsTree(dt)
  //   requires forall c | c in elemsTree(dt) :: c in classes[..]
  //   requires dt.root.Valid()
  //   requires ValidTree(dt)
  //   requires ValidTreeRepr(dt)
  //   ensures forall c | c in elemsTree(dt) :: c.Valid()
  //   ensures ValidTree(dt)
  //   ensures ValidTreeRepr(dt)
  // {
  //   match dt {
  //     case Node(p, cs) => {
  //       var children := {};
  //       while cs - children != {}
  //         decreases cs - children
  //         invariant children <= cs
  //         invariant Node(p, cs) == dt
  //         invariant p.Valid()
  //         invariant ValidTree(dt)
  //         invariant ValidTreeRepr(dt)
  //         invariant forall c, d | c in children && d in elemsTree(c) :: d.Valid()
  //         invariant forall ct, c, dt
  //           | ct in children && c in elemsTree(ct) && dt in cs - children
  //           :: dt.root !in c.repr
  //       {
  //         assert forall c, d | c in children && d in elemsTree(c) :: d.Valid();
  //         var ct; ct :| ct in cs - children;
  //         assert ct.root in elemsTree(ct);
  //         assert ct.root.IsChildOf(p);
  //         assert forall c, d | c in children && d in elemsTree(c) :: d.Valid();
  //         assert ct in cs - children;
  //         assert ct !in children;
  //         assert forall c, d | c in children && d in elemsTree(c) :: d.Valid();
  //         ct.root.repr := {ct.root} + p.repr;
  //         assert forall c, d | c in children && d in elemsTree(c) :: d.Valid();
  //         assert elemsTree(ct) <= elemsTree(dt);
  //         assert ct.root.parent == p;
  //         assert p.Valid();
  //         assert ct.root.parent.Valid();
  //         assert ct.root.Valid();
  //         assert elemsTree(ct) !! BigUnion(set t | t in children :: elemsTree(t));
  //         assert forall c, d, e | c in children && d in elemsTree(c) && e in d.repr :: e !in elemsTree(ct);
  //         RepairDescendants(ct);
  //         assert elemsTree(ct) <= elemsTree(dt);
  //         assert ct.root.Valid();
  //         assert forall c, d | c in children && d in elemsTree(c) :: d.Valid();
  //         assert forall d | d in elemsTree(ct) :: d.Valid();
  //         children := children + {ct};
  //       }
  //       assert cs - children == {};
  //       assert children <= cs;
  //       assert cs - children + children == {} + children;
  //       assert cs == children;
  //     }
  //   }
  // }

  // ghost method repair(e: EquivClass, c: EquivClass, top: EquivClass)
  //   modifies e
  // {
  //   e.repr := e.repr - c.repr;
  //   e.repr := e.repr + {c, top};
  // }

  method findAux(c: EquivClass) returns (res: EquivClass)
    decreases c.repr
    modifies multiset(classes[..])
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
      res := findAux(c.parent);
      assert res.Valid();
      assert Valid();
      ghost var dt := DescendantsTree(c);
      c.parent := res;
      // c.height := 1;
      ghost var orepr := c.repr;
      c.repr := {c, res};
      assert c.Valid();
      ghost var cs: set<EquivClass> := Descendants(c);
      assert forall e | e in cs :: e in multiset(classes[..]);
      assert forall e | e in classes[..] && e !in cs :: e.Valid();
      RepairDescendants(dt);
      assert forall e | e in cs :: e.Valid();
      assert forall e: EquivClass | e in classes[..] :: e.Valid();
      assert Valid();
    }
  }

  /*
  method find(i: nat) returns (res: EquivClass)
    modifies this, elems
    modifies set x | x in elems[..]
    modifies BigUnion(set e: EquivClass | e in elems[..] :: e.repr)
    requires Valid()
    requires 0 <= i < elems.Length
    ensures res.parent == null
    ensures res.Valid()
    ensures Valid()
  {
    res := findAux(elems[i]);
  }
  */
}
