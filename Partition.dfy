class EquivClass {
  ghost var repr: set<object>;
  var height: nat;
  var parent: EquivClass?;

  predicate Valid()
    reads this, repr
  {
    if parent == null then
      repr == {this}
      && height == 0
    else
      parent in repr
      && this !in parent.repr
      && height == 1 + parent.height
      && repr == {this} + parent.repr
      // && repr >= {this} + parent.repr
      && parent.Valid()
  }

  constructor()
    ensures Valid()
    ensures parent == null
    ensures fresh(repr)
  {
    height := 0;
    parent := null;
    repr := {this};
  }

  predicate IsChildOf(p: EquivClass)
    reads this, repr
    requires Valid()
  {
    p in repr
  }

  static lemma IsChildOfRefl(a: EquivClass)
    requires a.Valid()
    ensures a.IsChildOf(a)
  {}

  static lemma IsChildOfWeakenRight(a: EquivClass, b: EquivClass)
    requires a.Valid() && b.Valid()
    requires b.parent != null
    requires a.IsChildOf(b)
    ensures a.IsChildOf(b.parent)

  static lemma IsChildOfWeakenLeft(a: EquivClass, b: EquivClass)
    requires a.Valid() && b.Valid()
    requires a.parent != null
    requires a.IsChildOf(b)
    ensures a.parent.IsChildOf(b)

  static lemma IsChildOfWeakenLeftPrime(a: EquivClass, b: EquivClass)
    requires a.Valid() && b.Valid()
    requires a.parent != null
    requires !a.parent.IsChildOf(b)
    ensures !a.IsChildOf(b)
  {
    if a.IsChildOf(b) {
      IsChildOfWeakenLeft(a, b);
    }
  }

  static lemma IsChildOfTrans(a: EquivClass, b: EquivClass, c: EquivClass)
    decreases a.repr
    requires a.Valid() && b.Valid() && c.Valid()
    requires a.IsChildOf(b) && b.IsChildOf(c)
    ensures a.IsChildOf(c)
  {
    if a.parent != null && a != b {
      IsChildOfTrans(a.parent, b, c);
    }
  }

  static lemma IsChildOfAntisym(a: EquivClass, b: EquivClass)
    decreases b.repr
    requires a.Valid() && b.Valid()
    requires a != b
    requires a.IsChildOf(b)
    ensures !b.IsChildOf(a)
  {
    if b.parent != a && b.parent != null {
      IsChildOfWeakenRight(a, b);
      IsChildOfAntisym(a, b.parent);
    }
  }

  // static lemma IsChildOfTransPrime(a: EquivClass, b: EquivClass, c: EquivClass)
  //   decreases a.repr
  //   requires a.Valid() && b.Valid() && c.Valid()
  //   requires !a.IsChildOf(b) && b.IsChildOf(c)
  //   ensures !a.IsChildOf(c)
  // {
  //   if a.parent != null && a != b {
  //     if a != c {
  //       IsChildOfTransPrime(a.parent, b, c);
  //     } else {
  //       assert !a.IsChildOf(b);
  //       assert b.IsChildOf(a);
  //       IsChildOfAntisym(b, a);
  //       // assert a.IsChildOf(b);
  //       assert !a.IsChildOf(a);
  //       assert !a.IsChildOf(c);
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
      e.Valid() && (forall p: EquivClass | p in e.repr :: p in classes[..])
    )
    && (forall j, k | 0 <= j < k < classes.Length :: classes[j] != classes[k])
  }

  constructor(size: nat)
    ensures Valid()
  {
    new;  // ¿¿¿¿qué hace esto???? .-.
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

  lemma IsChildOfTransPrimeForall(a: EquivClass, c: EquivClass)
    requires a.Valid() && c.Valid()
    requires !a.IsChildOf(c)
    ensures forall b | b in classes[..] :: a.IsChildOf(b) ==> !a.IsChildOf(c)

  lemma IsChildOfTransPrimeForall2(a: EquivClass)
    requires a.Valid()
    requires Valid()
    ensures forall b | b in classes[..] :: a.IsChildOf(b) ==> !b.IsChildOf(a)

  function method ChildrenAuxAux(c: EquivClass, p: EquivClass):
      (set<EquivClass>, bool)
    decreases c.repr
    reads this, classes, elems(classes), ValidReads()
    requires Valid()
    requires p in classes[..]
    requires c in classes[..]
    ensures forall e: EquivClass | e in classes[..]
      :: e in ChildrenAuxAux(c, p).0 <==> c.IsChildOf(e) && e.IsChildOf(p)
    ensures ChildrenAuxAux(c, p).1 <==> c.IsChildOf(p)
  {
    if c == p then
      IsChildOfTransPrimeForall2(c);
      ({c}, true)
    else if c.parent == null then
      ({}, false)
    else
      var rec := ChildrenAuxAux(c.parent, p);
      if rec.1 then
        (rec.0 + {c}, true)
      else
        EquivClass.IsChildOfWeakenLeftPrime(c, p);
        IsChildOfTransPrimeForall(c, p);
        rec
  }

  // function method ChildrenAux(i: nat, p: EquivClass): set<EquivClass>
  //   reads this, classes, elems(classes), ValidReads()
  //   decreases classes.Length - i
  //   requires Valid()
  //   requires i <= classes.Length
  //   requires p in classes[..]
  //   ensures forall e, d
  //     | e in classes[i..] && d in classes[i..] && e.IsChildOf(d)
  //     :: e in ChildrenAux(i, p) <==> e.IsChildOf(p)
  // {
  //   if i == classes.Length then
  //     assert forall e: EquivClass
  //       | e in classes[i..]
  //       :: e in {} <==> e.IsChildOf(p);
  //     {}
  //   else
  //     var c := classes[i];
  //     var rec := ChildrenAux(i+1, p);
  //     // if classes[i] in rec then
  //     //   assert forall e: EquivClass
  //     //     | e in classes[i..]
  //     //     :: e in rec <==> e.IsChildOf(p);
  //     //   rec
  //     // else
  //       assert forall e, d: EquivClass
  //         | e in classes[i+1..] && d in classes[i+1..] && e.IsChildOf(d)
  //         :: e in rec <==> e.IsChildOf(p);
  //       assert forall e: EquivClass | e in classes[..]
  //         :: e in ChildrenAuxAux(c, p).0 <==> c.IsChildOf(e) && e.IsChildOf(p);
  //       assert forall e, d
  //         | e in classes[i..] && d in classes[i..] && e.IsChildOf(d)
  //         :: e in rec + ChildrenAuxAux(c, p).0 <==> e.IsChildOf(p);
  //       // assert forall e: EquivClass
  //       //   | e in classes[i..]
  //       //   :: e in rec + ChildrenAuxAux(classes[i], p).0 <==> e.IsChildOf(p);
  //       rec + ChildrenAuxAux(c, p).0
  // }

  // function method ChildrenAux(i: nat, p: EquivClass): set<EquivClass>
  //   reads this, classes, elems(classes), ValidReads()
  //   decreases classes.Length - i
  //   requires Valid()
  //   requires i <= classes.Length
  //   requires p in classes[..]
  //   ensures forall e: EquivClass
  //   | e in classes[i..]
  //   :: e in ChildrenAux(i, p) <==> e.IsChildOf(p)

  function Children(p: EquivClass): set<EquivClass>
    reads this, classes, elems(classes), ValidReads()
    requires Valid()
    requires p in classes[..]
  {
    set c | c in classes[..] && c.IsChildOf(p) :: c
  }

  /*
  method findAux(c: EquivClass) returns (res: EquivClass)
    decreases c.repr
    modifies c, c.repr
    requires Valid()
    requires c.Valid()
    ensures res in old(c.repr)
    ensures res.parent == null
    ensures res.Valid()
    ensures c.Valid()
    ensures c.parent == null || c.parent == res
    ensures Valid()
  {
    if c.parent == null {
      return c;
    } else {
      res := findAux(c.parent);
      assert Valid();
      c.parent := res;
      c.height := 1;
      c.repr := {c, res};
      assert c.Valid();
      assert Valid();
    }
  }

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
