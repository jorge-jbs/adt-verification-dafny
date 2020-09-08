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
}

function method BigUnion<A>(S: set<set<A>>): set<A>
{
  set X, x | X in S && x in X :: x
}

class Partition {
  var elems: array<EquivClass>;

  predicate Valid()
    reads this, elems
    reads set x | x in elems[..]
    reads BigUnion(set e: EquivClass | e in elems[..] :: e.repr)
  {
    (forall e: EquivClass | e in elems[..] ::
      e.Valid() && (forall p: EquivClass | p in e.repr :: p in elems[..])
    )
    && (forall j, k | 0 <= j < k < elems.Length :: elems[j] != elems[k])
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
    elems := new EquivClass[size](
      i requires 0 <= i < size reads temp => temp[i]
    );
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
