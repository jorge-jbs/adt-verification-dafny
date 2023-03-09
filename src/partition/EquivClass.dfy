class EquivClass {
  ghost var repr: set<EquivClass>;
  // var height: nat;
  var parent: EquivClass?;

  ghost predicate Valid()
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

  ghost predicate IsChildOf(p: EquivClass)
    reads this, repr
    // requires Valid()
  {
    parent == p
  }

  // The reflexive-transitive closure of `IsChildOf` (on valid EquivClasses)
  ghost predicate IsDescOf(p: EquivClass)
    reads this, repr
    // requires Valid()
  {
    p in repr
  }

  static lemma IsDescOfRefl(a: EquivClass)
    requires a.Valid()
    ensures a.IsDescOf(a)
  {}

  static lemma IsDescOfWeakenRight(a: EquivClass, b: EquivClass)
    decreases a.repr
    requires a.Valid() && b.Valid()
    requires b.parent != null
    requires a.IsDescOf(b)
    ensures a.IsDescOf(b.parent)
  {
    if a != b && a.parent != null {
      IsDescOfWeakenRight(a.parent, b);
    }
  }

  static lemma IsDescOfWeakenLeft(a: EquivClass, b: EquivClass)
    decreases a.repr
    requires a.Valid() && b.Valid()
    requires a.parent != null
    requires a != b
    requires a.IsDescOf(b)
    ensures a.parent.IsDescOf(b)
  {
    if a.parent != b && b.parent != null{
      IsDescOfWeakenLeft(a.parent, b);
    }
  }

  static lemma IsDescOfTrans(a: EquivClass, b: EquivClass, c: EquivClass)
    decreases a.repr
    requires a.Valid()
    requires a.IsDescOf(b) && b.IsDescOf(c)
    ensures a.IsDescOf(c)
  {
    if a.parent != null && a != b {
      IsDescOfTrans(a.parent, b, c);
    }
  }

  static lemma IsDescOfAntisym(a: EquivClass, b: EquivClass)
    decreases b.repr
    requires a.Valid() && b.Valid()
    requires a != b
    requires a.IsDescOf(b)
    ensures !b.IsDescOf(a)
  {
    if b.parent != a && b.parent != null {
      IsDescOfWeakenRight(a, b);
      IsDescOfAntisym(a, b.parent);
    }
  }
}
