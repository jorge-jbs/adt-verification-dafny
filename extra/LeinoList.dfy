class LNode<A> {
  ghost var repr: set<LNode<A>>;
  ghost var model: seq<A>
  var data: A;
  var next: LNode?<A>;

  constructor(x: A, next: LNode?<A>)
    requires next != null ==> next.Valid()
    ensures Valid()
    ensures model == [x] + (if next == null then [] else next.model)
    ensures forall x | x in repr - (if next == null then {} else next.repr) :: fresh(x)
  {
    this.data := x;
    this.next := next;
    if next == null {
      this.repr := {this};
      this.model := [data];
    } else {
      this.repr := {this} + next.repr;
      this.model := [data] + next.model;
    }
  }

  ghost predicate Valid()
    reads this, repr
  {
    && this in repr
    && (if next == null then
        repr == {this} && model == [data]
      else
        && next in repr
        && repr == {this} + next.repr
        && model == [data] + next.model
        && this !in next.repr
        && next.Valid()
      )
  }
}
