class Node {
    var val: int;
    var next: Node?
    ghost var repr: set<object>;
    ghost var model : seq<int>;

    predicate Valid()
      reads this, repr
      decreases repr
    {
      (next == null ==> model == [val])
        && this in repr
        && (next != null
        ==> next in repr
        && next.repr <= repr
        && this !in next.repr
        && next.Valid()
        && model == [val] + next.model)
    }

    function fmodel () : seq<int>
      requires Valid()
      ensures fmodel() == model  // esta línea la añadí yo
      reads repr
    {
        if next == null then [val]
                        else [val] + next.fmodel()
    }

    constructor (v: int)
      ensures Valid()
      ensures model == [v]
      ensures fmodel() == [v]
      ensures repr == {this}
    {
        val  := v;
        next := null;
        repr := {this};
        model := [v];
    }

    function length() : nat
      requires Valid()
      reads repr
      ensures length() == |fmodel()|
      decreases repr
    {
        if next == null then 1 else 1 + next.length()
    }
}

class List {
    var first : Node?;
    ghost var repr: set<object>;
    ghost var model: seq<int>;

    predicate Valid()
      reads this, repr
    {
      (first == null ==> model == [])
        && this in repr
        && (first != null
        ==> first in repr
        && (model == first.model)
        && first.repr <= repr
        && this !in first.repr
        && first.Valid())
    }

    constructor ()
      ensures Valid()
      ensures fresh(repr)
      ensures model == []
    {
        first := null;
        repr := {this};
        model := [];
    }

    function length (): nat
      requires Valid()
      ensures length () == |model|
      reads repr
    {
        if first == null then 0 else first.length()
    }

    // This adds an element to the left of the list
    method add (v: int)
      requires Valid()
      ensures Valid()
      modifies repr
      ensures fresh(repr - old(repr))
      ensures model == [v] + old(model)
    {
      var node := new Node(v);
      if first == null {
        node.repr := {node};
        node.model := [v];
      } else {
        node.repr := {node} + first.repr;
        node.model := [v] + first.model;
      }
      first, node.next := node, first;
      repr := repr + {node};
      model := first.model;
    }

    method appendAux(v: int, node: Node, extras: set<Node>)
      returns (res: Node)
      decreases node.repr
      requires node.Valid()
      ensures fresh(res)
      ensures res.Valid()
      ensures forall extra | extra in extras :: extra !in res.repr
      ensures res in res.repr
      ensures this !in res.repr
    {
      if node.next == null {
        res := new Node(node.val);
        var nuevo := new Node(v);
        res.next := nuevo;
        res.repr := {res, nuevo};
        res.model := [node.val, v];
      } else {
        res := new Node(node.val);
        var rec := appendAux(v, node.next, {res} + extras);
        res.next := rec;
        res.repr := {res} + res.next.repr;
        res.model := [node.val] + res.next.model;
      }
    }

    method append (v:int)
      requires Valid()
      ensures Valid()
      modifies repr
    {
      if first == null {
        add(v);
      } else {
        first := appendAux(v, first, {});
        repr := first.repr + {this};
        model := first.model;
      }
    }
}

method Main ()
{
    var l := new List();
    assert l.length () == 0;
    l.add(1);
    assert l.length () == 1;
    l.add(2);
    assert l.length() == 2;
    assert l.model == [2,1];
}

    // Exercise: implement and verify an append method adding a cell to the end of the list
method append (v:int)
  //requires Valid()
  //ensures Valid()
  //modifies repr 
