include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.FlipColors {
  import opened Color
  import opened Base

  function method FlipColors(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    Node(
      Child(Node(
        t.left.child.left,
        t.left.child.key,
        t.left.child.value,
        t.left.child.right,
        NegColor(t.left.child.color)
      )),
      t.key,
      t.value,
      Child(Node(
        t.right.child.left,
        t.right.child.key,
        t.right.child.value,
        t.right.child.right,
        NegColor(t.right.child.color)
      )),
      NegColor(t.color)
    )
  }

  lemma FlipColorsSpec(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires t.left.child.color == NegColor(t.color)
    requires t.right.child.color == NegColor(t.color)
    requires SearchTree(t)
    //requires BlackBalanced(t)
    ensures keys(t) == keys(FlipColors(t))
    ensures SearchTree(FlipColors(t))
    //ensures BlackBalanced(FlipColors(t))
    ensures BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma AllFlipColorsSpec()
    ensures forall t: rbtree
        | t.Node?
        && t.left.Child?
        && t.left.child.Node?
        && t.right.Child?
        && t.right.child.Node?
        && t.left.child.color == NegColor(t.color)
        && t.right.child.color == NegColor(t.color)
        && SearchTree(t)
      :: keys(t) == keys(FlipColors(t))
      && SearchTree(FlipColors(t))
      && BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

/*
  lemma {:verify false} FlipColorsModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(FlipColors(t))
    ensures toMap(t) == toMap(FlipColors(t))
  {
    calc == {
      toMap(FlipColors(t));
      toMap(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)),
          NegColor(t.color)
        )
      );
      toMap(Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)))
        + map[t.key := t.value]
        + toMap(Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)));
      toMap(t.left.left) + map[t.left.key := t.left.value] + toMap(t.left.right)
        + map[t.key := t.value]
        + toMap(t.right.left) + map[t.right.key := t.right.value] + toMap(t.right.right);
      toMap(Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color))
        + map[t.key := t.value]
        + toMap(Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color));
      toMap(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color),
          t.color
        )
      );
      toMap(t);
    }
  }
*/
}
