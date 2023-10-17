include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module {:options "-functionSyntax:4"} TRBTree.FlipColors {
  import opened Color
  import opened Base

  function FlipColors(t: trbtree): trbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    Node(
      Node(
        t.left.left,
        t.left.key,
        t.left.value,
        t.left.right,
        NegColor(t.left.color)
      ),
      t.key,
      t.value,
      Node(
        t.right.left,
        t.right.key,
        t.right.value,
        t.right.right,
        NegColor(t.right.color)
      ),
      NegColor(t.color)
    )
    /*
    Node(
      t.left.(color := NegColor(t.left.color)),
      t.key,
      t.value,
      t.right.(color := NegColor(t.right.color)),
      NegColor(t.color)
    )
    */
  }

  lemma FlipColorsSpec(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires t.left.color == NegColor(t.color)
    requires t.right.color == NegColor(t.color)
    requires SearchTree(t)
    //requires BlackBalanced(t)
    ensures keys(t) == keys(FlipColors(t))
    ensures SearchTree(FlipColors(t))
    //ensures BlackBalanced(FlipColors(t))
    ensures BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma AllFlipColorsSpec()
    ensures
      forall t: trbtree |
          && t.Node?
          && t.left.Node?
          && t.right.Node?
          && t.left.color == NegColor(t.color)
          && t.right.color == NegColor(t.color)
          && SearchTree(t) ::
        && keys(t) == keys(FlipColors(t))
        && SearchTree(FlipColors(t))
        && BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma FlipColorsSize(t: trbtree)
    requires FlipColors.requires(t)
    ensures size(t) == size(FlipColors(t))
  {}

/*
  lemma FlipColorsModel(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
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
