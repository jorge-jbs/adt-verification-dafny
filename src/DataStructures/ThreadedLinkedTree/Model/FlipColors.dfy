include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"

module {:options "-functionSyntax:4"} ThreadedLinkedTree.Model.FlipColors {
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
  {
    forall t: trbtree |
        && t.Node?
        && t.left.Node?
        && t.right.Node?
        && t.left.color == NegColor(t.color)
        && t.right.color == NegColor(t.color)
        && SearchTree(t)
      ensures keys(t) == keys(FlipColors(t))
      ensures SearchTree(FlipColors(t))
      ensures BlackHeight(t) == BlackHeight(FlipColors(t))
    {
      FlipColorsSpec(t);
    }
  }

  lemma FlipColorsSize(t: trbtree)
    requires FlipColors.requires(t)
    ensures size(t) == size(FlipColors(t))
  {}

  lemma FlipColorsModel(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(FlipColors(t))
    ensures toMapRec(t) == toMapRec(FlipColors(t))
  {}
}
