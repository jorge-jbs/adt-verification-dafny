include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Rotate.dfy"

module {:options "-functionSyntax:4"} TRBTree.Restore {
  import opened Color
  import opened Base
  import opened FC = FlipColors
  import opened Rotate

  function Restore(t: trbtree): trbtree
    requires t.Node?
  {
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    if isRed(t''.left) && isRed(t''.right) then
      FlipColors(t'')
    else
      t''
  }

  lemma RestoreSpec(t: trbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRed(t.right) && isRed(t.right.left) ==>
      isBlack(t) && isRed(t.left)
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.right)
    )
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.left.left)
    )
    requires BlackHeight(t.left) == BlackHeight(t.right)
    requires RedBlackTree(t.left)
    requires RedBlackTree(t.right)

    ensures keys(t) == keys(Restore(t))
    ensures SearchTree(Restore(t))
    ensures RedBlackTree(Restore(t))

    ensures BlackHeight(Restore(t)) == BlackHeight(t)
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures isRed(t) ==> isRed(Restore(t))
    ensures isRed(Restore(t)) && isRed(Restore(t).left) ==>
      isRed(t) && (isRed(t.left) || isRed(t.right))
    ensures isRed(Restore(t)) && isBlack(t) ==>
      || (isRed(t.left) && isRed(t.right))
      || (isRed(t.left) && isRed(t.left.left))
  {
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';

    if isRed(t.right) {
      RotateLeftSpec(t);
    }
    if isRed(t'.left) && isRed(t'.left.left) {
      RotateRightSpec(t');
    }
    if isRed(t''.left) && isRed(t''.right) {
      FlipColorsSpec(t'');
      assert RedBlackTree(Restore(t)) by {
        assert BlackHeight(t'''.left) == BlackHeight(t'''.right);
        assert RedBlackTree(t'''.left);
        assert RedBlackTree(t'''.right);
        assert (t'''.right.Node? ==> isBlack(t'''.right));
        assert (isRed(t'''.left) && t'''.left.left.Node? ==> isBlack(t'''.left.left));
      }
    } else {
      assert RedBlackTree(Restore(t)) by {
        assert BlackHeight(t'''.left) == BlackHeight(t'''.right);
        assert RedBlackTree(t'''.left);
        assert RedBlackTree(t'''.right);
        assert (t'''.right.Node? ==> isBlack(t'''.right));
        assert (isRed(t'''.left) && t'''.left.left.Node? ==> isBlack(t'''.left.left));
      }
    }
    assert t''' == Restore(t);
  }

  lemma RestoreThreaded(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty)
    requires t.Node?
    requires ThreadedTreeNe(prev, t, next)
    ensures ThreadedTreeNe(prev, Restore(t), next)
  {
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';
    if isRed(t.right) {
      RotateLeftThreaded(prev, t, next);
    }
    if isRed(t'.left) && isRed(t'.left.left) {
      RotateRightThreaded(prev, t', next);
    }
  }
/*
  lemma {:verify false} RestoreModel(t: trbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRed(t.right) && isRed(t.right.left) ==>
      isBlack(t) && isRed(t.left)
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.right)
    )
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.left.left)
    )
    requires BlackHeight(t.left) == BlackHeight(t.right)
    requires RedBlackTree(t.left)
    requires RedBlackTree(t.right)

    ensures SearchTree(Restore(t))
    ensures toMap(t) == toMap(Restore(t))
  {
    RestoreSpec(t);
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';


    if isRed(t.right) {
      RotateLeftModel(t);
      assert toMap(RotateLeft(t)) == toMap(t);
    }
    assert toMap(t) == toMap(t');

    if isRed(t'.left) && isRed(t'.left.left) {
      RotateRightModel(t');
      assert toMap(RotateRight(t')) == toMap(t');
    }
    assert toMap(t') == toMap(t'');

    if isRed(t''.left) && isRed(t''.right) {
      FlipColorsModel(t'');
      assert toMap(FlipColors(t'')) == toMap(t'');
    }
    assert toMap(t'') == toMap(t''');

    assert t''' == Restore(t);
  }
*/
}
