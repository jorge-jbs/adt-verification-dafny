include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"

module {:options "-functionSyntax:4"} TRBTree.Restore {
  import opened Color
  import opened Base
  import opened FC = FlipColors
  import opened Rotate

  function Restore(t: rbtree): rbtree
    requires t.Node?
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    if isRedP(t''.left) && isRedP(t''.right) then
      FlipColors(t'')
    else
      t''
  }

  lemma RestoreSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRedP(t.right) && isRedP(t.right.child.left) ==>
      isBlack(t) && isRedP(t.left)
    requires !(
      && isRed(t)
      && isRedP(t.left)
      && isRedP(t.right)
    )
    requires !(
      && isRed(t)
      && isRedP(t.left)
      && isRedP(t.left.child.left)
    )
    requires BlackHeightP(t.left) == BlackHeightP(t.right)
    requires RedBlackTreeP(t.left)
    requires RedBlackTreeP(t.right)

    ensures keys(t) == keys(Restore(t))
    ensures SearchTree(Restore(t))
    ensures RedBlackTree(Restore(t))

    ensures BlackHeight(Restore(t)) == BlackHeight(t)
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRedP(Restore(t).left)
    ensures isRed(t) ==> isRed(Restore(t))
    ensures isRed(Restore(t)) && isRedP(Restore(t).left) ==>
      isRed(t) && (isRedP(t.left) || isRedP(t.right))
    ensures isRed(Restore(t)) && isBlack(t) ==>
      || (isRedP(t.left) && isRedP(t.right))
      || (isRedP(t.left) && isRedP(t.left.child.left))
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRedP(t''.left) && isRedP(t''.right) then
        FlipColors(t'')
      else
        t'';

    if isRedP(t.right) {
      RotateLeftSpec(t);
    }
    if isRedP(t'.left) && isRedP(t'.left.child.left) {
      RotateRightSpec(t');
    }
    if isRedP(t''.left) && isRedP(t''.right) {
      FlipColorsSpec(t'');
      assert RedBlackTree(Restore(t)) by {
        assert BlackHeightP(t'''.left) == BlackHeightP(t'''.right);
        assert RedBlackTreeP(t'''.left);
        assert RedBlackTreeP(t'''.right);
        assert (isNode(t'''.right) ==> isBlackP(t'''.right));
        assert (isRedP(t'''.left) && isNode(t'''.left.child.left) ==> isBlackP(t'''.left.child.left));
      }
    } else {
      assert RedBlackTree(Restore(t)) by {
        assert BlackHeightP(t'''.left) == BlackHeightP(t'''.right);
        assert RedBlackTreeP(t'''.left);
        assert RedBlackTreeP(t'''.right);
        assert (isNode(t'''.right) ==> isBlackP(t'''.right));
        assert (isRedP(t'''.left) && isNode(t'''.left.child.left) ==> isBlackP(t'''.left.child.left));
      }
    }
    assert t''' == Restore(t);
  }

  lemma RestoreThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, Restore(t), next)
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRedP(t''.left) && isRedP(t''.right) then
        FlipColors(t'')
      else
        t'';
    if isRedP(t.right) {
      RotateLeftThreaded(prev, t, next);
    }
    if isRedP(t'.left) && isRedP(t'.left.child.left) {
      RotateRightThreaded(prev, t', next);
    }
  }
/*
  lemma {:verify false} RestoreModel(t: rbtree)
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
