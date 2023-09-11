include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"

module TRBTree.MoveRed {
  import opened Color
  import opened Base
  import opened FP = FlipColors
  import opened Rotate

  function method MoveRedLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    var t' := FlipColors(t);
    if isRedP(t'.right.child.left) then
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        Child(RotateRight(t'.right.child)),
        t'.color
      );
      FlipColors(RotateLeft(t''))
    else
      t'
  }

  lemma MoveRedLeftSize(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    ensures sizeWithPointers(t) == sizeWithPointers(MoveRedLeft(t))
  {
    assume false;
  }

  lemma {:verify false} MoveRedLeftSpec(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left.child)
    requires isBlack(t.right.child)
    requires !isRedP(t.left.child.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRedP(MoveRedLeft(t).left) || isRedP(MoveRedLeft(t).left.child.left)
    ensures SearchTree(MoveRedLeft(t))
    ensures RedBlackTreeP(MoveRedLeft(t).left)
    ensures RedBlackTreeP(MoveRedLeft(t).right)
    //ensures BlackBalanced(MoveRedLeft(t))
    ensures BlackHeightP(MoveRedLeft(t).right) == BlackHeightP(MoveRedLeft(t).left)
    ensures BlackHeight(MoveRedLeft(t)) == BlackHeight(t)
    ensures size(MoveRedLeft(t)) == size(t)

    ensures
      || isRedP(MoveRedLeft(t).left)
      || isRedP(MoveRedLeft(t).left.child.left)
    ensures
      || (!isRed(MoveRedLeft(t)) && isRedP(MoveRedLeft(t).left) && isRedP(MoveRedLeft(t).right) && !isRedP(MoveRedLeft(t).right.child.left) && !isRedP(MoveRedLeft(t).left.child.left))
      || (isRed(MoveRedLeft(t)) && !isRedP(MoveRedLeft(t).left) && !isRedP(MoveRedLeft(t).right) && isRedP(MoveRedLeft(t).left.child.left))
  {
    assert size(MoveRedLeft(t)) == size(t) by {
      forall t | RotateRight.requires(t)
        ensures size(t) == size(RotateRight(t))
      {
        RotateRightSize(t);
      }
      assert forall t | RotateRight.requires(t) :: size(t) == size(RotateRight(t));
      assert forall t | RotateLeft.requires(t) :: size(t) == size(RotateLeft(t));
      assert forall t | FlipColors.requires(t) :: size(t) == size(FlipColors(t));
    }
    assume false;
    /*
    AllFlipColorsSpec();
    AllRotateLeftSpec();
    AllRotateRightSpec();
    */
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRedP(t'.right.child.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        Child(RotateRight(t'.right.child)),
        t'.color
      );
      RotateRightSpec(t'.right.child);
      RotateLeftSpec(t'');
      FlipColorsSpec(RotateLeft(t''));

      var t''' := FlipColors(RotateLeft(t''));
      assert t'''.color.Red?;
      assert t'''.left.child.color.Black?;
      assert t'''.right.child.color.Black?;
      assert t'''.left.child.left.child.color.Red?;
      assert !isRedP(t'''.left.child.left.child.left);

      assert t'''.left.child.left.child.left == t.left.child.left;
      assert t'''.left.child.left.child.right == t.left.child.right;
      assert t'''.left.child.right == t.right.child.left.child.left;
      assert t'''.right.child.left == t.right.child.left.child.right;
      assert t'''.right.child.right == t.right.child.right;

      assert (t'''.left.child.right.child.Node? ==> t'''.left.child.right.child.color.Black?);
      assert (t'''.left.child.left.child.Node? && t'''.left.child.left.child.color.Red? && t'''.left.child.left.child.left.child.Node? ==> t'''.left.child.left.child.left.child.color.Black?);

      assert RedBlackTreeP(t.left.child.left);
      assert RedBlackTreeP(t.left.child.right);
      assert RedBlackTreeP(t.right.child.left);
      assert RedBlackTreeP(t.right.child.right);
    } else {
    }
  }

  function method MoveRedRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    var t' := FlipColors(t);
    if isRedP(t'.left.child.left) then
      var t'' := FlipColors(RotateRight(t'));
      Node(
        t''.left,
        t''.key,
        t''.value,
        Child(RotateLeft(t''.right.child)),
        t''.color
      )
    else
      t'
  }

  lemma MoveRedRightSize(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    ensures sizeWithPointers(t) == sizeWithPointers(MoveRedRight(t))
  {
    assume false;
  }
}
