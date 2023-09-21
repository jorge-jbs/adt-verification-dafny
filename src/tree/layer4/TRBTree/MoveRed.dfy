include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"

module {:options "-functionSyntax:4"} TRBTree.MoveRed {
  import opened Color
  import opened Base
  import opened FP = FlipColors
  import opened Rotate

  function MoveRedLeft(t: rbtree): rbtree
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
      //FlipColors(RotateLeft(t'.(right := Child(RotateRight(t'.right.child)))))
    else
      t'
  }

  lemma {:verify false} MoveRedLeftSize(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    ensures sizeWithPointers(t) == sizeWithPointers(MoveRedLeft(t))
  {
  }

  lemma MoveRedLeftSpec(t: rbtree)
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
    ensures BlackHeightP(MoveRedLeft(t).right) == BlackHeightP(MoveRedLeft(t).left)
    ensures BlackHeight(MoveRedLeft(t)) == BlackHeight(t)

    ensures
      || isRedP(MoveRedLeft(t).left)
      || isRedP(MoveRedLeft(t).left.child.left)
    ensures
      || (!isRed(MoveRedLeft(t)) && isRedP(MoveRedLeft(t).left) && isRedP(MoveRedLeft(t).right) && !isRedP(MoveRedLeft(t).right.child.left) && !isRedP(MoveRedLeft(t).left.child.left))
      || (isRed(MoveRedLeft(t)) && !isRedP(MoveRedLeft(t).left) && !isRedP(MoveRedLeft(t).right) && isRedP(MoveRedLeft(t).left.child.left))
  {
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
    }
  }

  lemma MoveRedLeftThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, MoveRedLeft(t), next)
  {
    var t' := FlipColors(t);
    if isRedP(t'.right.child.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        Child(RotateRight(t'.right.child)),
        t'.color
      );
      RotateRightThreaded(Thread(t'.key), t'.right.child, next);
      RotateLeftThreaded(prev, t'', next);
    }
  }

  function MoveRedRight(t: rbtree): rbtree
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

  lemma {:verify false} MoveRedRightSize(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    ensures sizeWithPointers(t) == sizeWithPointers(MoveRedRight(t))
  {
  }

  lemma MoveRedRightSpec(t: rbtree)
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
    requires !isRedP(t.right.child.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRedP(MoveRedRight(t).right) || isRedP(MoveRedRight(t).right.child.left)
    ensures SearchTree(MoveRedRight(t))
    ensures RedBlackTreeP(MoveRedRight(t).left)
    ensures RedBlackTreeP(MoveRedRight(t).right)
    ensures BlackHeightP(MoveRedRight(t).right) == BlackHeightP(MoveRedRight(t).left)
    ensures BlackHeight(MoveRedRight(t)) == BlackHeight(t)
  {
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRedP(t'.left.child.left) {
      var t'' := FlipColors(RotateRight(t'));
      var t''' :=
        Node(
          t''.left,
          t''.key,
          t''.value,
          Child(RotateLeft(t''.right.child)),
          t''.color
        );
      RotateRightSpec(t');
      FlipColorsSpec(RotateRight(t'));
      RotateLeftSpec(t''.right.child);

      assert RedBlackTreeP(MoveRedRight(t).right) by {
        assert RedBlackTreeP(MoveRedRight(t).right.child.left);
        assert RedBlackTreeP(MoveRedRight(t).right.child.right);
      }
    }
  }

  lemma MoveRedRightThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, MoveRedRight(t), next)
  {
    var t' := FlipColors(t);
    if isRedP(t'.left.child.left) {
      var t'' := FlipColors(RotateRight(t'));
      var t''' :=
        Node(
          t''.left,
          t''.key,
          t''.value,
          Child(RotateLeft(t''.right.child)),
          t''.color
        );
      RotateRightThreaded(prev, t', next);
      RotateLeftThreaded(Thread(t''.key), t''.right.child, next);
    }
  }
}
