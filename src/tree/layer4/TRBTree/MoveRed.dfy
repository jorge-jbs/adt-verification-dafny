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
}
