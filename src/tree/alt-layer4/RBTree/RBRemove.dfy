include "../../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"

module RBTree.RBRemove {
  import opened KeyValue

  import opened Base
  import opened RBInsert

  function method MoveRedLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    var t' := FlipColors(t);
    if isRed(t'.right.left) then
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      FlipColors(RotateLeft(t''))
    else
      t'
  }

  lemma MoveRedLeftSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.left.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRed(MoveRedLeft(t).left) || isRed(MoveRedLeft(t).left.left)
    ensures SearchTree(MoveRedLeft(t))
    ensures RedBlackTree(MoveRedLeft(t).left)
    ensures RedBlackTree(MoveRedLeft(t).right)
    //ensures BlackBalanced(MoveRedLeft(t))
    ensures BlackHeight(MoveRedLeft(t).right) == BlackHeight(MoveRedLeft(t).left)
    ensures BlackHeight(MoveRedLeft(t)) == BlackHeight(t)
    ensures size(MoveRedLeft(t)) == size(t)
  {
    assert size(MoveRedLeft(t)) == size(t) by {
      assert forall t | RotateRight.requires(t) :: size(t) == size(RotateRight(t));
      assert forall t | RotateLeft.requires(t) :: size(t) == size(RotateLeft(t));
      assert forall t | FlipColors.requires(t) :: size(t) == size(FlipColors(t));
    }
    /*
    AllFlipColorsSpec();
    AllRotateLeftSpec();
    AllRotateRightSpec();
    */
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRed(t'.right.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      RotateRightSpec(t'.right);
      RotateLeftSpec(t'');
      FlipColorsSpec(RotateLeft(t''));

      var t''' := FlipColors(RotateLeft(t''));
      assert t'''.color.Red?;
      assert t'''.left.color.Black?;
      assert t'''.right.color.Black?;
      assert t'''.left.left.color.Red?;
      assert !isRed(t'''.left.left.left);

      assert t'''.left.left.left == t.left.left;
      assert t'''.left.left.right == t.left.right;
      assert t'''.left.right == t.right.left.left;
      assert t'''.right.left == t.right.left.right;
      assert t'''.right.right == t.right.right;

      assert (t'''.left.right.Node? ==> t'''.left.right.color.Black?);
      assert (t'''.left.left.Node? && t'''.left.left.color.Red? && t'''.left.left.left.Node? ==> t'''.left.left.left.color.Black?);

      assert RedBlackTree(t.left.left);
      assert RedBlackTree(t.left.right);
      assert RedBlackTree(t.right.left);
      assert RedBlackTree(t.right.right);
    } else {
    }
  }

  function method MoveRedRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    var t' := FlipColors(t);
    if isRed(t'.left.left) then
      var t'' := FlipColors(RotateRight(t'));
      Node(
        t''.left,
        t''.key,
        t''.value,
        RotateLeft(t''.right),
        t''.color
      )
    else
      t'
  }

  lemma MoveRedRightSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.right.left)
    ensures keys(t) == keys(FlipColors(t))
    ensures isRed(MoveRedRight(t).right) || isRed(MoveRedRight(t).right.left)
    ensures SearchTree(MoveRedRight(t))
    ensures RedBlackTree(MoveRedRight(t).left)
    ensures RedBlackTree(MoveRedRight(t).right)
    ensures BlackHeight(MoveRedRight(t).right) == BlackHeight(MoveRedRight(t).left)
    ensures BlackHeight(MoveRedRight(t)) == BlackHeight(t)
    ensures size(MoveRedRight(t)) == size(t)
  {
    assert size(MoveRedRight(t)) == size(t) by {
      assert forall t | RotateRight.requires(t) :: size(t) == size(RotateRight(t));
      assert forall t | RotateLeft.requires(t) :: size(t) == size(RotateLeft(t));
      assert forall t | FlipColors.requires(t) :: size(t) == size(FlipColors(t));
    }
    var t' := FlipColors(t);
    FlipColorsSpec(t);
    if isRed(t'.left.left) {
      var t'' := FlipColors(RotateRight(t'));
      var t''' :=
        Node(
          t''.left,
          t''.key,
          t''.value,
          RotateLeft(t''.right),
          t''.color
        );
      RotateRightSpec(t');
      FlipColorsSpec(RotateRight(t'));
      RotateLeftSpec(t''.right);

      assert RedBlackTree(t.left.left);
      assert RedBlackTree(t.left.right);
      assert RedBlackTree(t.right.left);
      assert RedBlackTree(t.right.right);
    }
  }

  function method RemoveMin(t: rbtree): (rbtree, K, V)
    decreases size(t)
    requires t.Node?
    requires isRed(t) || isRed(t.left)
    requires SearchTree(t)
    requires RedBlackTree(t)
  {
    if t.left.Empty? then
      (t, t.key, t.value)
    else
      var t' :=
        if isBlack(t.left) && !isRed(t.left.left) then
          MoveRedLeftSpec(t);
          MoveRedLeft(t)
        else
          t;
      var (l', minK, minV) := RemoveMin(t'.left);
      ( Restore(
          Node(
            l',
            t'.key,
            t'.value,
            t'.right,
            t'.color
          )
        )
      , minK
      , minV
      )
  }

  function method Remove(t: rbtree, k: K): rbtree
    decreases size(t)
    requires t.Empty? || isRed(t) || isRed(t.left)
    requires SearchTree(t)
    requires RedBlackTree(t)
  {
    if t.Empty? then
      t
    else
      if t.key > k then
        var t' :=
          if isBlack(t.left) && !isRed(t.left.left) then
            MoveRedLeftSpec(t);
            MoveRedLeft(t)
          else
            t;
        Node(
          Remove(t'.left, k),
          t'.key,
          t'.value,
          t'.right,
          t'.color
        )
      else
        var t' :=
          if isRed(t.left) then
            RotateRightSpec(t);
            RotateRight(t)
          else
            t;
        if k == t'.key && t'.right.Empty? then
          t'.left
        else
          var t'' :=
            if isBlack(t'.right) && !isRed(t'.right.left) then
              MoveRedRightSpec(t');
              MoveRedRight(t')
            else
              t';
          if k != t''.key then
            Restore(
              Node(
                t''.left,
                t''.key,
                t''.value,
                Remove(t''.right, k),
                t''.color
              )
            )
          else
            var (r', minK, minV) := RemoveMin(t''.right);
            Restore(
              Node(
                t''.left,
                minK,
                minV,
                r',
                t''.color
              )
            )
  }
}
