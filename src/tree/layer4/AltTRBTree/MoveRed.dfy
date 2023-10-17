include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Rotate.dfy"

module {:options "-functionSyntax:4"} TRBTree.MoveRed {
  import opened Utils
  import opened Color
  import opened Base
  import opened FP = FlipColors
  import opened Rotate

  function MoveRedLeft(t: trbtree): trbtree
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
      //FlipColors(RotateLeft(t'.(right := Child(RotateRight(t'.right)))))
    else
      t'
  }

  lemma {:verify false} MoveRedLeftSize(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    ensures size(t) == size(MoveRedLeft(t))
  {}

  lemma MoveRedLeftSpec(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.left.left)
    ensures keys(t) == keys(MoveRedLeft(t))
    ensures isRed(MoveRedLeft(t).left) || isRed(MoveRedLeft(t).left.left)
    ensures SearchTree(MoveRedLeft(t))
    ensures RedBlackTree(MoveRedLeft(t).left)
    ensures RedBlackTree(MoveRedLeft(t).right)
    ensures BlackHeight(MoveRedLeft(t).right) == BlackHeight(MoveRedLeft(t).left)
    ensures BlackHeight(MoveRedLeft(t)) == BlackHeight(t)

    ensures
      || isRed(MoveRedLeft(t).left)
      || isRed(MoveRedLeft(t).left.left)
    ensures
      || (!isRed(MoveRedLeft(t)) && isRed(MoveRedLeft(t).left) && isRed(MoveRedLeft(t).right) && !isRed(MoveRedLeft(t).right.left) && !isRed(MoveRedLeft(t).left.left))
      || (isRed(MoveRedLeft(t)) && !isRed(MoveRedLeft(t).left) && !isRed(MoveRedLeft(t).right) && isRed(MoveRedLeft(t).left.left))
  {
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

      if !t.right.left.color.Black? {
        assert MoveRedLeft(t).Node?;
        assert MoveRedLeft(t).left.left.left == t.left.left;
        assert MoveRedLeft(t).left.left.right == t.left.right;
        assert !t.right.left.left.Thread? ==> MoveRedLeft(t).left.right == t.right.left.left;
        assert !t.right.left.right.Thread? ==> MoveRedLeft(t).right.left == t.right.left.right;
        assert MoveRedLeft(t).right.right == t.right.right;
        assert RedBlackTree(MoveRedLeft(t).left) by {
          assert BlackHeight(MoveRedLeft(t).left.left) == BlackHeight(MoveRedLeft(t).left.right) by {
            if !t.right.left.left.Thread? {
              calc == {
                BlackHeight(MoveRedLeft(t).left.left);
                max(BlackHeight(MoveRedLeft(t).left.left.left), BlackHeight(MoveRedLeft(t).left.left.right));
                max(BlackHeight(t.left.left), BlackHeight(t.left.right));
                BlackHeight(t.left.left);
                BlackHeight(t.left) - 1;
                BlackHeight(t) - 1;
                BlackHeight(t.right) - 1;
                BlackHeight(t.right.left);
                max(BlackHeight(t.right.left.left), BlackHeight(t.right.left.right));
                {
                  assert RedBlackTree(t.right.left);
                  assert BlackHeight(t.right.left.left) == BlackHeight(t.right.left.right);
                }
                BlackHeight(t.right.left.left);
                BlackHeight(MoveRedLeft(t).left.right);
              }
            } else {
              assert t.right.left.left.Thread?;
              assert MoveRedLeft(t).left.right == Thread(MoveRedLeft(t).key);
              calc == {
                BlackHeight(t.right.left.left);
                {
                  assert RedBlackTree(t.right.left);
                  assert BlackHeight(t.right.left.left) == BlackHeight(t.right.left.right);
                }
                max(BlackHeight(t.right.left.left), BlackHeight(t.right.left.right));
                BlackHeight(t.right.left);
                BlackHeight(t.right) - 1;
                BlackHeight(t) - 1;
                BlackHeight(t.left) - 1;
                BlackHeight(t.left.left);
              }
              if t.left.left.Node? {
                assert t.left.left.color.Black?;
                assert BlackHeight(t.left.left) >= 1;
                assert false;
              } else {
                assert BlackHeight(MoveRedLeft(t).left.left) == BlackHeight(MoveRedLeft(t).left.right);
              }
            }
          }
          assert RedBlackTree(MoveRedLeft(t).left.right) by {
            if !t.right.left.left.Thread? {
              assert RedBlackTree(t);
              assert RedBlackTree(t.right);
              assert RedBlackTree(t.right.left);
              assert RedBlackTree(t.right.left.left);
            }
          }
        }
        assert RedBlackTree(MoveRedLeft(t).right) by {
          assert RedBlackTree(MoveRedLeft(t).right.left) by {
            if !t.right.left.right.Thread? {
              assert MoveRedLeft(t).right.left == t.right.left.right;
              assert RedBlackTree(t.right.left);
              assert RedBlackTree(t.right.left.right);
            }
          }
          assert RedBlackTree(MoveRedLeft(t).right.right) by {
            assert MoveRedLeft(t).right.right == t.right.right;
            assert RedBlackTree(t.right.right);
          }
          assert BlackHeight(MoveRedLeft(t).right.left) == BlackHeight(MoveRedLeft(t).right.right) by {
            calc == {
              BlackHeight(MoveRedLeft(t).right.left);
              BlackHeight(t.right.left.right);
              {
                assert RedBlackTree(t.right.left);
                assert BlackHeight(t.right.left.left) == BlackHeight(t.right.left.right);
              }
              max(BlackHeight(t.right.left.left), BlackHeight(t.right.left.right));
              BlackHeight(t.right.left);
              BlackHeight(t.right.right);
              BlackHeight(MoveRedLeft(t).right.right);
            }
          }
          assert isRed(MoveRedLeft(t).right.left) ==> !isRed(MoveRedLeft(t).right.left.left) by {
            if !t.right.left.right.Thread? {
              assert MoveRedLeft(t).right.left == t.right.left.right;
              assert RedBlackTree(t.right.left);
              assert RedBlackTree(t.right.left.right);
            }
          }
        }
      }
    }
  }

  lemma MoveRedLeftThreaded(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires ThreadedTreeNe(prev, t, next)
    ensures ThreadedTreeNe(prev, MoveRedLeft(t), next)
  {
    var t' := FlipColors(t);
    if isRed(t'.right.left) {
      var t'' := Node(
        t'.left,
        t'.key,
        t'.value,
        RotateRight(t'.right),
        t'.color
      );
      RotateRightThreaded(Thread(t'.key), t'.right, next);
      RotateLeftThreaded(prev, t'', next);
    }
  }

  function MoveRedRight(t: trbtree): trbtree
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

  lemma {:verify false} MoveRedRightSize(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    ensures size(t) == size(MoveRedRight(t))
  {}

  lemma MoveRedRightSpec(t: trbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires isRed(t)
    requires isBlack(t.left)
    requires isBlack(t.right)
    requires !isRed(t.right.left)
    ensures keys(t) == keys(MoveRedRight(t))
    ensures isRed(MoveRedRight(t).right) || isRed(MoveRedRight(t).right.left)
    ensures SearchTree(MoveRedRight(t))
    ensures RedBlackTree(MoveRedRight(t).left)
    ensures RedBlackTree(MoveRedRight(t).right)
    ensures BlackHeight(MoveRedRight(t).right) == BlackHeight(MoveRedRight(t).left)
    ensures BlackHeight(MoveRedRight(t)) == BlackHeight(t)
  {
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

      assert RedBlackTree(MoveRedRight(t).left) by {
        if !t.left.left.color.Black? {
          assert MoveRedRight(t).left.left == t.left.left.left;
          assert MoveRedRight(t).left.right == t.left.left.right;
          assert !t.left.right.Thread? ==> MoveRedRight(t).right.left.left == t.left.right;
          /*
          calc == {
            MoveRedRight(t).right.left.left;
            RotateLeft(t''.right).left.left;
            RotateLeft(FlipColors(RotateRight(t')).right).left.left;
            RotateLeft(RotateRight(t').right).left.left;
            RotateRight(t).right.left;
            t.left.right;
          }
          */
          /*
          calc == {
            MoveRedRight(t).right.left.right;
            RotateLeft(t''.right).left.right;
            RotateLeft(FlipColors(RotateRight(t')).right).left.right;
            RotateLeft(RotateRight(t').right).left.right;
            RotateLeft(RotateRight(t).right).left.right;
            RotateRight(t).right.right.left;
            t.right.left;
          }
          */
          assert !t.right.left.Thread? ==> MoveRedRight(t).right.left.right == t.right.left;
          assert MoveRedRight(t).right.right == t.right.right;
          if MoveRedRight(t).left.right.Node? {
            assert MoveRedRight(t).left.right.color.Black? by {
              assert t.left.left.right.Node?;
              assert RedBlackTree(t.left.left);
              assert t.left.left.right.color.Black?;
            }
          }
          assert BlackHeight(MoveRedRight(t).left.left) == BlackHeight(MoveRedRight(t).left.right) by {
            assert RedBlackTree(t.left.left);
          } 
        }
      }
      assert RedBlackTree(MoveRedRight(t).right) by {
        assert RedBlackTree(MoveRedRight(t).right.left);
        assert RedBlackTree(MoveRedRight(t).right.right);
      }
    }
  }

  lemma MoveRedRightThreaded(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires ThreadedTreeNe(prev, t, next)
    ensures ThreadedTreeNe(prev, MoveRedRight(t), next)
  {
    var t' := FlipColors(t);
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
      RotateRightThreaded(prev, t', next);
      RotateLeftThreaded(Thread(t''.key), t''.right, next);
    }
  }
}
