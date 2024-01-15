include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/FlipColors.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/MoveRed.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/FlipColors.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Rotate.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.MoveRed {
  import opened KeyValue
  import opened Model.Color
  import ModelB = Model.Base
  import ModelF = Model.FlipColors
  import ModelR = Model.Rotate
  import ModelM = Model.MoveRed
  import opened T = TTree
  import opened FC = FlipColors
  import opened R = Rotate
  import opened TTNode

  function hue(): int { 1 }

  // 15"
  method MoveRedLeft(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>, 
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>
    )
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires ModelM.MoveRedLeft.requires(TreeModelRec(sk))

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == ModelM.MoveRedLeft(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    newNode := node;
    newSk := sk;
    ghost var t := TreeModelRec(newSk);
    FlipColors(newNode, prev, newSk, next);
    ghost var t' := TreeModelRec(newSk);
    assert newNode.color == t'.color;
    isRedLeftProp(newNode.right, newSk.right);
    if isRedLeft(newNode.right) {
      ghost var newSkRight;
      assert
        && {newNode.right, newNode.right.left} <= elems(newSk) == elems(sk)
        && {newNode, newNode.right, newNode.right.left} !! elems(newSk.left)
        && newNode !in {newNode.right, newNode.right.left}
      by {
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right.left, newSk.right.left);
      }
      label PreRR:
      newNode.right, newSkRight := RotateRight(newNode.right, Thread(newNode), newSk.right, next);
      ghost var t''right := TreeModelRec(newSkRight);
      assert unchanged@PreRR(elems(newSk.left));
      newSk := Node(newSk.left, newNode, newSkRight);
      ghost var t'' := TreeModelRec(newSk);
      assert newNode.color == t''.color;
      assert newNode.color == old@PreRR(newNode.color);
      assert ValidRec(newNode, newSk) by {
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.left, newSk.left);
        assert !newNode.isThreadRight;
      }
      newNode, newSk := RotateLeft(newNode, prev, newSk, next);
      FlipColors(newNode, prev, newSk, next);
      assert TreeModelRec(newSk) == ModelM.MoveRedLeft(old(TreeModelRec(sk))) by {
        assert t' == ModelF.FlipColors(t);
        assert t'' == ModelB.Node(
          t'.left,
          t'.key,
          t'.value,
          ModelR.RotateRight(t'.right),
          t'.color
        ) by {
          assert t''right == ModelR.RotateRight(t'.right);
          assert t'.left == t''.left;
          assert t'.key == t''.key;
          assert t'.value == t''.value;
          assert t'.color == t''.color; 
        }
      }
    }
  }

  // 33"
  method MoveRedRight(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>, 
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>
    )
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadRight
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadLeft

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires ModelM.MoveRedRight.requires(TreeModelRec(sk))

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == ModelM.MoveRedRight(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    newNode := node;
    newSk := sk;
    ghost var t := TreeModelRec(newSk);
    FlipColors(newNode, prev, newSk, next);
    ghost var t' := TreeModelRec(newSk);
    isRedLeftProp(newNode.left, newSk.left);
    if isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, prev, newSk, next);
      assert
        && newNode.right.right != null
        && !newNode.right.isThreadRight
        && TreeModelRec(newSk.right).right.Node?
        && {newNode.right, newNode.right.right} <= elems(newSk) == elems(sk)
        && {newNode, newNode.right, newNode.right.right} !! elems(newSk.left)
      by {
        assert TreeModelRec(newSk).right.right.Node?;
        assert TreeModelRec(newSk.right).right.Node?;
        assert TreeModelRec(newSk.right.right).Node?;
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.right.right, newSk.right.right);
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right, newSk.right);
        assert elems(newSk.left) !! elems(newSk.right);
      }
      FlipColors(newNode, prev, newSk, next);
      ghost var t'' := TreeModelRec(newSk);
      assert newNode.color == t''.color;
      assert newNode !in {newNode.right, newNode.right.right} by {
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.right.right, newSk.right.right);
      }
      label PreRL:
      ghost var newSkRight;
      newNode.right, newSkRight := RotateLeft(newNode.right, Thread(newNode), newSk.right, next);
      ghost var t'''right := TreeModelRec(newSkRight);
      assert unchanged@PreRL(elems(newSk.left));
      newSk := Node(newSk.left, newNode, newSkRight);
      ghost var t''' := TreeModelRec(newSk);
      assert newNode.color == old@PreRL(newNode.color);
      assert newNode.color == t''.color;
      assert ValidRec(newNode, newSk) by {
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.left, newSk.left);
      }
      assert TreeModelRec(newSk) == ModelM.MoveRedRight(old(TreeModelRec(sk))) by {
        assert t' == ModelF.FlipColors(t);
        var t'' := ModelF.FlipColors(ModelR.RotateRight(t'));
        assert t''' == ModelB.Node(
          t''.left,
          t''.key,
          t''.value,
          ModelR.RotateLeft(t''.right),
          t''.color
        ) by {
          assert t'''right == ModelR.RotateLeft(t''.right);
          assert t''.left == t'''.left;
          assert t''.key == t'''.key;
          assert t''.value == t'''.value;
          assert t''.color == t'''.color; 
        }
      }
    }
  }
}
