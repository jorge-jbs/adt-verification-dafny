include "../../../../src/MUtils.dfy"
include "../../../../src/tree/alt-layer4/LinkedTree/RBInsert.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBRemove.dfy"
include "../../../../src/tree/alt-layer4/Tree.dfy"
include "../../../../src/tree/alt-layer4/TNode.dfy"
include "../../../../src/tree/alt-layer4/Color.dfy"

module LinkedTree.RBRemove {
  import opened Utils
  import opened KeyValue
  import RB = RBTree.Base
  import RBi = RBTree.RBInsert
  import RBr = RBTree.RBRemove
  import opened T = Tree
  import opened TNode
  import opened Color
  import opened RBInsert
  
  method {:verify false} MoveRedLeft(node: TNode, ghost sk: tree<TNode>)  // 50"
      returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right
    //modifies elems(sk)

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.left.left)

    requires TreeModelRec(sk).left.Node?;  /* redundant */
    requires TreeModelRec(sk).right.Node?;  /* redundant */

    ensures ValidRec(newNode, newSk)

    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == RBr.MoveRedLeft(old(TreeModelRec(sk)))
    //ensures size(newSk) == size(sk)
    //ensures size(newSk.left) < size(sk)

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    ghost var t := TreeModelRec(sk);
    FlipColors(node, sk);
    ghost var t' := RBi.FlipColors(t);
    newNode := node;
    newSk := sk;
    assert TreeModelRec(newSk) == t';
    isRedProp(newNode.right.left, newSk.right.left);
    if isRed(newNode.right.left) {
      assert newNode.right.left != null && newNode.right.left.color.Red?;
      //assert size(newSk.left) < size(sk);
      ghost var newSkRight;
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right, newSk.right);
      assert ValidRec(newNode.right.left, newSk.right.left);
      assert elems(newSk.left) !! elems(newSk.right);
      label PreRR:
      newNode.right, newSkRight := RotateRight(newNode.right, newSk.right);
      newSk := Node(newSk.left, newNode, newSkRight);
      //assert size(newSk.left) < size(sk);
      assert unchanged@PreRR(elems(newSk.left));
      assert ValidRec(newNode.right, newSk.right);
      assert ValidRec(newNode.left, newSk.left);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right.right, newSk.right.right);
      assert newNode.right.right != null;
      assert TreeModelRec(newSk).right.right.Node?;
      var t'' := RB.Node(
        t'.left,
        t'.key,
        t'.value,
        RBi.RotateRight(t'.right),
        t'.color
      );
      assert TreeModelRec(newSk) == t'';
      label PreRL:
      newNode, newSk := RotateLeft(newNode, newSk);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right, newSk.right);
      assert newNode.left != null;
      assert TreeModelRec(newSk).right.Node?;
      assert newNode.right != null;
      //assume size(newSk.left) < size(sk);
      assert TreeModelRec(newSk) == RBi.RotateLeft(t'');
      label PreFlip:
      FlipColors(newNode, newSk);
      //assert size(newSk.left) < size(sk);
      assert TreeModelRec(newSk) == RBi.FlipColors(RBi.RotateLeft(t''));
    } else {
    }
  }

  method {:verify false} MoveRedRight(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.right.left)

    requires TreeModelRec(sk).left.Node?;  /* redundant */
    requires TreeModelRec(sk).right.Node?;  /* redundant */

    ensures ValidRec(newNode, newSk)

    ensures TreeModelRec(newSk) == RBr.MoveRedRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)
    //ensures size(newSk) == size(sk)
    //ensures size(newSk.right) < size(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    FlipColors(node, sk);
    newNode := node;
    newSk := sk;
    isRedProp(newNode.left.left, newSk.left.left);
    if isRed(newNode.left.left) {
      assert newNode.left.left != null && newNode.left.left.color.Red?;
      newNode, newSk := RotateRight(newNode, newSk);
      FlipColors(newNode, newSk);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.left, newSk.left);
      assert elems(newSk.left) !! elems(newSk.right);
      ghost var newSkRight;
      label PreRL:
      newNode.right, newSkRight := RotateLeft(newNode.right, newSk.right);
      assert unchanged@PreRL(elems(newSk.left));
      assert unchanged@PreRL(newNode.left);
      assert old@PreRL(ValidRec(newNode.left, newSk.left));
      assume false;
      assert ValidRec(newNode.left, newSk.left);
      newSk := Node(newSk.left, newNode, newSkRight);
      assert ValidRec(newNode, newSk);
      assume false;
    } else {
    }
  }

  lemma Allocated(x: object)
    ensures allocated(x)
  {}

  lemma AllocatedAll(xs: set<object>)
    ensures allocated(xs)
  {}

  method {:verify true} RemoveMinRec(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    decreases RB.size(TreeModelRec(sk))
    modifies elems(sk)
    //modifies set n | n in elems(sk) :: n`color
    //modifies set n | n in elems(sk) :: n`left
    //modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires !(isRed(node) && isRed(node.left))
    requires isRed(node) || isRed(node.left)

    requires RB.isRed(TreeModelRec(sk)) || RB.isRed(TreeModelRec(sk.left)) /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBr.RemoveMin(old(TreeModelRec(sk))).0
    ensures removedNode.key == RBr.RemoveMin(old(TreeModelRec(sk))).1
    ensures removedNode.value == RBr.RemoveMin(old(TreeModelRec(sk))).2
    ensures elems(newSk) == elems(sk) - {removedNode}

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
    } else {
      newNode := node;
      newSk := sk;
      isRedProp(newNode.left.left, newSk.left.left);
      if isBlack(newNode.left) && !isRed(newNode.left.left) {
        RBr.MoveRedLeftSpec(TreeModelRec(newSk));
        newNode, newSk := MoveRedLeft(newNode, newSk);
        isRedProp(newNode.left, newSk.left);
        isRedProp(newNode.left.left, newSk.left.left);
        assert isRed(newNode.left) || isRed(newNode.left.left);
        assert !(isRed(newNode.left) && isRed(newNode.left.left));
      }
      var newNodeLeft;
      ghost var newSkLeft;
      label PreRec:
      assert RB.size(TreeModelRec(newSk.left)) < RB.size(old(TreeModelRec(sk)));
      assert ValidRec(newNode.left, newSk.left);
      assert SearchTreeRec(newSk.left);
      assert RedBlackTreeRec(newSk.left);
      assert !(isRed(newNode.left) && isRed(newNode.left.left));
      assert isRed(newNode.left) || isRed(newNode.left.left);
      assert RB.isRed(TreeModelRec(newSk.left)) || RB.isRed(TreeModelRec(newSk.left.left));
      assert elems(newSk.left) !! elems(newSk.right);
      assert newNode !in elems(newSk.right);
      assert newNode !in elems(newSk.left);
      assert allocated(elems(newSk)) by {
        AllocatedAll(elems(newSk));
      }
      newNodeLeft, newSkLeft, removedNode := RemoveMinRec(newNode.left, newSk.left);
      assert elems(newSk.left) !! elems(newSk.right);
      assert newNode !in elems(newSk.right);
      assert newNode !in elems(newSk.left);
      assert ValidRec(newNodeLeft, newSkLeft);
      newNode.left := newNodeLeft;
      newSk := Node(newSkLeft, newNode, newSk.right);
      assume false;
      assert ValidRec(newNode.left, newSk.left);
      assert allocated(elems(newSk)) by {
        AllocatedAll(elems(newSk));
      }
      assert elems(newSk) <= elems(sk);
      //assert ValidRec(newNode.left, newSk.left);
      assume ValidRec(newNode, newSk);
      newNode, newSk := Restore(newNode, newSk);
      assume false;
    }
  }
}
