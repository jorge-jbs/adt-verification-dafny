include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"
include "../../../../src/tree/alt-layer4/Tree.dfy"
include "../../../../src/tree/alt-layer4/TNode.dfy"
include "../../../../src/tree/alt-layer4/Color.dfy"

module LinkedTree.RBInsert {
  import opened KeyValue
  import RB = RBTree.Base
  import RBi = RBTree.RBInsert
  import opened T = Tree
  import opened TNode
  import opened Color

  // 67"
  method FlipColors(node: TNode, ghost sk: tree<TNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires node.right != null
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk)
    ensures TreeModelRec(sk) == RBi.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }

  // 22"
  method RotateLeft(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`right
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires node.right != null
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBi.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(T.Node(sk.left, node, sk.right.left), newNode, sk.right.right);
  }

  // 10"
  method RotateRight(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires TreeModelRec(sk).left.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBi.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node.left;
    node.left := newNode.right;
    newNode.right := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(sk.left.left, newNode, T.Node(sk.left.right, node, sk.right));
  }

  // 4"
  method Restore(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBi.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    ghost var t' :=
      if RB.isRed(t.right) then
        RBi.RotateLeft(t)
      else
        t;
    ghost var t'' :=
      if RB.isRed(t'.left) && RB.isRed(t'.left.left) then
        RBi.RotateRight(t')
      else
        t';
    ghost var t''' :=
      if RB.isRed(t''.left) && RB.isRed(t''.right) then
        RBi.FlipColors(t'')
      else
        t'';
    newNode := node;
    newSk := sk;

    if isRed(newNode.right) {
      newNode, newSk := RotateLeft(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t';

    isRedProp(newNode.left, newSk.left);
    assert isRed(newNode.left) <==> RB.isRed(t'.left);
    if newNode.left != null {
      assert TreeModelRec(newSk.left.left) == t'.left.left;
      isRedProp(newNode.left.left, newSk.left.left);
      assert isRed(newNode.left.left) <==> RB.isRed(t'.left.left);
    }
    if isRed(newNode.left) && isRed(newNode.left.left) {
      newNode, newSk := RotateRight(newNode, newSk);
      assert TreeModelRec(newSk) == RBi.RotateRight(t');
    }

    assert TreeModelRec(newSk) == t'';

    if isRed(newNode.left) && isRed(newNode.right) {
      FlipColors(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t''';
  }

  // 4'41"
  method RBInsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
    returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBi.RBInsert(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      newNode := new TNode.RedBlack(null, k, v, null, Red);
      newSk := T.Node(T.Empty, newNode, T.Empty);
      insertedNode := newNode;
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, insertedNode := RBInsertRec(node.right, sk.right, k, v);
        newSk := T.Node(sk.left, node, newSkRight);
        newNode, newSk := Restore(newNode, newSk);
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode := RBInsertRec(node.left, sk.left, k, v);
        newSk := T.Node(newSkLeft, node, sk.right);
        newNode, newSk := Restore(newNode, newSk);
      } else {
        assert false;
      }
    }
  }

  // 5"
  method RBInsertRoot(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
    returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBi.RBInsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode := RBInsertRec(node, sk, k, v);
    newNode.color := Black;
  }
}
