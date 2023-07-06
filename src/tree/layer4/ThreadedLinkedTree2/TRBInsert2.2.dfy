include "../../../../src/tree/layer4/TRBTree2/Base.dfy"
include "../../../../src/tree/layer4/TRBTree2/TRBInsert.dfy"
include "../../../../src/tree/layer4/Tree.dfy"
include "../../../../src/tree/layer4/TTNode2.2.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module LinkedTree.TRBInsert {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = Tree
  import opened TTNode
  import opened Color

  // 67"
  method FlipColors(node: TTNode, ghost sk: tree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk)
    ensures TreeModelRec(sk) == TRBi.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }

  // 22"
  method RotateLeft(node: TTNode, ghost sk: tree<TTNode>)
    returns (newNode: TTNode, ghost newSk: tree<TTNode>)

    modifies node`color
    modifies node`right
    modifies node`isThreadRight
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires node.right != null
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node.right;
    node.isThreadRight := newNode.isThreadLeft;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(T.Node(sk.left, node, sk.right.left), newNode, sk.right.right);
  }
/*

  // 10"
  method RotateRight(node: TTNode, ghost sk: tree<TTNode>)
    returns (newNode: TTNode, ghost newSk: tree<TTNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires TreeModelRec(sk).left.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateRight(old(TreeModelRec(sk)))
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
  method Restore(node: TTNode, ghost sk: tree<TTNode>)
    returns (newNode: TTNode, ghost newSk: tree<TTNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    ghost var t' :=
      if TRB.isRed(t.right) then
        TRBi.RotateLeft(t)
      else
        t;
    ghost var t'' :=
      if TRB.isRed(t'.left) && TRB.isRed(t'.left.left) then
        TRBi.RotateRight(t')
      else
        t';
    ghost var t''' :=
      if TRB.isRed(t''.left) && TRB.isRed(t''.right) then
        TRBi.FlipColors(t'')
      else
        t'';
    newNode := node;
    newSk := sk;

    if isRed(newNode.right) {
      newNode, newSk := RotateLeft(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t';

    isRedProp(newNode.left, newSk.left);
    assert isRed(newNode.left) <==> TRB.isRed(t'.left);
    if newNode.left != null {
      assert TreeModelRec(newSk.left.left) == t'.left.left;
      isRedProp(newNode.left.left, newSk.left.left);
      assert isRed(newNode.left.left) <==> TRB.isRed(t'.left.left);
    }
    if isRed(newNode.left) && isRed(newNode.left.left) {
      newNode, newSk := RotateRight(newNode, newSk);
      assert TreeModelRec(newSk) == TRBi.RotateRight(t');
    }

    assert TreeModelRec(newSk) == t'';

    if isRed(newNode.left) && isRed(newNode.right) {
      FlipColors(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t''';
  }

  // 4'41"
  method TRBInsertRec(node: TTNode?, ghost sk: tree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: tree<TTNode>, ghost insertedNode:TTNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.TRBInsert(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      newNode := new TTNode.RedBlack(null, k, v, null, Red);
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
        node.right, newSkRight, insertedNode := TRBInsertRec(node.right, sk.right, k, v);
        newSk := T.Node(sk.left, node, newSkRight);
        newNode, newSk := Restore(newNode, newSk);
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode := TRBInsertRec(node.left, sk.left, k, v);
        newSk := T.Node(newSkLeft, node, sk.right);
        newNode, newSk := Restore(newNode, newSk);
      } else {
        assert false;
      }
    }
  }

  // 5"
  method {:verify false} TRBInsertRoot(node: TTNode?, ghost sk: tree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: tree<TTNode>, ghost insertedNode:TTNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.TRBInsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode := TRBInsertRec(node, sk, k, v);
    newNode.color := Black;
  }
  */
}
