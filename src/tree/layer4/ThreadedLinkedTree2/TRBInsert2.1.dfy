include "../../../../src/tree/layer4/TRBTree2/Base.dfy"
include "../../../../src/tree/layer4/TRBTree2/TRBInsert.dfy"
include "../../../../src/tree/layer4/TTree2.dfy"
include "../../../../src/tree/layer4/TTNode2.1.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module LinkedTree.TRBInsert {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = Tree
  import opened TTNode
  import opened Color

  // 67"
  method FlipColors(node: TTNode, ghost sk: ttree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk, false)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk, false)
    ensures TreeModelRec(sk) == TRBi.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    assert TreeModelRec(sk).Node?;
    assert TreeModelRec(sk).left.Node?;
    assert TreeModelRec(sk).right.Node?;

    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);

    assert !node.isThreadLeft;
    assert !node.isThreadRight;
    assert sk.Node?;
    assert unchanged(set x | x in elems(sk) :: x`left);
    assert unchanged(set x | x in elems(sk) :: x`isThreadLeft);
    assert unchanged(set x | x in elems(sk) :: x`right);
    assert unchanged(set x | x in elems(sk) :: x`isThreadRight);
    assert ValidRec(node, sk, false);
    assert ValidRec(node.left, sk.left, false);
    assert ValidRec(node.left.left, sk.left.left, node.left.isThreadLeft);
    assert old(TreeModelRec(sk)).Node?;
    assert TreeModelRec(sk).Node?;
    assert TreeModelRec(sk).key == old(TreeModelRec(sk)).key;
    assert TreeModelRec(sk).value == old(TreeModelRec(sk)).value;
    assert TreeModelRec(sk).color == NegColor(old(TreeModelRec(sk)).color);
    assert old(TreeModelRec(sk)).left.Node?;
    assert TreeModelRec(sk).left.Node?;
    assert TreeModelRec(sk).left.key == old(TreeModelRec(sk)).left.key;
    assert TreeModelRec(sk).left.value == old(TreeModelRec(sk)).left.value;
    assert node.left.left == old(node.left.left);
    assert ValidRec(node.left.left, sk.left.left, node.left.isThreadLeft);
    assert unchanged(elems(sk.left.left));
    //assert unchanged(elemsAndThreads(sk.left.left));
    assume false;
    assert unchanged(set x | x in elemsAndThreads(sk) :: x`key);
    assume false;
    assert unchanged(set x | x in subtrees(sk) && x.Thread? :: x.thread`key);
    assert unchanged(set x | x in subtrees(sk) && x.Node? :: x.data`left);
    assert unchanged(set x | x in subtrees(sk) && x.Node? :: x.data`key);
    assert unchanged(set x | x in subtrees(sk) && x.Node? :: x.data`value);
    assert unchanged(set x | x in subtrees(sk) && x.Node? :: x.data`color);
    assume false;
    assert TreeModelRec(sk.left.left) == old(TreeModelRec(sk.left.left));
    assume false;
    //assert TreeModelRec(sk.left).left == old(TreeModelRec(sk).left).left;
    assert TreeModelRec(sk).left.left == old(TreeModelRec(sk)).left.left;
    assume false;
    assert TreeModelRec(sk).left.right == old(TreeModelRec(sk)).left.right;
    assert TreeModelRec(sk).left.color == NegColor(old(TreeModelRec(sk)).left.color);
    assert old(TreeModelRec(sk)).right.Node?;
    assert TreeModelRec(sk).right.Node?;
    assert TreeModelRec(sk).right.key == old(TreeModelRec(sk)).right.key;
    assert TreeModelRec(sk).right.value == old(TreeModelRec(sk)).right.value;
    assert TreeModelRec(sk).right.left == old(TreeModelRec(sk)).right.left;
    assert TreeModelRec(sk).right.right == old(TreeModelRec(sk)).right.right;
    assert TreeModelRec(sk).right.color == NegColor(old(TreeModelRec(sk)).right.color);
    assert TreeModelRec(sk) == TRBi.FlipColors(old(TreeModelRec(sk)));
  }

/*
  // 22"
  method RotateLeft(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`right
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
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(T.Node(sk.left, node, sk.right.left), newNode, sk.right.right);
  }

  // 10"
  method RotateRight(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

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
  method Restore(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

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
  method TRBInsertRec(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)

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
  method {:verify false} TRBInsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)

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
