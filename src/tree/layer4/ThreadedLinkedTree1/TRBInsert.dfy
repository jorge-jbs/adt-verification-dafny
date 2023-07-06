include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/TTree1.dfy"
include "../../../../src/tree/layer4/TTNode1.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module LinkedTree.TRBInsert {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = Tree
  import opened TTNode
  import opened Color

  // 14"
  method {:verify false} FlipColors(node: TTNode, ghost sk: ttree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Child?  /* redundant */
    requires TreeModelRec(sk).left.child.Node?  /* redundant */
    requires TreeModelRec(sk).right.Child?  /* redundant */
    requires TreeModelRec(sk).right.child.Node?  /* redundant */

    ensures ValidRec(node, sk)
    ensures TreeModelRec(sk) == TRBi.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }

  // 36"
  method {:verify false} RotateLeft(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).right.Child?  /* redundant */
    requires TreeModelRec(sk).right.child.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    //assert TreeModelRec(sk).right.Child?
    //assert TreeModelRec(sk).right.child.Node?
    newNode := node.right;
    node.right := newNode.left;
    node.isThreadRight := newNode.isThreadLeft;
    newNode.left := node;
    newNode.isThreadLeft := false;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(T.Child(T.Node(sk.left, node, sk.right.child.left)), newNode, sk.right.child.right);
  }

  // 52"
  method {:verify false} RotateRight(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadLeft
    modifies node`left
    modifies node.left`isThreadRight
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires !node.isThreadLeft
    requires TreeModelRec(sk).left.Child?  /* redundant */
    requires TreeModelRec(sk).left.child.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node.left;
    node.left := newNode.right;
    node.isThreadLeft := newNode.isThreadRight;
    newNode.right := node;
    newNode.isThreadRight := false;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(sk.left.child.left, newNode, T.Child(T.Node(sk.left.child.right, node, sk.right)));
  }

  // 4"
  method {:verify false} Restore(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
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
      if TRB.isRedP(t.right) then
        TRBi.RotateLeft(t)
      else
        t;
    ghost var t'' :=
      if TRB.isRedP(t'.left) && TRB.isRedP(t'.left.child.left) then
        TRBi.RotateRight(t')
      else
        t';
    ghost var t''' :=
      if TRB.isRedP(t''.left) && TRB.isRedP(t''.right) then
        TRBi.FlipColors(t'')
      else
        t'';
    newNode := node;
    newSk := sk;

    if newNode.right != null && !newNode.isThreadRight && newNode.right.color.Red? {
      newNode, newSk := RotateLeft(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t';

    isRedLeftProp(newNode, newSk);
    assert isRedLeft(newNode) <==> TRB.isRedP(t'.left);
    if newNode.left != null && !newNode.isThreadLeft {
      assert TreeModelRecP(newSk.left.child.left) == t'.left.child.left;
      isRedLeftProp(newNode.left, newSk.left.child);
      assert isRedLeft(newNode.left) <==> TRB.isRedP(t'.left.child.left);
    }
    if isRedLeft(newNode) && isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, newSk);
      assert TreeModelRec(newSk) == TRBi.RotateRight(t');
    }

    assert TreeModelRec(newSk) == t'';

    if isRedLeft(newNode) && isRedRight(newNode) {
      FlipColors(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t''';
  }

  function method nodeToPointer(node: TTNode?): TRB.threadOrEmpty
  {
    if node == null then
      TRB.Child(TRB.Empty)
    else
      TRB.Thread(node.key)
  }

  method TRBInsertRecP(prev: TTNode?, node: TTNode?, isThread: bool, next: TTNode?, ghost sk: ttreePointer<TTNode>, k: K, v: V)
    returns (newNode: TTNode, newIsThread: bool, ghost newSk: ttreePointer<TTNode>, ghost insertedNode:TTNode)

    decreases sk

    modifies set x | x in elemsP(sk) :: x`isThreadLeft
    modifies set x | x in elemsP(sk) :: x`left
    modifies set x | x in elemsP(sk) :: x`isThreadRight
    modifies set x | x in elemsP(sk) :: x`right
    modifies set x | x in elemsP(sk) :: x`value
    modifies set x | x in elemsP(sk) :: x`color

    requires ValidRecP(node, sk, isThread)
    ensures ValidRecP(newNode, newSk, newIsThread)
    ensures
      TreeModelRecP(newSk)
        == TRBi.TRBInsertP(
            nodeToPointer(prev),
            old(TreeModelRecP(sk)),
            nodeToPointer(next),
            k,
            v
          )

    ensures elemsP(newSk) == elemsP(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elemsP(sk))
    ensures fresh(elemsP(newSk)-elemsP(sk))
    ensures allocated(elemsP(newSk))
  {
    newIsThread := false;
    if !isThread {
      ghost var newChild;
      newNode, newChild, insertedNode := TRBInsertRec(prev, node, next, sk.child, k, v);
      newSk := T.Child(newChild);
    } else {
      ghost var newChildLeft :=
        if prev == null then
          T.Child(T.Empty)
        else
          T.Thread(prev as TTNode);
      ghost var newChildRight :=
        if next == null then
          T.Child(T.Empty)
        else
          T.Thread(next as TTNode);
      newNode := new TTNode(prev != null, prev, k, v, next != null, next, Red);
      newSk := T.Child(T.Node(newChildLeft, newNode, newChildRight));
      insertedNode := newNode;
      calc == {
        TreeModelRecP(newSk);
        TRB.Child(TRB.Node(TreeModelRecP(newChildLeft), newNode.key, newNode.value, TreeModelRecP(newChildRight), newNode.color));
        TRB.Child(TRB.Node(nodeToPointer(prev), k, v, nodeToPointer(next), Red));
        TRBi.TRBInsertP(
          nodeToPointer(prev),
          old(TreeModelRecP(sk)),
          nodeToPointer(next),
          k,
          v
        );
      }
    }
  }

  // 1'33"
  method {:verify false} TRBInsertRec(prev: TTNode?, node: TTNode?, next: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)
   
    decreases sk

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures
      TreeModelRec(newSk)
        == TRBi.TRBInsert(
            nodeToPointer(prev),
            old(TreeModelRec(sk)),
            nodeToPointer(next),
            k,
            v
          )

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      ghost var newChildLeft :=
        if prev != null then
          T.Thread(prev as TTNode)
        else
          T.Child(T.Empty);
      ghost var newChildRight :=
        if next != null then
          T.Thread(next as TTNode)
        else
          T.Child(T.Empty);
      newNode := new TTNode(prev != null, prev, k, v, next != null, next, Red);
      newSk := T.Node(newChildLeft, newNode, newChildRight);
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
        node.right, node.isThreadRight, newSkRight, insertedNode := TRBInsertRecP(node, node.right, node.isThreadRight, next, sk.right, k, v);
        newSk := T.Node(sk.left, node, newSkRight);
        newNode, newSk := Restore(newNode, newSk);
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, node.isThreadLeft, newSkLeft, insertedNode := TRBInsertRecP(prev, node.left, node.isThreadLeft, node, sk.left, k, v);
        newSk := T.Node(newSkLeft, node, sk.right);
        newNode, newSk := Restore(newNode, newSk);
      } else {
        assert false;
      }
    }
  }

/*
  // 5"
  method TRBInsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
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
