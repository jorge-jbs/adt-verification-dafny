include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Restore.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.TRBInsert {
  import opened KeyValue
  import opened Res = Restore
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = TTree
  import opened TTNode
  import opened Color

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

  // 5"
  method TRBInsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.TRBInsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode := TRBInsertRec(null, node, null, sk, k, v);
    newNode.color := Black;
  }
}
