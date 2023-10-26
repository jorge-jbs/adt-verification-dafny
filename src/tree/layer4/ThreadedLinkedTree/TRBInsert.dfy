include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Restore.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.TRBInsert {
  import opened KeyValue
  import opened Res = Restore
  import TRB = TRBTree.Base
  import TRBr = TRBTree.Restore
  import TRBi = TRBTree.TRBInsert
  import opened T = TTree
  import opened TTNode
  import opened Color

  // 45"
  method TRBInsertRec(
      prev: TTNode?, 
      node: TTNode?, 
      isThread: bool,
      next: TTNode?, 
      ghost sk: ttreeOrThread<TTNode>, 
      k: K, 
      v: V
    )
    returns (
      newNode: TTNode, 
      ghost newSk: nettree<TTNode>, 
      insertedNode: TTNode,
      isInserted: bool
    )

    decreases sk

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidChild(node, sk, isThread)
    requires sk.Node? ==> ThreadedNe(nodeToThread(prev), sk, nodeToThread(next))
    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(nodeToThread(prev), newSk, nodeToThread(next))
    ensures
      TreeModelRec(newSk)
        == TRBi.TRBInsert(
            TreeModelRec(nodeToThread(prev)),
            old(TreeModelRec(sk)),
            TreeModelRec(nodeToThread(next)),
            k,
            v
          )

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    
    ensures isInserted <==> old(TRBi.IsInserted(TreeModelRec(sk), k))

/*
    ensures insertedNode == null ==>
      && elems(newSk) == elems(sk)
      && k in old(TRB.keys(TreeModelRec(sk)))
      && k in TRB.keys(TreeModelRec(newSk))
      && TRB.Get'(TreeModelRec(newSk), k) == v
*/

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null || isThread {
      ghost var newChildLeft :=
        if prev != null then
          T.Thread(prev as TTNode)
        else
          T.Empty;
      ghost var newChildRight :=
        if next != null then
          T.Thread(next as TTNode)
        else
          T.Empty;
      newNode := new TTNode(prev != null, prev, k, v, next != null, next, Red);
      newSk := T.Node(newChildLeft, newNode, newChildRight);
      insertedNode := newNode;
      isInserted := true;
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
        isInserted := false;
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, insertedNode, isInserted := TRBInsertRec(
          node, 
          node.right, 
          node.isThreadRight, 
          next, 
          sk.right, 
          k, 
          v
        );
        node.isThreadRight := false;
        newSk := T.Node(sk.left, node, newSkRight);
        newNode, newSk := Restore(newNode, nodeToThread(prev), newSk, nodeToThread(next));
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode, isInserted := TRBInsertRec(
          prev, 
          node.left, 
          node.isThreadLeft, 
          node, 
          sk.left, 
          k, 
          v
        );
        node.isThreadLeft := false;
        newSk := T.Node(newSkLeft, node, sk.right);
        newNode, newSk := Restore(newNode, nodeToThread(prev), newSk, nodeToThread(next));
      } else {
        assert false;
      }
    }
  }

  method TRBInsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (
      newNode: TTNode, 
      ghost newSk: ttree<TTNode>, 
      insertedNode: TTNode,
      isInserted: bool
    )

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    requires ThreadedRoot(sk)
    ensures ValidRec(newNode, newSk)
    ensures ThreadedRoot(newSk)
    ensures TreeModelRec(newSk) == TRBi.TRBInsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures isInserted <==> TRBi.IsInserted(old(TreeModelRec(sk)), k)

/*
    ensures insertedNode == null ==>
      && elems(newSk) == elems(sk)
      && k in old(TRB.keys(TreeModelRec(sk)))
      && k in TRB.keys(TreeModelRec(newSk))
      && TRB.Get'(TreeModelRec(newSk), k) == v
*/

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode, isInserted := TRBInsertRec(null, node, false, null, sk, k, v);
    newNode.color := Black;
  }
}
