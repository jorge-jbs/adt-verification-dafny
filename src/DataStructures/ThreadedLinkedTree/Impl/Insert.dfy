include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Restore.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Insert.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Restore.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.Insert {
  import opened KeyValue
  import opened Res = Restore
  import opened Model.Color
  import Model = Model.Insert
  import opened T = TTree
  import opened TTNode

  // 45"
  method InsertRec(
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
        == Model.Insert(
            TreeModelRec(nodeToThread(prev)),
            old(TreeModelRec(sk)),
            TreeModelRec(nodeToThread(next)),
            k,
            v
          )

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    ensures isInserted <==> old(Model.IsInserted(TreeModelRec(sk), k))

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
        node.right, newSkRight, insertedNode, isInserted := InsertRec(
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
        node.left, newSkLeft, insertedNode, isInserted := InsertRec(
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

  method InsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
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
    ensures TreeModelRec(newSk) == Model.InsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures isInserted <==> Model.IsInserted(old(TreeModelRec(sk)), k)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode, isInserted := InsertRec(null, node, false, null, sk, k, v);
    newNode.color := Black;
  }
}
