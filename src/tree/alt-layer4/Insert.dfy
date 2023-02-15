include "../../../src/tree/alt-layer4/RBTreeData.dfy"
include "../../../src/tree/alt-layer4/TreeData.dfy"
include "../../../src/tree/alt-layer4/TNode.dfy"
include "../../../src/tree/alt-layer4/KeyValue.dfy"

module Insert {
  import opened RB = RBTreeData
  import opened T = TreeData
  import opened TNode
  import opened KeyValue

  method InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
      returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode: TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures ValidRec(newNode, newSk)
    ensures SearchTreeRec(newSk)
    ensures TreeModelRec(newSk) == SInsert(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk)+{insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures allocated(elems(newSk))
  {
    if node == null {
      newNode := new TNode(null, k, v, null);
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
        node.right, newSkRight, insertedNode := InsertRec(node.right, sk.right, k, v);
        newSk := T.Node(sk.left, node, newSkRight);
        /*
        assert TreeModelRec(newSkRight) == SInsert(old(TreeModelRec(sk.right)), k, v);
        assert TreeModelRec(sk.left) == old(TreeModelRec(sk.left));
        calc == {
          TreeModelRec(newSk);
          RB.Node(TreeModelRec(sk.left), node.key, node.value, TreeModelRec(newSkRight), node.color);
          RB.Node(TreeModelRec(sk.left), node.key, node.value, SInsert(old(TreeModelRec(sk.right)), k, v), node.color);
          SInsert(RB.Node(TreeModelRec(sk.left), node.key, node.value, old(TreeModelRec(sk.right)), node.color), k, v);
          SInsert(old(TreeModelRec(sk)), k, v);
        }
        assert TreeModelRec(newSk) == SInsert(old(TreeModelRec(sk)), k, v);
        */
        //assume false;
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, newSkLeft, insertedNode := InsertRec(node.left, sk.left, k, v);
        newSk := T.Node(newSkLeft, node, sk.right);
        //assume false;
      } else {
        assert false;
      }
    }
  }
}
