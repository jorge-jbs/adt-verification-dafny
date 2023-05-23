include "../../../../src/tree/layer4/RBTree/SInsert.dfy"
include "../../../../src/tree/layer4/Tree.dfy"
include "../../../../src/tree/layer4/TNode.dfy"
include "../../../../src/tree/layer4/KeyValue.dfy"

module LinkedTree.Find {
  import opened RB = RBTree.Base
  import opened T = Tree
  import opened TNode
  import opened KeyValue

  method FindRec(node: TNode?, ghost sk: tree<TNode>, k: K)
      returns (foundNode: TNode?)
    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)

    ensures foundNode != null <==> k in keys(TreeModelRec(sk))
    ensures foundNode != null ==> foundNode.key == k
    ensures foundNode != null ==> foundNode.value == RB.Get(TreeModelRec(sk), k)

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    if node == null {
      return null;
    } else {
      if k == node.key {
        return node;
      } else if node.key < k {
        foundNode := FindRec(node.right, sk.right, k);
      } else if k < node.key {
        foundNode := FindRec(node.left, sk.left, k);
      } else {
        assert false;
      }
    }
  }
}
