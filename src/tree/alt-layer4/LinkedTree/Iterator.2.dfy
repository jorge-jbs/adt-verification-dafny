include "../../../../src/MUtils.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Iterator.2.dfy"
include "../../../../src/tree/alt-layer4/Tree.dfy"
include "../../../../src/tree/alt-layer4/TNode.dfy"

module LinkedTree.Iterator {
  import opened Utils
  import opened KeyValue
  import RB = RBTree.Base
  import RBit = RBTree.Iterator
  import opened T = Tree
  import opened TNode

  class Iterator {
    var stack: seq<TNode>;
    ghost var stackSk: seq<tree<TNode>>;
    ghost var root: TNode?;
    ghost var skeleton: tree<TNode>;
    ghost var traversed: seq<(K, V)>;

    function RBStack(): seq<RB.rbtree>
      reads this, BigUnion(set sk | sk in stackSk :: elems(sk))
    {
      seq(|stackSk|, i reads this, BigUnion(set sk | sk in stackSk :: elems(sk)) requires 0 <= i < |stackSk| => TreeModelRec(stackSk[i]))
    }

    predicate Valid()
      reads this, elems(skeleton), BigUnion(set sk | sk in stackSk :: elems(sk))
    {
      && RBit.ValidStack(RBStack())
      && RB.inorder(TreeModelRec(skeleton)) == traversed + RBit.inorderStack(RBStack())
    }


    constructor(node: TNode, ghost sk: tree<TNode>, ghost root: TNode?, ghost skeleton: tree<TNode>)
    {
      this.stack := [node];
      this.stackSk := [sk];
      this.root := root;
      this.skeleton := skeleton;
      this.traversed := [];
    }
    
    method DescendAndPush(node: TNode?, ghost sk: tree<TNode>)
      modifies this
      requires ValidRec(node, sk)
      requires Valid()
    {
      var node := node;
      ghost var sk := sk;
      while node != null
        decreases sk
        invariant ValidRec(node, sk)
        invariant RBit.ValidStack(RBStack())
        //invariant RB.inorder(TreeModelRec(skeleton)) == traversed + RBit.inorderStack(RBStack())
      {
        var st := RBStack();
        assert RBit.ValidStack(st);
        assert forall k | 0 <= k < |st| :: st[k].Node?;
        stack := stack + [node];
        st := RBStack();
        assert node != null;
        assert sk.Node?;
        assert TreeModelRec(sk).Node?;
        assume false;
        assert forall k | 0 <= k < |st|-1 :: st[k].Node?;
        assert RBit.ValidStack(RBStack());
        node := node.left;
        sk := sk.left;
        assume false;
      }
    }

  }
}
