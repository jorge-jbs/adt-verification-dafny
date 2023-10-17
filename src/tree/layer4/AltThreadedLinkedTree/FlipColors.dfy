include "../../../../src/tree/layer4/AltTRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/AltTTree.dfy"
include "../../../../src/tree/layer4/AltTTNode2.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.FlipColors {
  import opened KeyValue
  import TRBf = TRBTree.FlipColors
  import opened T = TTree
  import opened TTNode
  import opened Color

/*
  method FlipColors(node: TTNode, ghost sk: ttree<TTNode>, ghost parents: set<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk, parents)
    /*
    requires assert ValidRec(node.left, sk.left, parents + {node}); true
    requires TRBf.FlipColors.requires(TreeModelRec(sk))
    requires assert sk.Node?; true
    requires assert TreeModelRec(sk).Node?; true
    requires assert sk.left.Node?; true
    requires assert TreeModelRec(sk).left.Node? ==> TreeModelRec(sk.left).Node? && sk.left.Node? && node.left != null; true
    */
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk, parents)
    ensures TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }
  */

  method FlipColors(
      node: TTNode,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
      //ghost parents: set<TTNode>
    )
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    //requires ThreadsInParentsRec(sk, parents)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk)
    //ensures ThreadsInParentsRec(sk, parents)
    ensures ThreadedNe(prev, sk, next)
    ensures TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }
}
