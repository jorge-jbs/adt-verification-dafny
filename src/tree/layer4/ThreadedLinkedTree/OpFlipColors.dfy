include "../../../../src/tree/layer4/ThreadedLinkedTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.OpFlipColors {
  import opened KeyValue
  import TRBf = TRBTree.FlipColors
  import opened FC = FlipColors
  import opened T = TTree
  import opened TTNode
  import opened Color

/*
  method FlipColors(node: TTNode, ghost sk: ttree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires OpValidRec(node, sk)
    requires TRBf.FlipColors.requires(TreeModelRec(sk))
    requires reveal OpValidRec(); true

    ensures OpValidRec(node, sk)
    ensures TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    assert
      && node.left != null
      && !node.isThreadLeft
      && node.right != null
      && !node.isThreadRight
      && TreeModelRec(sk).left.Child?
      && TreeModelRec(sk).left.child.Node?
      && TreeModelRec(sk).right.Child?
      && TreeModelRec(sk).right.child.Node?
    by {
      reveal OpValidRec();
      reveal OpValidRecP();
    }
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
    assert
      && OpValidRec(node, sk)
      //&& OpValidRecP(node.left, sk.left, false)
      //&& OpValidRecP(node.right, sk.right, false)
    by {
      reveal OpValidRec();
      reveal OpValidRecP();
    }
    assert {:only} TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk))) by {
      assert sk.Node?;
      calc == {
        TreeModelRec(sk);
        RB.Node(
          TreeModelRecP(sk.left), 
          sk.data.key, 
          sk.data.value, 
          TreeModelRecP(sk.right), 
          sk.data.color
        );
        RB.Node(
          RB.Child(RB.Node(
            TreeModelRecP(sk.left.child.left), 
            sk.left.child.data.key, 
            sk.left.child.data.value, 
            TreeModelRecP(sk.left.child.right), 
            sk.left.child.data.color
          )),
          sk.data.key, 
          sk.data.value, 
          RB.Child(RB.Node(
            TreeModelRecP(sk.right.child.left), 
            sk.right.child.data.key, 
            sk.right.child.data.value, 
            TreeModelRecP(sk.right.child.right), 
            sk.right.child.data.color
          )),
          sk.data.color
        );
        {
          assume sk.data == node;
          assume sk.left.child.data == node.left;
        }
        RB.Node(
          RB.Child(RB.Node(
            TreeModelRecP(sk.left.child.left), 
            sk.left.child.data.key, 
            sk.left.child.data.value, 
            TreeModelRecP(sk.left.child.right), 
            sk.left.child.data.color
            //NegColor(old(sk.left.child.data.color))
          )),
          sk.data.key, 
          sk.data.value, 
          RB.Child(RB.Node(
            TreeModelRecP(sk.right.child.left), 
            sk.right.child.data.key, 
            sk.right.child.data.value, 
            TreeModelRecP(sk.right.child.right), 
            sk.right.child.data.color
          )),
          NegColor(old(sk.data.color))
        );
        { assume false; }
        TRBf.FlipColors(old(TreeModelRec(sk)));
      }
    }
  }
  */

  method OpFlipColors(node: TTNode, ghost sk: ttree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires OpValidRec(node, sk)
    requires reveal OpValidRec(); true
    requires TRBf.FlipColors.requires(TreeModelRec(sk))

    ensures OpValidRec(node, sk)
    ensures TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    OpValidEq(node, sk);
    FC.FlipColors(node, sk);
  }
    /*
  {
    reveal OpValidRec();
    reveal OpValidRecP();
    assert
      && node.left != null
      && !node.isThreadLeft
      && node.right != null
      && !node.isThreadRight
      && TreeModelRec(sk).left.Child?
      && TreeModelRec(sk).left.child.Node?
      && TreeModelRec(sk).right.Child?
      && TreeModelRec(sk).right.child.Node?
    by {
      reveal FPpre;
    }
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }
  */
}
