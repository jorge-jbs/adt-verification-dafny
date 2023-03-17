include "../../../../src/MUtils.dfy"
include "../../../../src/tree/alt-layer4/LinkedTree/RBInsert.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"
include "../../../../src/tree/alt-layer4/RBTree/RBRemove.dfy"
include "../../../../src/tree/alt-layer4/Tree.dfy"
include "../../../../src/tree/alt-layer4/TNode.dfy"
include "../../../../src/tree/alt-layer4/Color.dfy"

module LinkedTree.RBRemove {
  import opened Utils
  import opened KeyValue
  import RB = RBTree.Base
  import RBi = RBTree.RBInsert
  import RBr = RBTree.RBRemove
  import opened T = Tree
  import opened TNode
  import opened Color
  import opened RBInsert
  
  method {:verify false} MoveRedLeft(node: TNode, ghost sk: tree<TNode>)  // 2'30"
      returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right
    //modifies elems(sk)

    requires ValidRec(node, sk)
    requires RBr.MoveRedLeft.requires(TreeModelRec(sk))
    /*
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.left.left)

    requires TreeModelRec(sk).left.Node?;  /* redundant */
    requires TreeModelRec(sk).right.Node?;  /* redundant */
    */

    ensures ValidRec(newNode, newSk)

    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == RBr.MoveRedLeft(old(TreeModelRec(sk)))
    //ensures size(newSk) == size(sk)
    //ensures size(newSk.left) < size(sk)

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    ghost var t := TreeModelRec(sk);
    FlipColors(node, sk);
    ghost var t' := RBi.FlipColors(t);
    newNode := node;
    newSk := sk;
    assert TreeModelRec(newSk) == t';
    isRedProp(newNode.right.left, newSk.right.left);
    if isRed(newNode.right.left) {
      assert newNode.right.left != null && newNode.right.left.color.Red?;
      //assert size(newSk.left) < size(sk);
      ghost var newSkRight;
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right, newSk.right);
      assert ValidRec(newNode.right.left, newSk.right.left);
      assert elems(newSk.left) !! elems(newSk.right);
      label PreRR:
      newNode.right, newSkRight := RotateRight(newNode.right, newSk.right);
      newSk := Node(newSk.left, newNode, newSkRight);
      //assert size(newSk.left) < size(sk);
      assert unchanged@PreRR(elems(newSk.left));
      assert ValidRec(newNode.right, newSk.right);
      assert ValidRec(newNode.left, newSk.left);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right.right, newSk.right.right);
      assert newNode.right.right != null;
      assert TreeModelRec(newSk).right.right.Node?;
      var t'' := RB.Node(
        t'.left,
        t'.key,
        t'.value,
        RBi.RotateRight(t'.right),
        t'.color
      );
      assert TreeModelRec(newSk) == t'';
      label PreRL:
      newNode, newSk := RotateLeft(newNode, newSk);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right, newSk.right);
      assert newNode.left != null;
      assert TreeModelRec(newSk).right.Node?;
      assert newNode.right != null;
      //assume size(newSk.left) < size(sk);
      assert TreeModelRec(newSk) == RBi.RotateLeft(t'');
      label PreFlip:
      FlipColors(newNode, newSk);
      //assert size(newSk.left) < size(sk);
      assert TreeModelRec(newSk) == RBi.FlipColors(RBi.RotateLeft(t''));
    } else {
    }
  }

  method {:verify false} MoveRedRight(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires SearchTreeRec(sk)
    requires RedBlackTreeRec(sk)
    requires isRed(node)
    requires isBlack(node.left)
    requires isBlack(node.right)
    requires !isRed(node.right.left)

    requires TreeModelRec(sk).left.Node?;  /* redundant */
    requires TreeModelRec(sk).right.Node?;  /* redundant */

    ensures ValidRec(newNode, newSk)

    ensures TreeModelRec(newSk) == RBr.MoveRedRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)
    //ensures size(newSk) == size(sk)
    //ensures size(newSk.right) < size(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    FlipColors(node, sk);
    newNode := node;
    newSk := sk;
    isRedProp(newNode.left.left, newSk.left.left);
    if isRed(newNode.left.left) {
      assert newNode.left.left != null && newNode.left.left.color.Red?;
      newNode, newSk := RotateRight(newNode, newSk);
      FlipColors(newNode, newSk);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.left, newSk.left);
      assert elems(newSk.left) !! elems(newSk.right);
      ghost var newSkRight;
      label PreRL:
      newNode.right, newSkRight := RotateLeft(newNode.right, newSk.right);
      assert unchanged@PreRL(elems(newSk.left));
      assert unchanged@PreRL(newNode.left);
      assert old@PreRL(ValidRec(newNode.left, newSk.left));
      assume false;
      assert ValidRec(newNode.left, newSk.left);
      newSk := Node(newSk.left, newNode, newSkRight);
      assert ValidRec(newNode, newSk);
      assume false;
    } else {
    }
  }

  lemma Allocated(x: object)
    ensures allocated(x)
  {}

  lemma AllocatedAll(xs: set<object>)
    ensures allocated(xs)
  {}

  lemma SetDiffComm<K>(r: set<K>, k: K, s: set<K>)
    requires k !in s
    ensures r - {k} + s == r + s - {k}
  {}

  lemma CongUnion<K>(r: set<K>, r': set<K>, s: set<K>)
    requires r == r'
    ensures r + s == r' + s
  {}

  method {:verify false} RemoveMinRec(node: TNode, ghost sk: tree<TNode>)  // 11'15"
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    decreases RB.size(TreeModelRec(sk))
    modifies elems(sk)
    //modifies set n | n in elems(sk) :: n`color
    //modifies set n | n in elems(sk) :: n`left
    //modifies set n | n in elems(sk) :: n`right

    requires ValidRec(node, sk)
    requires RBr.RemoveMin.requires(TreeModelRec(sk))

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBr.RemoveMin(old(TreeModelRec(sk))).0
    ensures removedNode.key == RBr.RemoveMin(old(TreeModelRec(sk))).1
    ensures removedNode.value == RBr.RemoveMin(old(TreeModelRec(sk))).2
    ensures removedNode in elems(sk)
    ensures removedNode !in elems(newSk)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures elems(newSk) <= elems(sk)

    //ensures RBi.Restore.requires(TreeModelRec(newSk))

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
    ensures allocated(removedNode)
  {
    ghost var t := TreeModelRec(sk);
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
    } else {
      ghost var t' :=
        if RB.isBlack(t.left) && !RB.isRed(t.left.left) then
          RBr.MoveRedLeftSpec(t);
          RBr.MoveRedLeft(t)
        else
          t;
      ghost var (l', minK, minV) := RBr.RemoveMin(t'.left);
      ghost var t'' := RB.Node(
          l',
          t'.key,
          t'.value,
          t'.right,
          t'.color
        );
      ghost var t''' := RBi.Restore(t'');
      newNode := node;
      newSk := sk;
      assert TreeModelRec(newSk) == t;
      isRedProp(newNode.left.left, newSk.left.left);
      if isBlack(newNode.left) && !isRed(newNode.left.left) {
        RBr.MoveRedLeftSpec(TreeModelRec(newSk));
        newNode, newSk := MoveRedLeft(newNode, newSk);
        isRedProp(newNode.left, newSk.left);
        isRedProp(newNode.left.left, newSk.left.left);
        assert isRed(newNode.left) || isRed(newNode.left.left);
        assert !(isRed(newNode.left) && isRed(newNode.left.left));
      }
      assert TreeModelRec(newSk) == t';
      assert TreeModelRec(newSk.left) == t'.left;
      assert TreeModelRec(newSk.right) == t'.right;
      assert newNode.key == TreeModelRec(newSk).key == t'.key;
      assert newNode.value == TreeModelRec(newSk).value == t'.value;
      var newNodeLeft;
      ghost var newSkLeft;
      ghost var preRecNewSk := newSk;
      assert elems(newSk) == elems(sk);
      assert ValidRec(newNode, newSk);
      assert ValidRec(newNode.right, newSk.right);
      assert newNode !in elems(newSk.right);
      assert newNode.left !in elems(newSk.right);
      assert newNode !in elems(newSk.left);
      assert newNode.right !in elems(newSk.left);
      assert elems(newSk.left) !! elems(newSk.right);
      assert allocated(elems(newSk));
      RBr.RemoveMinSpec(TreeModelRec(newSk.left));
      label PreRec:
      newNodeLeft, newSkLeft, removedNode := RemoveMinRec(newNode.left, newSk.left);
      assert TreeModelRec(newSkLeft) == l';
      assert unchanged@PreRec(elems(newSk.right));
      assert ValidRec(newNode.right, newSk.right);
      assert TreeModelRec(newSk.right) == t'.right;
      assert newNode.key == TreeModelRec(newSk).key == t'.key;
      assert newNode.value == TreeModelRec(newSk).value == t'.value;
      assert newNode.color == TreeModelRec(newSk).color == t'.color;
      assert elems(newSkLeft) == elems(newSk.left) - {removedNode};

      assert elems(newSk.left) !! elems(newSk.right);
      assert newNode !in elems(newSk.right);
      assert newNode !in elems(newSk.left);
      assert ValidRec(newNodeLeft, newSkLeft);
      newNode.left := newNodeLeft;
      newSk := Node(newSkLeft, newNode, newSk.right);
      calc == {
        elems(newSk);
        elems(newSk.left) + {newNode} + elems(newSk.right);
        elems(newSkLeft) + {newNode} + elems(newSk.right);
        elems(preRecNewSk.left) - {removedNode} + {newNode} + elems(newSk.right);
        (elems(preRecNewSk.left) - {removedNode} + {newNode}) + elems(newSk.right);
        {
          assert removedNode != newNode;
          SetDiffComm(elems(preRecNewSk.left), removedNode, {newNode});
          assert elems(preRecNewSk.left) - {removedNode} + {newNode}
            == elems(preRecNewSk.left) + {newNode} - {removedNode};
          CongUnion(elems(preRecNewSk.left) - {removedNode} + {newNode}, elems(preRecNewSk.left) + {newNode} - {removedNode}, elems(newSk.right));
        }
        (elems(preRecNewSk.left) + {newNode} - {removedNode}) + elems(newSk.right);
        {
          assert removedNode !in elems(newSk.right);
          SetDiffComm(elems(preRecNewSk.left) + {newNode}, removedNode, elems(newSk.right));
        }
        (elems(preRecNewSk.left) + {newNode} + elems(newSk.right)) - {removedNode};
        elems(preRecNewSk) - {removedNode};
        elems(sk) - {removedNode};
      }
      assert removedNode.key == minK == RBr.RemoveMin(old(TreeModelRec(sk))).1;
      assert removedNode.value == minV == RBr.RemoveMin(old(TreeModelRec(sk))).2;
      assert unchanged@PreRec(elems(newSk.right));
      assert ValidRec(newNode.right, newSk.right);
      assert ValidRec(newNode, newSk);
      assert elems(newSk) <= elems(sk);
      assert TreeModelRec(newSk).left == l' == t''.left;
      assert newNode.key == TreeModelRec(newSk).key == t'.key == t''.key;
      assert newNode.value == TreeModelRec(newSk).value == t'.value == t''.value;
      assert newNode.color == TreeModelRec(newSk).color == t'.color == t''.color;
      assert TreeModelRec(newSk).right == t'.right == t''.right;
      assert TreeModelRec(newSk) == t'';
      //RBi.RestoreSpec(TreeModelRec(newSk.left));
      newNode, newSk := Restore(newNode, newSk);
      assert TreeModelRec(newSk) == t''';
      assert elems(newSk) == elems(sk) - {removedNode};
      assert removedNode.key == minK == RBr.RemoveMin(old(TreeModelRec(sk))).1;
      assert removedNode.value == minV == RBr.RemoveMin(old(TreeModelRec(sk))).2;
    }
  }
  
  method {:verify true} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode?)
    decreases RB.size(TreeModelRec(sk))
    modifies elems(sk)

    requires ValidRec(node, sk)
    requires RBr.Remove.requires(TreeModelRec(sk), k)

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == RBr.Remove(old(TreeModelRec(sk)), k)
    ensures elems(newSk) <= elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
    } else {
      newNode := node;
      newSk := sk;
      ghost var t := TreeModelRec(newSk);
      if node.key > k {  // 16'~
        assume false;
        var t' :=
          if RB.isBlack(t.left) && !RB.isRed(t.left.left) then
            RBr.MoveRedLeftSpec(t);
            RBr.MoveRedLeft(t)
          else
            t;
        ghost var t'' :=
          RB.Node(
            RBr.Remove(t'.left, k),
            t'.key,
            t'.value,
            t'.right,
            t'.color
          );

        isBlackProp(newNode.left, newSk.left);
        if isBlack(newNode.left) {
          isRedProp(newNode.left.left, newSk.left.left);
        }
        if isBlack(newNode.left) && !isRed(newNode.left.left) {
          RBr.MoveRedLeftSpec(TreeModelRec(newSk));
          newNode, newSk := MoveRedLeft(newNode, newSk);
        }
        assert TreeModelRec(newSk) == t';

        var newNodeLeft;
        ghost var newSkLeft;
        label PreRec:
        assert elems(newSk) <= elems(sk);
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.left, newSk.left);
        assert ValidRec(newNode.right, newSk.right);
        assert newNode !in elems(newSk.right);
        assert newNode.left !in elems(newSk.right);
        assert newNode !in elems(newSk.left);
        assert newNode.right !in elems(newSk.left);
        assert elems(newSk.left) !! elems(newSk.right);
        assert allocated(elems(newSk));
        assert RBr.Remove.requires(TreeModelRec(newSk.left), k);

        RBr.RemoveSpec(TreeModelRec(newSk.left), k);
        newNodeLeft, newSkLeft, removedNode := RemoveRec(newNode.left, newSk.left, k);

        assert elems(newSk) <= elems(sk);
        assert unchanged@PreRec(elems(newSk.right));
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNodeLeft, newSkLeft);

        newNode.left := newNodeLeft;
        newSk := Node(newSkLeft, newNode, newSk.right);

        assert elems(newSk) <= elems(sk);
        assert allocated(elems(newSk));
        assert unchanged@PreRec(elems(newSk.right));
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode, newSk);

        assert TreeModelRec(newSk) == t'';

        newNode, newSk := Restore(newNode, newSk);
        assert ValidRec(newNode, newSk);
        assert elems(newSk) <= elems(sk);
        assert TreeModelRec(newSk) == RBi.Restore(t'') == RBr.Remove(old(TreeModelRec(sk)), k);
      } else {
        var t' :=
          if RB.isRed(t.left) then
            RBi.RotateRightSpec(t);
            RBi.RotateRight(t)
          else
            t;

        if isRed(newNode.left) {
          RBi.RotateRightSpec(TreeModelRec(newSk));
          newNode, newSk := RotateRight(newNode, newSk);
        }

        assert TreeModelRec(newSk) == t';

        if k == newNode.key && newNode.right == null {
          removedNode := newNode;
          newNode := newNode.left;
          newSk := newSk.left;
          assert elems(newSk) == elems(sk) - {removedNode};
          return;
        }

        isBlackProp(newNode.right, newSk.right);
        if isBlack(newNode.right) {
          isRedProp(newNode.right.left, newSk.right.left);
        }
        if isBlack(newNode.right) && !isRed(newNode.right.left) {
          RBr.MoveRedRightSpec(TreeModelRec(newSk));
          newNode, newSk := MoveRedRight(newNode, newSk);
        }

        var t'' :=
          if RB.isBlack(t'.right) && !RB.isRed(t'.right.left) then
            RBr.MoveRedRightSpec(t');
            RBr.MoveRedRight(t')
          else
            t';

        assert TreeModelRec(newSk) == t'';

        if k != newNode.key {
          assume false;
          ghost var t''' :=
            RB.Node(
              t''.left,
              t''.key,
              t''.value,
              RBr.Remove(t''.right, k),
              t''.color
            );

          label PreRec:
          assert elems(newSk) <= elems(sk);
          assert ValidRec(newNode, newSk);
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode.right, newSk.right);
          assert newNode !in elems(newSk.right);
          assert newNode.left !in elems(newSk.right);
          assert newNode !in elems(newSk.right);
          assert newNode.right !in elems(newSk.left);
          assert elems(newSk.left) !! elems(newSk.right);
          assert allocated(elems(newSk));
          assert RBr.Remove.requires(TreeModelRec(newSk.right), k);

          var newNodeRight;
          ghost var newSkRight;
          newNodeRight, newSkRight, removedNode := RemoveRec(newNode.right, newSk.right, k);

          assert elems(newSk) <= elems(sk);
          assert unchanged@PreRec(elems(newSk.left));
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNodeRight, newSkRight);

          newNode.right := newNodeRight;
          newSk := Node(newSk.left, newNode, newSkRight);

          assert elems(newSk) <= elems(sk);
          assert allocated(elems(newSk));
          assert unchanged@PreRec(elems(newSk.left));
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode, newSk);
          
          assert TreeModelRec(newSk) == t''';

          newNode, newSk := Restore(newNode, newSk);
          assert ValidRec(newNode, newSk);
          assert elems(newSk) <= elems(sk);
          assert TreeModelRec(newSk) == RBi.Restore(t''') == RBr.Remove(old(TreeModelRec(sk)), k);
        } else {
          label PreRec:
          assert newSk.left.data == newNode.left;
          assert elems(newSk) <= elems(sk);
          assert ValidRec(newNode, newSk);
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode.right, newSk.right);
          assert newNode !in elems(newSk.right);
          assert newNode.left !in elems(newSk.right);
          assert newNode !in elems(newSk.right);
          assert newNode.right !in elems(newSk.left);
          assert elems(newSk.left) !! elems(newSk.right);
          assert allocated(elems(newSk));
          assert RBr.Remove.requires(TreeModelRec(newSk.right), k);

          ghost var newSkRight;
          var newNodeRight;
          newNodeRight, newSkRight, removedNode := RemoveMinRec(newNode.right, newSk.right);

          label PostRec:
          assert newNode !in elems(newSkRight);
          assert newNode.left !in elems(newSkRight);
          assert newNode !in elems(newSk.right);
          assert newNode.right !in elems(newSk.left);
          assert elems(newSk.left) !! elems(newSkRight);
          assert elems(newSk) <= elems(sk);
          assert unchanged@PreRec(elems(newSk.left));
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNodeRight, newSkRight);

          newNode.key := removedNode.key;
          newNode.value := removedNode.value;
          newNode.right := newNodeRight;
          ghost var goodSk := Node(newSk.left, newNode, newSkRight);
          newSk := goodSk;

          assert elems(newSk) <= elems(sk);
          assert allocated(elems(newSk));
          assert unchanged@PreRec(elems(newSk.left));
          assert unchanged@PostRec(elems(newSk.left));
          assert newNode.left == old@PostRec(newNode.left);
          assert old@PostRec(ValidRec(newNode.left, newSk.left));
          assume false;
          assert ValidRec(newNode.left, newSk.left);
          assert ValidRec(newNode.right, newSk.right);
          assume false;


          //assume false;
/*
          assert olºdeLeft);
          assert oldNewNodeLeft == oldNewNodeLeft';
          assert oldNewNodeLeft' == old@PreRec(newNode.left);
          assume false;
          assert oldNewNodeLeft == old@PostRec(newNode.left);
          assert oldNewNodeLeft == old@PreRec(newNode.left);
*/
          assert elems(newSk) <= elems(sk);
          assert allocated(elems(newSk));
          assert unchanged@PreRec(elems(newSk.left));
          assert newSk.left.data == newNode.left;
          assume false;
          //assert newNode.left == old@PreRec(newNode.left);
          assume false;
          //assert unchanged@PreRec(newNode.left);
          assert ValidRec(newNode.left, newSk.left);
          assume false;
          //assert ValidRec(newNode, newSk);

          assert newNode !in elems(newSk.left);
          assert newNode !in elems(newSk.right);
          assert elems(newSk.left) !! elems(newSk.right);
          assume false;
          assert ValidRec(newNode, newSk);

          assume false;
          newNode, newSk := Restore(newNode, newSk);
        }
      }
    }
  }
}
