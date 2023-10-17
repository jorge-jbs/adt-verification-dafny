include "../../../../src/tree/layer4/AltTRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/AltTTree.dfy"
include "../../../../src/tree/layer4/AltTTNode2.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Rotate {
  import opened KeyValue
  import TRBr = TRBTree.Rotate
  import opened T = TTree
  import opened TTNode
  import opened Color

/*
  method RotateLeft(node: TTNode, ghost sk: ttree<TTNode>, ghost parents: set<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk, parents)
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(newNode, newSk, parents)
    ensures TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    assert ValidRec(node.right, sk.right, parents + {node});
    assert !sk.right.left.Thread? ==> ValidRec(node.right.left, sk.right.left, parents + {node} + {node.right});
    newNode := node.right;
    assert !sk.right.left.Thread? ==> ValidRec(newNode.left, sk.right.left, parents + {node} + {node.right});
    ghost var newSkLeftRight;
    if newNode.isThreadLeft {
      node.right := newNode;
      node.isThreadRight := true;
      newSkLeftRight := T.Thread(newNode);
    } else {
      node.right := newNode.left;
      node.isThreadRight := false;
      newSkLeftRight := sk.right.left;
    }
    assert ValidChild(
      node.right,
      newSkLeftRight,
      node.isThreadRight,
      parents + {node} + {newNode}
    );
    newNode.color := node.color;
    node.color := Red;
    newNode.left := node;
    newNode.isThreadLeft := false;
    newSk := T.Node(T.Node(sk.left, node, newSkLeftRight), newNode, sk.right.right);
    assert ValidRec(newNode, newSk, parents) by {
      assert ValidRec'(
        newNode.left,
        newSk.left,
        parents + {newNode}
      ) by {
        assert ValidChild(
          newNode.left.right,
          newSk.left.right,
          newNode.left.isThreadRight,
          parents + {newNode.left} + {newNode}
        );
        assert ValidChild(
          node.left,
          sk.left,
          node.isThreadLeft,
          parents + {node}
        );
        assert ValidChild(
          node.left,
          sk.left,
          node.isThreadLeft,
          parents + {newNode.left} + {newNode}
        ) by {
          assert parents + {node} <= parents + {newNode.left} + {newNode};
          SubValidChild(
            node.left,
            sk.left,
            node.isThreadLeft,
            parents + {node},
            parents + {newNode.left} + {newNode}
          );
        }
        assert ValidChild(
          newNode.left.left, 
          newSk.left.left, 
          newNode.left.isThreadLeft, 
          parents + {newNode.left} + {newNode}
        );
      }
      assert ValidChild(
        newNode.right, 
        newSk.right, 
        newNode.isThreadRight, 
        parents + {newNode}
      ) by {
        assume false;
      }
    }
    assert TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk))) by {
      assume false;
    }
    assert elems(newSk) == elems(sk) by {
      assume false;
    }
  }
  */

  method RotateLeft(
      node: TTNode,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
      //ghost parents: set<TTNode>
    )
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    //requires ThreadsInParentsRec(sk, parents)
    requires ThreadedNe(prev, sk, next)
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    //ensures ThreadsInParentsRec(newSk, parents)
    ensures ThreadedNe(prev, newSk, next)
    ensures TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    assert trl: ThreadedRecL(Thread(sk.data), sk.right.left, Thread(sk.right.data));
    newNode := node.right;
    ghost var newSkLeftRight;
    if newNode.isThreadLeft {
      node.right := newNode;
      node.isThreadRight := true;
      newSkLeftRight := T.Thread(newNode);
    } else {
      node.right := newNode.left;
      node.isThreadRight := false;
      newSkLeftRight := sk.right.left;
    }
    newNode.color := node.color;
    node.color := Red;
    newNode.left := node;
    newNode.isThreadLeft := false;
    newSk := T.Node(T.Node(sk.left, node, newSkLeftRight), newNode, sk.right.right);
    assert ValidRec(newNode, newSk);
    /*
    assert ThreadsInParentsRec(newSk, parents) by {
      ThreadsInParentsSub(newSk.left.left, parents + {newNode.left}, parents + {newNode} + {newNode.left});
      ThreadsInParentsSub(newSk.left.right, parents + {newNode.left} + {newNode}, parents + {newNode} + {newNode.left});
      ThreadsInParentsSub(newSk.right, parents + {newNode.left} + {newNode}, parents + {newNode});
    }
    */
    assert elems(newSk) == elems(sk);
    assert ThreadedNe(prev, newSk, next) by {
      assert ThreadedRecL(prev, newSk.left, Thread(newSk.data)) by {
        assert ThreadedNe(prev, newSk.left, Thread(newSk.data)) by {
          assert ThreadedRecL(prev, newSk.left.left, Thread(newSk.left.data));
          assert ThreadedRecR(Thread(newSk.left.data), newSk.left.right, Thread(newSk.data)) by {
            reveal trl;
          }
        }
      }
      assert ThreadedRecR(Thread(newSk.data), newSk.right, next);
    }
    assert TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk))) by {
      assume false;
    }
  }

  method RotateRight(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
      //parents: set<TTNode>
    )
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadLeft
    modifies node`left
    modifies node.left`isThreadRight
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    //requires ThreadsInParentsRec(sk, parents)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires TreeModelRec(sk).left.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    //ensures ThreadsInParentsRec(newSk, parents)
    ensures ThreadedNe(prev, newSk, next)
    ensures TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    assert tlr: ThreadedRecR(Thread(sk.left.data), sk.left.right, Thread(sk.data));
    newNode := node.left;
    ghost var newChildRightLeft;
    if newNode.isThreadRight {
      node.left := newNode;
      node.isThreadLeft := true;
      newChildRightLeft := T.Thread(newNode);
    } else {
      node.left := newNode.right;
      node.isThreadLeft := false;
      newChildRightLeft := sk.left.right;
    }
    newNode.right := node;
    newNode.isThreadRight := false;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(sk.left.left, newNode, T.Node(newChildRightLeft, node, sk.right));
    assert ValidRec(newNode, newSk);
    assert elems(newSk) == elems(sk);
    assert ThreadedNe(prev, newSk, next) by {
      assert ThreadedRecL(prev, newSk.left, Thread(newSk.data));
      assert ThreadedRecR(Thread(newSk.data), newSk.right, next) by {
        assert ThreadedNe(Thread(newSk.data), newSk.right, next) by {
          assert ThreadedRecL(Thread(newSk.data), newSk.right.left, Thread(newSk.right.data)) by {
            reveal tlr;
          }
          assert ThreadedRecR(Thread(newSk.right.data), newSk.right.right, next);
        }
      }
    }
    assert TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk))) by {
      assume false;
    }
  }
}
