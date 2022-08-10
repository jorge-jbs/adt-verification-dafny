include "../../src/tree/Tree.dfy"
include "../../src/tree/SearchTree.dfy"
include "../../src/tree/TreeData.dfy"

lemma {:verify false} SubAddToAddSubPrime(p: map<K, V>, k: K, v: V, q: K)
  requires q != k
  ensures (p - {q})[k := v] == p[k := v] - {q}
{}

class RedBlackTree {
  var tree: SearchTree;

  function Repr(): set<object>
    reads this, tree, tree.tree
  {
    tree.Repr()
  }

  predicate Valid()
    reads this, tree, tree.tree, tree.Repr()
  {
    && tree.Valid()
    && tree.tree.RedBlackTree()
  }

  function Model(): map<K, V>
    reads this, tree, tree.tree, tree.Repr()
    requires Valid()
  {
    tree.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == map[]
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() :: fresh(x)
    ensures fresh(Repr())
    ensures forall x | x in Repr() :: allocated(x)
  {
    tree := new SearchTree();
  }

  static method {:verify false} RotateLeft(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`right
    modifies node.right`left
    modifies node.right`color

    requires Tree.ValidRec(node, sk)
    requires node.right != null
    requires node.right.color.Red?
    requires node.left != null ==> node.left.color.Black?
    requires node.right.left != null ==> node.right.left.color.Black?
    requires node.right.right != null ==> node.right.right.color.Black?
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures newNode.color == old(node.color)
    ensures newNode.left != null
    ensures newNode.left.color.Red?
    ensures newNode.right != null ==> newNode.right.color.Black?
    ensures newNode.left.left != null ==> newNode.left.left.color.Black?
    ensures newNode.left.right != null ==> newNode.left.right.color.Black?
    ensures Tree.RedBlackTreeRec(newSk.left)
    ensures Tree.RedBlackTreeRec(newSk.right)
    ensures Tree.RedBlackTreeRec(newSk)

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(Node(sk.left, node, sk.right.left), newNode, sk.right.right);
    assert Tree.ValidRec(newNode.right, newSk.right);
    assert Tree.ValidRec(newNode.left.left, newSk.left.left);
    assert Tree.ValidRec(newNode.left.right, newSk.left.right);
    assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) by {
      reveal Tree.ModelRec();
      calc == {
        Tree.ModelRec(newSk);
        Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right)[newNode.key := newNode.value];
        Tree.ModelRec(Node(sk.left, node, sk.right.left)) + Tree.ModelRec(sk.right.right)[newNode.key := newNode.value];
        (Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right.left))[node.key := node.value] + Tree.ModelRec(sk.right.right)[newNode.key := newNode.value];
        (Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right.left)) + map[node.key := node.value] + Tree.ModelRec(sk.right.right) + map[newNode.key := newNode.value];
        {
          assert node.key !in Tree.ModelRec(sk.right.right) by {
            Tree.ModelLemmas(newNode, newSk);
          }
        }
        (Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right.left)) + Tree.ModelRec(sk.right.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        Tree.ModelRec(sk.left) + (Tree.ModelRec(sk.right.left) + Tree.ModelRec(sk.right.right)) + map[node.key := node.value] + map[newNode.key := newNode.value];
        (Tree.ModelRec(sk.left) + (Tree.ModelRec(sk.right.left) + Tree.ModelRec(sk.right.right))[newNode.key := newNode.value])[node.key := node.value];
        (Tree.ModelRec(sk.left) + (Tree.ModelRec(sk.right.left) + Tree.ModelRec(sk.right.right))[old(node.right.key) := old(node.right.value)])[node.key := node.value];
        old((Tree.ModelRec(sk.left) + (Tree.ModelRec(sk.right.left) + Tree.ModelRec(sk.right.right))[node.right.key := node.right.value])[node.key := node.value]);
        old((Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right))[node.key := node.value]);
        old(Tree.ModelRec(sk));
      }
    }
  }

  static method {:verify false} RotateRight(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires Tree.ValidRec(node, sk)
    requires node.color.Black?
    requires node.left != null
    requires node.left.color.Red?
    requires node.left.left != null
    requires node.left.left.color.Red?
    requires node.left.left.left != null ==> node.left.left.left.color.Black?
    requires node.left.left.right != null ==> node.left.left.right.color.Black?
    requires node.left.right != null ==> node.left.right.color.Black?
    requires node.right != null ==> node.right.color.Black?
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures Tree.RedBlackTreeRec(newSk.left)
    ensures Tree.RedBlackTreeRec(newSk.right)
    ensures newNode.color.Black?
    ensures newNode.left != null
    ensures newNode.left.color.Red?
    ensures newNode.left.left != null ==> newNode.left.left.color.Black?
    ensures newNode.left.right != null ==> newNode.left.right.color.Black?
    ensures newNode.right != null
    ensures newNode.right.color.Red?
    ensures newNode.right.left != null ==> newNode.right.left.color.Black?
    ensures newNode.right.right != null ==> newNode.right.right.color.Black?

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node.left;
    node.left := newNode.right;
    newNode.right := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(sk.left.left, newNode, Node(sk.left.right, node, sk.right));
    assert Tree.ValidRec(newNode.left, newSk.left);
    assert Tree.ValidRec(newNode.left.left, newSk.left.left);
    assert Tree.ValidRec(newNode.left.right, newSk.left.right);
    assert Tree.ValidRec(newNode.right.left, newSk.right.left);
    assert Tree.ValidRec(newNode.right.right, newSk.right.right);
    assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) by {
      reveal Tree.ModelRec();
      calc == {
        Tree.ModelRec(newSk);
        Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right)[newNode.key := newNode.value];
        Tree.ModelRec(sk.left.left) + Tree.ModelRec(Node(sk.left.right, node, sk.right)) + map[newNode.key := newNode.value];
        Tree.ModelRec(sk.left.left) + Tree.ModelRec(sk.left.right) + Tree.ModelRec(sk.right) + map[node.key := node.value] + map[newNode.key := newNode.value];
        Tree.ModelRec(sk.left.left) + Tree.ModelRec(sk.left.right) + Tree.ModelRec(sk.right) + map[newNode.key := newNode.value] + map[node.key := node.value];
        {
          assert newNode.key !in Tree.ModelRec(sk.right) by {
            Tree.ModelLemmas(newNode, newSk);
          }
        }
        Tree.ModelRec(sk.left.left) + Tree.ModelRec(sk.left.right) + map[newNode.key := newNode.value] + Tree.ModelRec(sk.right) + map[node.key := node.value];
        old(Tree.ModelRec(sk.left.left) + Tree.ModelRec(sk.left.right) + map[node.left.key := node.left.value] + Tree.ModelRec(sk.right) + map[node.key := node.value]);
        old(Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right) + map[node.key := node.value]);
        old(Tree.ModelRec(sk));
      }
    }
  }

  static method {:verify false} FlipColors(node: TNode, ghost sk: tree<TNode>)
    modifies node`color, node.left`color, node.right`color
    requires Tree.ValidRec(node, sk)
    requires node.color.Black?
    requires node.left != null
    requires node.left.color.Red?
    requires node.left.left != null ==> node.left.left.color.Black?
    requires node.left.right != null ==> node.left.right.color.Black?
    requires node.right != null
    requires node.right.color.Red?
    requires node.right.left != null ==> node.right.left.color.Black?
    requires node.right.right != null ==> node.right.right.color.Black?
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)

    ensures node.color.Red?
    ensures node.left != null
    ensures node.left.color.Black?
    ensures node.left.left != null ==> node.left.left.color.Black?
    ensures node.left.right != null ==> node.left.right.color.Black?
    ensures node.right != null
    ensures node.right.color.Black?
    ensures node.right.left != null ==> node.right.left.color.Black?
    ensures node.right.right != null ==> node.right.right.color.Black?
    ensures Tree.ValidRec(node, sk)
    ensures Tree.SearchTreeRec(sk)
    ensures Tree.BlackHeight(sk) == old(Tree.BlackHeight(sk))
    ensures Tree.RedBlackTreeRec(sk)

    ensures Tree.ModelRec(sk) == old(Tree.ModelRec(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    assert node.left.left != null ==> node.left.left.color.Black?;
    node.color := Red;
    node.left.color := Black;
    node.right.color := Black;
    assert Tree.ValidRec(node.left.left, sk.left.left);
    assert Tree.ValidRec(node.left.right, sk.left.right);
    assert Tree.ValidRec(node.right.left, sk.right.left);
    assert Tree.ValidRec(node.right.right, sk.right.right);
  }

  static method {:verify false} RestoreInsert(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)
    requires !(node.right != null && node.right.color.Red? && node.right.left != null && node.right.left.color.Red?)
    requires node.left != null && node.left.color.Red? && node.right != null && node.right.color.Red? ==>
      node.color.Black? && (node.left.left == null || node.left.left.color.Black?)
    requires node.left != null && node.left.color.Red? && node.left.left != null && node.left.left.color.Red? ==>
      node.color.Black?

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures old(node.color).Black? && newNode.color.Red? ==> newNode.left == null || newNode.left.color.Black?
    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node.left == null || node.left.color.Black? {
      if node.right != null && node.right.color.Red? {
        assert node.right.left != null ==> node.right.left.color.Black?;

        if sk.right.right.Node? {
          assert sk.right.right.data.color.Black?;
          assert Tree.ValidRec(node.right.right, sk.right.right);
          assert sk.right.right.data == node.right.right;
        }
        if node.right.right != null {
          assert Tree.ValidRec(node.right.right, sk.right.right);
        }
        assert node.right.right != null ==> node.right.right.color.Black?;

        newNode, newSk := RotateLeft(node, sk);
      } else {
        assert Tree.RedBlackTreeRec(sk);
        newNode := node;
        newSk := sk;
      }
    } else {
      assert node.left != null;
      assert node.left.color.Red?;
      if node.right != null && node.right.color.Red? {
        assert node.left.color.Red?;
        assert node.right.color.Red?;
        assert node.color.Black?;

        assert Tree.ValidRec(node.left.left, sk.left.left);
        assert Tree.ValidRec(node.left.right, sk.left.right);
        assert Tree.ValidRec(node.right.left, sk.right.left);
        assert Tree.ValidRec(node.right.right, sk.right.right);

        FlipColors(node, sk);
        newNode := node;
        newSk := sk;
      } else {
        assert node.right == null || node.right.color.Black?;
        if node.left.left != null && node.left.left.color.Red? {
          assert node.color.Black?;
          assert Tree.ValidRec(node.left.left, sk.left.left);
          assert Tree.ValidRec(node.left.right, sk.left.right);
          assert Tree.ValidRec(node.left.left.left, sk.left.left.left);
          assert Tree.ValidRec(node.left.left.right, sk.left.left.right);
          newNode, newSk := RotateRight(node, sk);
          FlipColors(newNode, newSk);
        } else {
          if sk.left.left.Node? {
            assert Tree.ValidRec(node.left.left, sk.left.left);
            assert sk.left.left.data == node.left.left;
          }

          assert Tree.RedBlackTreeRec(sk);
          newNode := node;
          newSk := sk;
        }
      }
    }
  }

  static method {:verify false} RBInsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
    returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk)

    /*
      La siguiente precondición es para el FlipColor.

      Si el nodo era rojo, con esta precondición garantizamos
      que el nodo izquierdo y el derecho eran negros. De esta forma, si insertamos a la derecha o a la izquierda
      solo uno de los hijos podrá ser rojo, pero no los dos, y por tanto FlipColor no se ejecutará.

      En cambio, si el hijo izquierdo era rojo, entonces sabemos que el padre era negro, y en el caso de que el
      hijo derecho se vuelva rojo podremos ejecutar FlipColor sin problema (ya que la raíz será negra).
    */
    requires alt_rb: node != null && node.color.Red? ==> node.left == null || node.left.color.Black?

    /*
      La siguiente poscondición es para descartar el caso de tener el hijo derecho rojo y su hijo
      izquierdo (node.right.left) también rojo.
    */
    ensures old(node) != null && old(node.color).Black? && newNode.color.Red? ==>
      newNode.left == null || newNode.left.color.Black?

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v]

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode.RedBlack(null, k, v, null, Red);
      newSk := Node(Empty, newNode, Empty);
      insertedNode := newNode;
      assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v] by {
        reveal Tree.ModelRec();
      }
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
        assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v] by {
          reveal Tree.ModelRec();
        }
      } else if node.key < k {
        ghost var newSkRight;
        node.right, newSkRight, insertedNode := RBInsertRec(node.right, sk.right, k, v);
        assert Tree.ModelRec(newSkRight) == old(Tree.ModelRec(sk.right))[k := v];
        newSk := Node(sk.left, node, newSkRight);
        assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v] by {
          reveal Tree.ModelRec();
        }
      } else if k < node.key {
        ghost var oMMRight := Tree.ModelRec(sk.right);
        ghost var oMMLeft := Tree.ModelRec(sk.left);
        ghost var oMM := Tree.ModelRec(sk);
        Tree.keysSearchTree(sk, k);
        ghost var newSkLeft;
        assert node.left != null && node.left.color.Red? ==> node.left.left == null || node.left.left.color.Black? by {
          if node.left != null && node.left.left != null {
            assert Tree.ValidRec(node.left.left, sk.left.left);
          }
          reveal alt_rb;
        }
        node.left, newSkLeft, insertedNode := RBInsertRec(node.left, sk.left, k, v);
        assert Tree.ModelRec(newSkLeft) == old(Tree.ModelRec(sk.left))[k := v];
        newSk := Node(newSkLeft, node, sk.right);

        assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v] by {
          reveal Tree.ModelRec();
          assert node.key!=k;
          assert node.key==old(node.key) && node.value==old(node.value);
          assert node.key !in oMMLeft && node.key !in oMMRight && node.key !=k;

          assert newSk.left==newSkLeft && newSk.right==sk.right && newSk.data==node;
          assert Tree.ModelRec(newSk.left)==oMMLeft[k:=v];
          assert Tree.ModelRec(newSk.right)==oMMRight;
          assert oMM==(oMMLeft+oMMRight)[node.key:=node.value];
          Tree.oldNewModelRecL(newSk,old(Tree.ModelRec(sk)),oMMLeft,oMMRight,node,k,v);
        }
      } else {
        assert false;
      }
    }
    assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v];

    label A:
    assert !(newNode.right != null && newNode.right.color.Red? && newNode.right.left != null && newNode.right.left.color.Red?) by {
      if newNode.right != null && newNode.right.left != null {
        assert Tree.ValidRec(newNode.right.left, newSk.right.left);
      }
    }
    assert newNode.left != null && newNode.left.color.Red? && newNode.right != null && newNode.right.color.Red? ==>
        newNode.color.Black? && (newNode.left.left == null || newNode.left.left.color.Black?) by {
      if newNode.left != null && newNode.left.left != null {
        assert Tree.ValidRec(newNode.left.left, newSk.left.left);
      }
      reveal alt_rb;
    }
    assert newNode.left != null && newNode.left.color.Red? && newNode.left.left != null && newNode.left.left.color.Red? ==> newNode.color.Black? by{
      reveal alt_rb;
    }
    var newNewNode, newNewSk := RestoreInsert(newNode, newSk);
    assert old(node) != null && old(node.color).Black? && newNewNode.color.Red? ==> newNewNode.left == null || newNewNode.left.color.Black? by{
      assert old@A(newNode.color).Black? && newNewNode.color.Red? ==> newNewNode.left == null || newNewNode.left.color.Black?;
      if old(node) != null && old(node.color).Black? {
        assert old@A(newNode.color) == old(node.color);
        assert old@A(newNode.color).Black?;
      }
    }

    newNode, newSk := newNewNode, newNewSk;
    assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v];
  }
}