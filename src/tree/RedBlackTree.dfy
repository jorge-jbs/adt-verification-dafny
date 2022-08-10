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

  static method {:verify false} GFlipColors(node: TNode, ghost sk: tree<TNode>)
    modifies node`color, node.left`color, node.right`color

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires node.left != null
    requires node.left.color == Tree.NegColor(node.color)
    requires node.right != null
    requires node.right.color == Tree.NegColor(node.color)

    ensures Tree.ValidRec(node, sk)
    ensures Tree.SearchTreeRec(sk)
    ensures Tree.BlackHeight(sk) == old(Tree.BlackHeight(sk))
    ensures node.color == Tree.NegColor(old(node.color))
    ensures node.left != null
    ensures node.left.color == Tree.NegColor(old(node.left.color))
    ensures node.right != null
    ensures node.right.color == Tree.NegColor(old(node.right.color))

    ensures Tree.ModelRec(sk) == old(Tree.ModelRec(sk))
    ensures elems(sk) == old(elems(sk))

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(sk), x in old(elems(sk))} | x in elems(sk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(sk)-old(elems(sk)))
    ensures forall x | x in elems(sk) :: allocated(x)
  {
    node.color := Tree.NegColor(node.color);
    node.left.color := Tree.NegColor(node.left.color);
    node.right.color := Tree.NegColor(node.right.color);
  }

  static method {:verify false} GRotateLeft(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`right
    modifies node.right`left
    modifies node.right`color

    requires Tree.ValidRec(node, sk)
    requires Tree.isRed(node.right)
    requires Tree.SearchTreeRec(sk)
    requires sk.right.Node? /* redundant */

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))

    ensures newNode.left == old(node)
    ensures newNode.left.left == old(node.left)
    ensures newNode.left.right == old(node.right.left)
    ensures newNode == old(node.right)
    ensures newNode.right == old(node.right.right)

    ensures newNode.color == old(node.color)
    ensures newNode.left.color == Red

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.left) < size(sk)

    ensures newSk.right == sk.right.right
    ensures newSk.left.Node? /* redundant */
    ensures newSk.left.left == sk.left
    ensures newSk.left.right == sk.right.left

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    assert node.key !in Tree.ModelRec(sk.right) by {
      reveal Tree.ModelRec();
      Tree.ModelLemmas(node, sk);
    }
    newNode := node.right;
    node.right := newNode.left;
    newNode.left := node;
    newNode.color := node.color;
    node.color := Red;
    newSk := Node(Node(sk.left, node, sk.right.left), newNode, sk.right.right);
    calc == {
      size(newSk);
      size(newSk.left) + size(newSk.right) + 1;
      size(newSk.left.left) + size(newSk.left.right) + 1 + size(newSk.right) + 1;
      size(sk.left) + size(sk.right.left) + 1 + size(sk.right.right) + 1;
      size(sk.left) + (size(sk.right.left) + size(sk.right.right) + 1) + 1;
      size(sk.left) + size(sk.right) + 1;
      size(sk);
    }
    calc {
      size(newSk.left);
      == 1 + size(sk.left) + size(sk.right.left);
      < 1 + size(sk.left) + size(sk.right);
      == size(sk);
    }
    assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) by {
      reveal Tree.ModelRec();
      calc == {
        Tree.ModelRec(newSk);
        Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right)[newNode.key := newNode.value];
        Tree.ModelRec(Node(sk.left, node, sk.right.left)) + Tree.ModelRec(sk.right.right)[newNode.key := newNode.value];
        (Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right.left))[node.key := node.value] + Tree.ModelRec(sk.right.right)[newNode.key := newNode.value];
        (Tree.ModelRec(sk.left) + Tree.ModelRec(sk.right.left)) + map[node.key := node.value] + Tree.ModelRec(sk.right.right) + map[newNode.key := newNode.value];
        { assert node.key !in Tree.ModelRec(sk.right.right); }
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

  static method {:verify false} GRotateRight(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies node`color
    modifies node`left
    modifies node.left`right
    modifies node.left`color

    requires Tree.ValidRec(node, sk)
    requires Tree.isRed(node.left)
    requires Tree.SearchTreeRec(sk)
    requires sk.left.Node? /* redundant */

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))

    ensures newNode == old(node.left)
    ensures newNode.left == old(node.left.left)
    ensures newNode.right == old(node)
    ensures newNode.right.left == old(node.left.right)
    ensures newNode.right.right == old(node.right)

    ensures newNode.color == old(node.color)
    ensures newNode.right.color == Red

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.right) < size(sk)

    ensures newSk.left == sk.left.left
    ensures newSk.right.Node? /* redundant */
    ensures newSk.right.left == sk.left.right
    ensures newSk.right.right == sk.right

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
    calc {
      size(newSk.right);
      == 1 + size(sk.left.right) + size(sk.right);
      < 1 + size(sk.left) + size(sk.right);
      == size(sk);
    }
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

  static method {:verify false} RBRestore(node: TNode, ghost sk: tree<TNode>)
    returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires
      || (
        && Tree.isBlack(node)
        && Tree.isRed(node.left)
        && Tree.isRed(node.right)
        && Tree.isRed(node.right.left)
      )
      || !(
        && Tree.isRed(node.right)
        && Tree.isRed(node.right.left)
      )
    requires !(
      && Tree.isRed(node)
      && Tree.isRed(node.left)
      && Tree.isRed(node.right)
    )
    requires !(
      && Tree.isRed(node)
      && Tree.isRed(node.left)
      && Tree.isRed(node.left.left)
    )
    requires Tree.BlackHeight(sk.left) == Tree.BlackHeight(sk.right)
    requires Tree.RedBlackTreeRec(sk.left)
    requires Tree.RedBlackTreeRec(sk.right)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures old(Tree.isBlack(node)) && Tree.isRed(newNode) ==>
      !Tree.isRed(newNode.left)
    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    newNode := node;
    newSk := sk;

    assert !(
      && Tree.isRed(newNode)
      && Tree.isRed(newNode.left)
      && Tree.isRed(newNode.right));

    if newNode.right != null && newNode.right.right != null {
      assert Tree.ValidRec(newNode.right.right, newSk.right.right);
      assert Tree.RedBlackTreeRec(newSk.right);
      assert Tree.RedBlackTreeRec(newSk.right.right);
      assert newNode.right.right.color.Black?;
    }

    if newNode.left!= null && newNode.left.right != null {
      assert Tree.ValidRec(newNode.left.right, newSk.left.right);
      assert Tree.RedBlackTreeRec(newSk.left);
      assert Tree.RedBlackTreeRec(newSk.left.right);
      assert newNode.left.right.color.Black?;
    }

    assert Tree.RedBlackTreeRec(newSk.left);

    label A:
    if Tree.isRed(newNode.right) {
      assert newNode.right.left != newNode by {
        Tree.ParentNotChild2(newNode, newSk);
      }
      assert newNode.right.left != newNode.right by {
        Tree.ParentNotChild1(newNode.right, newSk.right);
      }
      newNode, newSk := GRotateLeft(newNode, newSk);
      assert !(
        && Tree.isRed(newNode)
        && Tree.isRed(newNode.left)
        && Tree.isRed(newNode.left.left));
      assert Tree.RedBlackTreeRec(newSk.right);
      assert newNode.left.right == old(node.right.left);
      assert newNode.left.right != null ==>
        newNode.left.right.color == old(node.right.left.color);
      assert !Tree.isRed(newNode.left.right) || old(
        && Tree.isBlack(node)
        && Tree.isRed(node.left)
        && Tree.isRed(node.right)
        && Tree.isRed(node.right.left)
      );
    } else {
      assert Tree.RedBlackTreeRec(newSk.left);
      assert Tree.RedBlackTreeRec(newSk.right);
    }

    if newNode.left != null {
      assert !Tree.isRed(newNode.left.right) || old(
        && Tree.isBlack(node)
        && Tree.isRed(node.left)
        && Tree.isRed(node.right)
        && Tree.isRed(node.right.left)
      );
    }

    assert !(
      && Tree.isRed(newNode)
      && Tree.isRed(newNode.left)
      && Tree.isRed(newNode.right));

    assert !Tree.isRed(newNode.right);
    assert Tree.RedBlackTreeRec(newSk.right);
    if newNode.left != null {
      assert Tree.RedBlackTreeRec(newSk.left.left);
      assert Tree.RedBlackTreeRec(newSk.left.right);
    }

    label B:
    if Tree.isRed(newNode.left) && Tree.isRed(newNode.left.left) {
      newNode, newSk := GRotateRight(newNode, newSk);
      assert Tree.isRed(newNode.left);
      assert Tree.isRed(newNode.right);
      assert !Tree.isRed(newNode);
      assert Tree.RedBlackTreeRec(newSk.right);
      assert Tree.RedBlackTreeRec(newSk.left);
    } else {
      assert Tree.RedBlackTreeRec(newSk.right);
      if newNode.left != null {
        assert Tree.RedBlackTreeRec(newSk.left.left);
        assert Tree.RedBlackTreeRec(newSk.left.right);
        assert Tree.BlackHeight(newSk.left.left) == Tree.BlackHeight(newSk.left.right);
        assert (newSk.left.left.Node? && newSk.left.left.data.color.Red? && newSk.left.left.left.Node? ==> newSk.left.left.left.data.color.Black?);
        assert (newSk.left.right.Node? ==> newSk.left.right.data.color.Black?) by {
          assert Tree.ValidRec(newNode.left, newSk.left);
          assert Tree.ValidRec(newNode.left.right, newSk.left.right);
          if newSk.left.right.Node? {
            assert newSk.left.right.data == newNode.left.right;
            assert !Tree.isRed(newNode.left.right);
          }
        }
      }
    }

    assert Tree.RedBlackTreeRec(newSk.right);
    assert Tree.RedBlackTreeRec(newSk.left);

    label C:
    if Tree.isRed(newNode.left) && Tree.isRed(newNode.right) {
      GFlipColors(newNode, newSk);
    }

    assert Tree.ValidRec(newNode, newSk);
    assert Tree.SearchTreeRec(newSk);
    assert Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk));
    assert Tree.RedBlackTreeRec(newSk) by {
      assert newSk.right.Node? ==> newSk.right.data.color.Black? by {
        assert !Tree.isRed(newNode.right);
      }
      assert newSk.left.Node? && newSk.left.data.color.Red? && newSk.left.left.Node?
          ==> newSk.left.left.data.color.Black? by {
        if newNode.left != null {
          assert Tree.ValidRec(newNode.left, newSk.left);
          assert Tree.ValidRec(newNode.left.left, newSk.left.left);
          assert !(Tree.isRed(newNode.left) && Tree.isRed(newNode.left.left));
        }
      }
      assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
      assert Tree.RedBlackTreeRec(newSk.left);
      assert Tree.RedBlackTreeRec(newSk.right);
    }
  }

  // 3'30"
  static method {:verify false} MoveRedLeft(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right
    //modifies elems(sk)

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk)
    requires Tree.isRed(node)
    requires Tree.isBlack(node.left)
    requires Tree.isBlack(node.right)
    requires !Tree.isRed(node.left.left)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk.left)
    ensures Tree.RedBlackTreeRec(newSk.right)
    ensures Tree.BlackHeight(newSk.right) == Tree.BlackHeight(newSk.left)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures newNode.left != null && newNode.right != null
    ensures
      || Tree.isRed(newNode.left)
      || Tree.isRed(newNode.left.left)
    ensures
      || (!Tree.isRed(newNode) && Tree.isRed(newNode.left) && Tree.isRed(newNode.right) && !Tree.isRed(newNode.right.left) && !Tree.isRed(newNode.left.left))
      || (Tree.isRed(newNode) && !Tree.isRed(newNode.left) && !Tree.isRed(newNode.right) && Tree.isRed(newNode.left.left))

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.left) < size(sk)

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    GFlipColors(node, sk);
    newNode := node;
    newSk := sk;
    assert Tree.RedBlackTreeRec(newSk.left);
    assert Tree.RedBlackTreeRec(newSk.right);
    if (newNode.right.left != null && newNode.right.left.color.Red?) {
      assert size(newSk.left) < size(sk);
      ghost var newSkRight;
      assert Tree.ValidRec(newNode.right.left, newSk.right.left);
      assert Tree.RedBlackTreeRec(newSk.right.right);
      assert Tree.RedBlackTreeRec(newSk.right.left);
      assert Tree.RedBlackTreeRec(newSk.right.left.left);
      assert Tree.RedBlackTreeRec(newSk.right.left.right);
      label PreRR:
      newNode.right, newSkRight := GRotateRight(newNode.right, newSk.right);
      assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk));
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert unchanged(elems(newSk.right.right));
      assert unchanged(elems(newSk.right.left.left));
      assert unchanged(elems(newSk.right.left.right));
      newSk := Node(newSk.left, newNode, newSkRight);
      assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) by {
        reveal Tree.ModelRec();
      }
      assert size(newSk.left) < size(sk);
      assert unchanged@PreRR(elems(newSk.left));
      assert Tree.RedBlackTreeRec(newSk.left);
      assert Tree.RedBlackTreeRec(newSk.right.left);
      assert Tree.RedBlackTreeRec(newSk.right.right.left);
      assert Tree.RedBlackTreeRec(newSk.right.right.right);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      label PreRL:
      newNode, newSk := GRotateLeft(newNode, newSk);
      assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk));
      assert size(newSk.left) < size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert unchanged@PreRL(elems(newSk.left.left));
      assert unchanged@PreRL(elems(newSk.left.right));
      assert unchanged@PreRL(elems(newSk.right.left));
      assert unchanged@PreRL(elems(newSk.right.right));
      assert Tree.RedBlackTreeRec(newSk.left.left);
      assert Tree.RedBlackTreeRec(newSk.left.right);
      assert Tree.RedBlackTreeRec(newSk.right.left);
      assert Tree.RedBlackTreeRec(newSk.right.right);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      label PreFlip:
      GFlipColors(newNode, newSk);
      assert Tree.ModelRec(newSk) == old(Tree.ModelRec(sk));
      assert size(newSk.left) < size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert Tree.RedBlackTreeRec(newSk.left) by {
        assert unchanged@PreRL(elems(newSk.left.left));
        assert unchanged@PreRL(elems(newSk.left.right));
        assert !Tree.isRed(newNode.left.right);
        assert !Tree.isRed(newNode.left.left.left);
        assert Tree.BlackHeight(newSk.left.left) == Tree.BlackHeight(newSk.left.right);
        assert Tree.RedBlackTreeRec(newSk.left.left);
        assert Tree.RedBlackTreeRec(newSk.left.right);
      }
      assert Tree.RedBlackTreeRec(newSk.right) by {
        assert unchanged@PreRL(elems(newSk.right.left));
        assert unchanged@PreRL(elems(newSk.right.right));
        assert Tree.RedBlackTreeRec(newSk.right.left);
        assert Tree.RedBlackTreeRec(newSk.right.right);
        assert !Tree.isRed(newNode.right.right) by {
          assert newNode.right.right == old(node.right.right);
          assert Tree.ValidRec(newNode.right.right, newSk.right.right);
        }
        assert !Tree.isRed(newNode.right.left) by {
          assert newNode.right.left == old(node.right.left.right);
          assert Tree.ValidRec(newNode.right.left, newSk.right.left);
        }
        assert Tree.BlackHeight(newSk.right.left) == Tree.BlackHeight(newSk.right.right);
      }
      assert Tree.BlackHeight(newSk.left.left) == Tree.BlackHeight(newSk.left.right);
      assert Tree.BlackHeight(newSk.right.left) == Tree.BlackHeight(newSk.right.right);
      assert Tree.RedBlackTreeRec(newSk) by {
        assert Tree.RedBlackTreeRec(newSk.left);
        assert Tree.RedBlackTreeRec(newSk.right);
        assert Tree.isBlack(newNode.right);
        assert Tree.isBlack(newNode.left);
        assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
      }
      assert Tree.isRed(newNode);
      assert Tree.isBlack(newNode.left);
      assert Tree.isBlack(newNode.right);
      assert Tree.isRed(newNode.left.left);
      assert Tree.ValidRec(newNode, newSk);
      assert Tree.SearchTreeRec(newSk);
      assert elems(newSk) == elems(sk);
      assert size(newSk) == size(sk);
      assert forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assert size(newSk.left) < size(sk);
    } else {
      assert Tree.ValidRec(newNode.left.left, newSk.left.left);
      assert !Tree.isRed(newNode) && Tree.isRed(newNode.left) && Tree.isRed(newNode.right) && !Tree.isRed(newNode.right.left) && !Tree.isRed(newNode.left.left);
    }
  }

  static method {:verify false} MoveRedRight(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`right

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk)
    requires Tree.isRed(node)
    requires Tree.isBlack(node.left)
    requires Tree.isBlack(node.right)
    requires !Tree.isRed(node.right.left)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures
      || newNode.right == null
      || newNode.right.color.Red?
      || (newNode.right.left != null && newNode.right.left.color.Red?)
    ensures Tree.RedBlackTreeRec(newSk.left)  // TODO
    ensures Tree.RedBlackTreeRec(newSk.right)  // TODO
    ensures Tree.BlackHeight(newSk.right) == Tree.BlackHeight(newSk.left)  // TODO
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))  // TODO
    ensures newNode.left != null && newNode.right != null  // TODO
    ensures
      || Tree.isRed(newNode.left)
      || Tree.isRed(newNode.left.left)
    ensures  // TODO
      || (!Tree.isRed(newNode) && Tree.isRed(newNode.left) && Tree.isRed(newNode.right) && !Tree.isRed(newNode.left.left) && !Tree.isRed(newNode.right.left) && !Tree.isRed(newNode.right.right))
      || (Tree.isRed(newNode) && !Tree.isRed(newNode.left) && !Tree.isRed(newNode.right) && Tree.isRed(newNode.right.right))

    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))
    ensures elems(newSk) == elems(sk)
    ensures size(newSk) == size(sk)
    ensures size(newSk.right) < size(sk)
    ensures forall n | n in elems(newSk) ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    GFlipColors(node, sk);
    newNode := node;
    newSk := sk;
    if (newNode.left.left != null && newNode.left.left.color.Red?) {
      newNode, newSk := GRotateRight(newNode, newSk);
      GFlipColors(newNode, newSk);
      ghost var newSkRight;
      newNode.right, newSkRight := GRotateLeft(newNode.right, newSk.right);
      newSk := Node(newSk.left, newNode, newSkRight);
      /*
      assert RestorePre(newNode, newSk) by {
        assume false;
      }
      */
    } else {
      assert Tree.ValidRec(newNode.left.left, newSk.left.left);
    }
  }

  // 1'5"
  static method {:verify false} RBRemoveMinRec(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    decreases size(sk)
    modifies elems(sk)
    //modifies set n | n in elems(sk) :: n`color
    //modifies set n | n in elems(sk) :: n`left
    //modifies set n | n in elems(sk) :: n`right

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk)
    requires !(Tree.isRed(node) && Tree.isRed(node.left))
    requires Tree.isRed(node) || Tree.isRed(node.left)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    //ensures old(node.color).Black? && newNode.color.Red? ==>
      //newNode.left == null || newNode.left.color.Black?
    ensures old(Tree.isBlack(node)) && Tree.isRed(newNode) ==> !Tree.isRed(newNode.left)

    ensures removedNode in elems(sk)
    ensures removedNode !in elems(newSk)
    ensures removedNode.key == old(removedNode.key)
    ensures removedNode.value == old(removedNode.value)
    ensures elems(newSk) == elems(sk) - {removedNode}

    //ensures removedNode.key in old(Tree.ModelRec(sk))
    //ensures old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
    //ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) - {removedNode.key}

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)
    ensures forall n | n in elems(newSk) ::
      removedNode.key < n.key

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node.left == null {
      newNode := node.right;
      newSk := sk.right;
      removedNode := node;
      /*
      assert
        && removedNode.key in old(Tree.ModelRec(sk))
        && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
        && Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) - {removedNode.key}
      by {
        reveal Tree.ModelRec();
        calc == {
          Tree.ModelRec(newSk);
          old(Tree.ModelRec(sk.right));
          old(Tree.ModelRec(sk.right)) + (map[removedNode.key := removedNode.value] - {removedNode.key});
          {
            assert removedNode.key !in old(Tree.ModelRec(sk.right)) by {
              Tree.ModelLemmas(node, sk);
            }
          }
          (old(Tree.ModelRec(sk.right)) + map[removedNode.key := removedNode.value]) - {removedNode.key};
          { assert old(Tree.ModelRec(sk.left)) == map[]; }
          (old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right)) + map[removedNode.key := removedNode.value]) - {removedNode.key};
          old(Tree.ModelRec(sk)) - {removedNode.key};
        }
      }
      */
    } else {
      //Tree.ModelLemmas(node, sk);
      newNode := node;
      newSk := sk;
      if newNode.left != null && newNode.left.color.Black?
          && (newNode.left.left == null || newNode.left.left.color.Black?) {
        newNode, newSk := MoveRedLeft(newNode, newSk);
      } else {
        assert !(Tree.isRed(newNode.left) && Tree.isRed(newNode.left.left)) by {
          assert Tree.ValidRec(newNode.left.left, newSk.left.left);
        }
      }
      var newNodeLeft;
      ghost var newSkLeft;
      label PreRec:
      newNodeLeft, newSkLeft, removedNode := RBRemoveMinRec(newNode.left, newSk.left);
      /*
      label PostRec:
      assert Tree.ModelRec(newSkLeft) == old@PreRec(Tree.ModelRec(newSk.left)) - {removedNode.key};
      assert unchanged@PreRec(elems(newSk.right));
      */
      assert Tree.ValidRec(newNode.right, newSk.right);
      assert Tree.SearchTreeRec(newSk.right);
      assert Tree.RedBlackTreeRec(newSk.right);
      newNode.left := newNodeLeft;
      newSk := Node(newSkLeft, newNode, newSk.right);
      /*
      assert
        && removedNode.key in old(Tree.ModelRec(sk))
        && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
        && Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) - {removedNode.key}
      by {
        reveal Tree.ModelRec();
        assert removedNode.key !in old(Tree.ModelRec(sk.right));
        assert newSk.Node?;
        assert Tree.ValidRec(newNode, newSk);
        assert Tree.ModelRec(newSk) == (Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right))[newNode.key := newNode.value];
        //assert Tree.ModelRec(newSk) == Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
        //assert Tree.ModelRec(newSk.right) == old(Tree.ModelRec(sk.right));
        //assert Tree.ModelRec(newSk.left) == old(Tree.ModelRec(sk.left));
        calc == {
          Tree.ModelRec(newSk);
          (Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right))[newNode.key := newNode.value];
          //Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
          {
            //assume Tree.ModelRec(newSkLeft) == old@PreRec(Tree.ModelRec(newSk.left)) - {removedNode.key};
            assume false;
          }
          ((old@PreRec(Tree.ModelRec(newSk.left)) - {removedNode.key}) + Tree.ModelRec(newSk.right))[newNode.key := newNode.value];
          //old(Tree.ModelRec(sk.left)) - {removedNode.key} + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
          {
            //assume false;
            assume removedNode.key !in Tree.ModelRec(newSk.right);
            //assert removedNode.key !in Tree.ModelRec(newSk.right);
            SubAddToAddSub(old(Tree.ModelRec(sk.left)), Tree.ModelRec(newSk.right), removedNode.key);
          }
          (old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) - {removedNode.key})[newNode.key := newNode.value];
          {
            assume false;
            assert removedNode.key != newNode.key;
            SubAddToAddSub(Tree.ModelRec(newSk.right), map[newNode.key := newNode.value], removedNode.key);
          }
          old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value] - {removedNode.key};
          { assume false; }
          old(Tree.ModelRec(sk)) - {removedNode.key};
        }
        assume false;
      }
      assume false;
      */
      assert !(
        && Tree.isRed(newNode.right)
        && Tree.isRed(newNode.right.left)
      ) by {
        if newNode.right != null && newNode.right.left != null {
          assert Tree.ValidRec(newNode.right.left, newSk.right.left);
        }
      }
      assert !(
        && Tree.isRed(newNode)
        && Tree.isRed(newNode.left)
        && Tree.isRed(newNode.left.left)
      ) by {
        if newNode.left != null && newNode.left.left != null {
          assert Tree.ValidRec(newNode.left.left, newSk.left.left);
        }
      }
      newNode, newSk := RBRestore(newNode, newSk);
    }
  }

  static method {:verify false} RBRemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    decreases size(sk)
    //modifies set x | x in elems(sk) :: x`color
    //modifies set x | x in elems(sk) :: x`left
    //modifies set x | x in elems(sk) :: x`right
    modifies elems(sk)

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    requires Tree.RedBlackTreeRec(sk)
    requires
      || node == null
      || Tree.isRed(node)
      || Tree.isRed(node.left)
    requires !(Tree.isRed(node) && Tree.isRed(node.left))

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.RedBlackTreeRec(newSk)
    ensures Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk))
    ensures old(Tree.isBlack(node)) && Tree.isRed(newNode) ==>
      !Tree.isRed(newNode.left)

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures removedNode != null ==>
      && removedNode in elems(sk)
      && removedNode !in elems(newSk)
      && removedNode.key == k
    //ensures k !in old(ModelRec(sk)) <==> removedNode==null
    //ensures ModelRec(newSk)==old(ModelRec(sk))-{k}

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
    } else {
      if node.key > k {
        //assume false;
        newNode := node;
        newSk := sk;
        if Tree.isBlack(newNode.left) && !Tree.isRed(newNode.left.left) {
          newNode, newSk := MoveRedLeft(newNode, newSk);
        } else {
          assert !(Tree.isRed(newNode.left) && Tree.isRed(newNode.left.left)) by {
            assert Tree.RedBlackTreeRec(newSk);
            if newNode.left != null {
              assert Tree.ValidRec(newNode.left.left, newSk.left.left);
            }
          }
        }
        ghost var newSkLeft;
        label PreRec:
        newNode.left, newSkLeft, removedNode := RBRemoveRec(newNode.left, newSk.left, k);
        newSk := Node(newSkLeft, newNode, newSk.right);
        //assume false;
        assert Tree.ValidRec(newNode, newSk);
        assert !(
          && Tree.isRed(newNode.right)
          && Tree.isRed(newNode.right.left)
        ) by {
          assert Tree.ValidRec(newNode.right, newSk.right);
          if newNode.right != null {
            assert Tree.ValidRec(newNode.right.left, newSk.right.left);
          }
        }
        assert !(
          && Tree.isRed(newNode)
          && Tree.isRed(newNode.left)
          && Tree.isRed(newNode.right)
        );
        assert !(
          && Tree.isRed(newNode)
          && Tree.isRed(newNode.left)
          && Tree.isRed(newNode.left.left)
        ) by {
          assert Tree.ValidRec(newNode.left, newSk.left);
          if newNode.left != null {
            assert Tree.ValidRec(newNode.left.left, newSk.left.left);
          }
        }
        assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
        assert Tree.RedBlackTreeRec(newSk.left);
        assert Tree.RedBlackTreeRec(newSk.right);
      } else {
        newNode := node;
        newSk := sk;

        if Tree.isRed(newNode.left) {
          assert Tree.ValidRec(newNode.left.right, newSk.left.right);
          newNode, newSk := GRotateRight(newNode, newSk);
          assert Tree.isRed(newNode.right) || Tree.isRed(newNode.right.left);
          assert !(Tree.isRed(newNode.right) && Tree.isRed(newNode.right.left));
        }

        if k == newNode.key && newNode.right == null {
          label A:
          assert elems(sk) == elems(newSk) == elems(newSk.left) + {newNode};
          assert elems(sk) - {newNode} == elems(newSk) - {newNode} == elems(newSk.left);
          newNode := newNode.left;
          newSk := newSk.left;
          removedNode := newNode;
          assume elems(newSk) == elems(sk) - {removedNode};
          assert elems(newSk) == old@A(elems(newSk) - {newNode}) == old@A(elems(sk)) - {removedNode};
          return;
        }

        if Tree.isBlack(newNode.right) && !Tree.isRed(newNode.right.left) {
          newNode, newSk := MoveRedRight(newNode, newSk);
          assert !(Tree.isRed(newNode.right) && Tree.isRed(newNode.right.left));
        } else {
          assert
            || newNode.right == null
            || Tree.isRed(newNode.right)
            || Tree.isRed(newNode.right.left);
          assert !(Tree.isRed(newNode.right) && Tree.isRed(newNode.right.left));
        }
        assert !(Tree.isRed(newNode.right) && Tree.isRed(newNode.right.left));
        if k == newNode.key {
          //assume false;
          label PreRec:
          ghost var newSkRight;
          newNode.right, newSkRight, removedNode := RBRemoveRec(newNode.right, newSk.right, k);
          newSk := Node(newSk.left, newNode, newSkRight);
          assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
          assert Tree.RedBlackTreeRec(newSk.right);
          assert unchanged@PreRec(elems(newSk.left));
          assert Tree.RedBlackTreeRec(newSk.left);
          assert Tree.ValidRec(newNode, newSk);
          assert || (
              && Tree.isBlack(newNode)
              && Tree.isRed(newNode.left)
              && Tree.isRed(newNode.right)
              && Tree.isRed(newNode.right.left)
          ) || !(
              && Tree.isRed(newNode.right)
              && Tree.isRed(newNode.right.left)
          ) by {
            if Tree.isRed(newNode.right) {
              if old@PreRec(Tree.isBlack(newNode.right)) {
                assert !Tree.isRed(newNode.right.left);
                assert !(
                  && Tree.isRed(newNode.right)
                  && Tree.isRed(newNode.right.left)
                );
              } else if Tree.isRed(newNode.right.left) && old@PreRec(newNode.right != null) {
                assert Tree.isBlack(newNode);
                assert Tree.isRed(newNode.left);
                assert Tree.isRed(newNode.right);
                assert Tree.isRed(newNode.right.left);
              }
            }
            /*
            if old@PreRec(isBlack(newNode.right)) && Tree.isRed(newNode.right) {
              assert !Tree.isRed(newNode.right.left);
              assert !(
                && Tree.isRed(newNode.right)
                && Tree.isRed(newNode.right.left)
              );
            } else if !Tree.isRed(newNode.right) {
              assert !(
                && Tree.isRed(newNode.right)
                && Tree.isRed(newNode.right.left)
              );
            } else if old@PreRec(newNode.right == null) {
              assert !(
                && Tree.isRed(newNode.right)
                && Tree.isRed(newNode.right.left)
              );
            } else if Tree.isRed(newNode.right.left) {
              assert old@PreRec(Tree.isRed(newNode.right)) && Tree.isRed(newNode.right);
              //assert Tree.isRed(newNode.left);
              assert isBlack(newNode);
              assert Tree.isRed(newNode.left);
              assert Tree.isRed(newNode.right);
              assert Tree.isRed(newNode.right.left);
            } else {
            }
            */
          }
          assert !(
            && Tree.isRed(newNode)
            && Tree.isRed(newNode.left)
            && Tree.isRed(newNode.right)
          );
          assert !(
            && Tree.isRed(newNode)
            && Tree.isRed(newNode.left)
            && Tree.isRed(newNode.left.left)
          ) by {
            assert Tree.ValidRec(newNode.left, newSk.left);
            if newNode.left != null {
              assert Tree.ValidRec(newNode.left.left, newSk.left.left);
            }
          }
        } else {
          //assume false;
          if newNode.right == null {
            assume false;
            return;
          }
          removedNode := newNode;
          ghost var oldNewSkLeft := newSk.left;
          var oldNewNodeLeft := newNode.left;
          var oldNewNodeColor := newNode.color;
          assert Tree.RedBlackTreeRec(newSk.left);
          assert !(
            && Tree.isRed(newNode)
            && Tree.isRed(newNode.left)
          );
          label PreRec:
          ghost var newSkRight;
          var newNodeRight;
          var minNode;
          newNodeRight, newSkRight, minNode := RBRemoveMinRec(newNode.right, newSk.right);
          /*
          label PostRec:
          assert old@PreRec(isBlack(newNode.right)) && Tree.isRed(newNodeRight)
            ==> !Tree.isRed(newNodeRight.left);
          assert newNode !in elems(newSkRight);
          assert newNode != newNodeRight;
          assert newNodeRight != null ==> newNode != newNodeRight.left;
          assert minNode !in elems(newSkRight);
          assert minNode != newNodeRight;
          assert newNodeRight != null ==> minNode != newNodeRight.left;
          */
          newNode := minNode;
          /*
          // Somehow Dafny cannot prove the following:
          assume old@PreRec(isBlack(newNode.right)) && old@PostRec(Tree.isRed(newNodeRight))
            ==> old@PostRec(!Tree.isRed(newNodeRight.left));
          assert old@PreRec(isBlack(newNode.right)) && Tree.isRed(newNodeRight)
            ==> !Tree.isRed(newNodeRight.left);
          */
          /*
          assert Tree.isRed(newNodeRight) <==> old@PostRec(Tree.isRed(newNodeRight));
          if newNodeRight != null {
            assert unchanged@PostRec(newNodeRight);
            assert old@PostRec(newNodeRight.color) == newNodeRight.color;
            assert Tree.isRed(newNodeRight.left) <==> old@PostRec(Tree.isRed(newNodeRight.left));
            if newNodeRight.left != null {
              assert unchanged@PostRec(newNodeRight.left);
            }
          }
          */
          newNode.left := oldNewNodeLeft;
          newNode.right := newNodeRight;
          newNode.color := oldNewNodeColor;
          ghost var goodSk := Node(oldNewSkLeft, newNode, newSkRight);
          newSk := goodSk;
          //newSk := Node(oldNewSkLeft, newNode, newSkRight);
          assert || (
              && Tree.isBlack(newNode)
              && Tree.isRed(newNode.left)
              && Tree.isRed(newNode.right)
              && Tree.isRed(newNode.right.left)
          ) || !(
              && Tree.isRed(newNode.right)
              && Tree.isRed(newNode.right.left)
          ) by {
            assume false;
            /*
            assert old@PreRec(isBlack(newNode.right)) && Tree.isRed(newNode.right)
              ==> !Tree.isRed(newNode.right.left);
            if old@PreRec(isBlack(newNode.right)) && Tree.isRed(newNode.right) {
              assert !Tree.isRed(newNode.right.left);
              assert !(
                && Tree.isRed(newNode.right)
                && Tree.isRed(newNode.right.left)
              );
            } else if !Tree.isRed(newNode.right) {
              assert !(
                && Tree.isRed(newNode.right)
                && Tree.isRed(newNode.right.left)
              );
            } else if old@PreRec(newNode.right == null) {
              // The proof would be something like this but Dafny cannot even
              // prove that newNode.right was valid before the call.
              /*
              assert Tree.isRed(newNode.right);
              assert newNode.right != null;
              assert old@PreRec(Tree.ValidRec(newNode.right, newSk.right));
              assert old@PreRec(newSk.right.Empty?);
              assert old@PreRec(elems(newSk.right)) == {};
              assert elems(newSk.right) <= old@PreRec(elems(newSk.right));
              assert elems(newSk.right) == {};
              assert newNode.right in elems(newSk.right);
              assert newNode.right in {};
              assert false;
              */
              assume false;
            } else if Tree.isRed(newNode.right.left) {
              assert old@PreRec(Tree.isRed(newNode.right)) && Tree.isRed(newNode.right);
              //assert Tree.isRed(newNode.left);
              assert isBlack(newNode);
              assert Tree.isRed(newNode.right);
              assume false;
              assert Tree.isRed(newNode.left);
              assert Tree.isRed(newNode.right.left);
            } else {
              assume false;
            }
            */
          }
          assert unchanged@PreRec(elems(newSk.left));
          assert newNode.left != null ==> unchanged@PreRec(newNode.left);
          assert !(
            && Tree.isRed(newNode)
            && Tree.isRed(newNode.left)
            && Tree.isRed(newNode.left.left)
          ) by {
            assert Tree.ValidRec(newNode.left, newSk.left);
            if newNode.left != null {
              assert Tree.ValidRec(newNode.left.left, newSk.left.left);
            }
          }
          assert !(
            && Tree.isRed(newNode)
            && Tree.isRed(newNode.left)
            && Tree.isRed(newNode.right)
          );
          assert Tree.RedBlackTreeRec(newSk.right);
          assert Tree.RedBlackTreeRec(newSk.left);
          assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
          assert Tree.ValidRec(newNode, newSk);
          assert Tree.SearchTreeRec(newSk);
          assert forall n | n in elems(sk) ::
            n.key == old(n.key) && n.value == old(n.value);
          assert elems(newSk) == elems(sk) - {removedNode};
          assert removedNode != null ==>
            && removedNode in elems(sk)
            && removedNode !in elems(newSk)
            && removedNode.key == k by {
            assume false;
          }
        }
        /*
        assume false;
        assert Tree.ValidRec(newNode, newSk);
        assert !(
          && Tree.isRed(newNode)
          && Tree.isRed(newNode.left)
          && Tree.isRed(newNode.right)
        );
        */
      }

      assert || (
          && Tree.isBlack(newNode)
          && Tree.isRed(newNode.left)
          && Tree.isRed(newNode.right)
          && Tree.isRed(newNode.right.left)
      ) || !(
          && Tree.isRed(newNode.right)
          && Tree.isRed(newNode.right.left)
      );
      assert !(
        && Tree.isRed(newNode)
        && Tree.isRed(newNode.left)
        && Tree.isRed(newNode.right)
      );
      assert !(
        && Tree.isRed(newNode)
        && Tree.isRed(newNode.left)
        && Tree.isRed(newNode.left.left)
      );
      assert Tree.BlackHeight(newSk.left) == Tree.BlackHeight(newSk.right);
      assert Tree.RedBlackTreeRec(newSk.left);
      assert Tree.RedBlackTreeRec(newSk.right);
      assert Tree.ValidRec(newNode, newSk);
      assert Tree.SearchTreeRec(newSk);
      newNode, newSk := RBRestore(newNode, newSk);
/*
      assert Tree.ValidRec(node, newSk);
      assert Tree.SearchTreeRec(newSk);
      assume forall n | n in elems(sk) ::
        n.key == old(n.key) && n.value == old(n.value);
      assume elems(newSk) == elems(sk) - {removedNode};
      assume removedNode != null ==>
        && removedNode in elems(sk)
        && removedNode !in elems(newSk)
        && removedNode.key == k;
*/
    }
    assert Tree.BlackHeight(newSk) == old(Tree.BlackHeight(sk));
    assert Tree.RedBlackTreeRec(newSk);
    assert old(Tree.isBlack(node)) && Tree.isRed(newNode) ==>
      !Tree.isRed(newNode.left);
  }
}