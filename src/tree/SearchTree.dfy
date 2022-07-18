include "../../src/tree/Tree.dfy"
include "../../src/tree/TreeData.dfy"

lemma {:verify true} idem(m:map<K,V>,k:K,v:V)
  requires k in m && m[k]==v
  ensures (m-{k})[k:=v]==m
{}

lemma {:verify true} idem2(m:map<K,V>,k:K,v:V)
  requires k !in m
  ensures (m[k:=v])-{k}==m
{}

lemma {:verify true} SubAddToAddSub(p: map<K, V>, q: map<K, V>, k: K)
  requires k !in q
  ensures p - {k} + q == p + q - {k}
{}

class SearchTree {
  var tree: Tree;

  function Repr(): set<object>
    reads this, tree
  {
    tree.Repr()
  }

  predicate Valid()
    reads this, tree, tree.Repr()
  {
    && tree.Valid()
    && tree.SearchTree()
  }

  function Model(): map<K, V>
    reads this, tree, Repr()
    requires Valid()
  {
    tree.Model()
  }

  static function ModelRec(sk: tree<TNode>): map<K, V>
    reads set x | x in elems(sk) :: x`key
    reads set x | x in elems(sk) :: x`value
  {
    Tree.ModelRec(sk)
  }

  constructor()
    ensures Valid()
    ensures Model() == map[]
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() :: fresh(x)
    ensures fresh(Repr())
    ensures forall x | x in Repr() :: allocated(x)
  {
    tree := new Tree();
  }

  static method {:verify true} FindRec(node: TNode?, ghost sk: tree<TNode>, k: K) returns (found: TNode?)
    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)

    ensures Tree.ValidRec(node, sk)
    ensures Tree.SearchTreeRec(sk)
    ensures found == null <==> k !in Tree.ModelRec(sk)
    ensures found != null ==>
      && found.key == k
      && found.value == Tree.ModelRec(sk)[k]
      && found in elems(sk)

    requires forall x | x in elems(sk) :: allocated(x)
  {
    if node == null {
      found := null;
      //assert found != null ==> found.key == k && found.value == Tree.ModelRec(sk)[k] && found in elems(sk);
    } else {
      assert elems(sk) == elems(sk.left) + {sk.data} + elems(sk.right);
      if k == node.key {
        found := node;
        /*
        assert
          && found == null <==> k !in Tree.ModelRec(sk)
        by {
          reveal Tree.ModelRec();
        }
        assert found != null;
        assert found.key == k && found.value == Tree.ModelRec(sk)[k] && found in elems(sk) by {
          reveal Tree.ModelRec();
        }
        */
      } else if node.key < k {
        /*
        assert k !in Tree.ModelRec(sk.left) by {
          reveal Tree.ModelRec();
          Tree.ModelLemmas(node, sk);
        }
        */
        found := FindRec(node.right, sk.right, k);
        //assert Tree.ValidRec(node, sk);
        /*
        assert
          && found == null <==> k !in Tree.ModelRec(sk)
        by {
          reveal Tree.ModelRec();
          Tree.ModelLemmas(node, sk);
          if found != null {
            assert k in Tree.ModelRec(sk.right);
            assert k in Tree.ModelRec(sk.right).Keys;
            Tree.ModelLemmas(node.right, sk.right);
            assert Tree.ModelRec(sk.right).Keys == Tree.TreeKeys(sk.right);
            calc == {
              Tree.ModelRec(sk).Keys;
              Tree.TreeKeys(sk);
              Tree.TreeKeys(sk.left) + Tree.TreeKeys(sk.right) + {node.key};
              Tree.TreeKeys(sk.left) + Tree.ModelRec(sk.right).Keys + {node.key};
            }
            assert k in Tree.ModelRec(sk).Keys;
            assert k in Tree.ModelRec(sk);
          } else {
            assert k !in Tree.ModelRec(sk.right);
            assert k !in Tree.ModelRec(sk.left);
            assert node.key != k;
            assert k !in Tree.ModelRec(sk);
          }
        }
        */
        /*
        assert found != null ==> found.key == k && found.value == Tree.ModelRec(sk)[k] && found in elems(sk) by {
          reveal Tree.ModelRec();
        }
        */
      } else if k < node.key {
        found := FindRec(node.left, sk.left, k);
      } else {
        assert false;
      }
    }
    assert
      && (found == null <==> k !in Tree.ModelRec(sk))
      && (found != null ==> found.key == k && found.value == Tree.ModelRec(sk)[k] && found in elems(sk))
    by {
      reveal Tree.ModelRec();
      Tree.ModelLemmas(node, sk);
    }
  }

  method {:verify true} Find(k: K) returns (found: TNode?)
    requires Valid()
    ensures found == null <==> k !in Model()
    ensures found != null ==>
      && found.key == k
      && found.value == Model()[k]
      && found in elems(tree.skeleton)

    requires forall x | x in Repr() :: allocated(x)
  {
    assert Repr() == elems(tree.skeleton);
    found := FindRec(tree.root, tree.skeleton, k);
  }

  method {:verify true} Search(k: K) returns (b: bool)
    requires Valid()
    ensures b == (k in Model())

    requires forall x | x in Repr() :: allocated(x)
  {
    var found := Find(k);
    return found != null;
  }

  method {:verify true} Get(k: K) returns (v: V)
    requires Valid()
    requires k in Model()
    ensures Model()[k] == v

    requires forall x | x in Repr() :: allocated(x)
  {
    var found := Find(k);
    return found.value;
  }

  static method {:verify true} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
      returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode: TNode)
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)
    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk))[k := v]

    ensures elems(newSk) == elems(sk)+{insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v
    ensures forall n | n in elems(sk) && old(n.key) != k ::
      n.key == old(n.key) && n.value == old(n.value)

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := new TNode(null, k, v, null);
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
        node.right, newSkRight, insertedNode := InsertRec(node.right, sk.right, k, v);
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
        node.left, newSkLeft, insertedNode := InsertRec(node.left, sk.left, k, v);
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
          Tree.oldNewModelRecL(newSk, old(Tree.ModelRec(sk)), oMMLeft, oMMRight, node, k, v);
        }
      } else {
        assert false;
      }
    }
  }

  method {:verify true} Insert(k: K, v: V)
    modifies this, tree, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())[k := v]

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var z;
    tree.root, tree.skeleton, z := InsertRec(tree.root, tree.skeleton, k, v);
  }

  static method {:verify true} RemoveMinRec(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, removedNode: TNode)
    //decreases size(sk)
    modifies elems(sk)

    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)

    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)

    ensures removedNode in elems(sk)
    ensures removedNode !in elems(newSk)
    ensures removedNode.key == old(removedNode.key)
    ensures removedNode.value == old(removedNode.value)
    ensures elems(newSk) == elems(sk) - {removedNode}

    ensures removedNode.key in old(Tree.ModelRec(sk))
    ensures old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
    ensures Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) - {removedNode.key}

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
    } else {
      Tree.ModelLemmas(node, sk);
      newNode := node;
      newSk := sk;
      ghost var newSkLeft;
      newNode.left, newSkLeft, removedNode := RemoveMinRec(newNode.left, newSk.left);
      newSk := Node(newSkLeft, newNode, newSk.right);
      assert
        && removedNode.key in old(Tree.ModelRec(sk))
        && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
        && Tree.ModelRec(newSk) == old(Tree.ModelRec(sk)) - {removedNode.key}
      by {
        reveal Tree.ModelRec();
        assert removedNode.key !in old(Tree.ModelRec(sk.right));
        calc == {
          Tree.ModelRec(newSk);
          Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
          old(Tree.ModelRec(sk.left)) - {removedNode.key} + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
          {
            assert removedNode.key !in Tree.ModelRec(newSk.right);
            SubAddToAddSub(old(Tree.ModelRec(sk.left)), Tree.ModelRec(newSk.right), removedNode.key);
          }
          old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) - {removedNode.key} + map[newNode.key := newNode.value];
          {
            assert removedNode.key != newNode.key;
            SubAddToAddSub(Tree.ModelRec(newSk.right), map[newNode.key := newNode.value], removedNode.key);
          }
          old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value] - {removedNode.key};
          old(Tree.ModelRec(sk)) - {removedNode.key};
        }
      }
    }
  }

  static method {:verify true} RemoveRec(node: TNode?, ghost sk: tree<TNode>, k: K)
      returns (newNode: TNode?, ghost newSk: tree<TNode>, ghost removedNode: TNode?)
    modifies elems(sk)
    requires Tree.ValidRec(node, sk)
    requires Tree.SearchTreeRec(sk)
    ensures Tree.ValidRec(newNode, newSk)
    ensures Tree.SearchTreeRec(newSk)

    ensures forall n | n in elems(sk) ::
      n.key == old(n.key) && n.value == old(n.value)
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures removedNode != null ==>
      && removedNode in elems(sk)
      && removedNode !in elems(newSk)
      && removedNode.key == k

    ensures removedNode == null <==> k !in old(ModelRec(sk))
    ensures removedNode != null ==>
      && removedNode.key in old(Tree.ModelRec(sk))
      && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
    ensures ModelRec(newSk) == old(ModelRec(sk)) - {k}

    requires forall x | x in elems(sk) :: allocated(x)
    ensures forall x {:trigger x in elems(newSk), x in old(elems(sk))} | x in elems(newSk) - old(elems(sk)) :: fresh(x)
    ensures fresh(elems(newSk)-old(elems(sk)))
    ensures forall x | x in elems(newSk) :: allocated(x)
  {
    if node == null {
      newNode := node;
      newSk := sk;
      removedNode := null;
      assert
        && ModelRec(newSk) == old(ModelRec(sk)) - {k}
        && (removedNode != null ==>
          && removedNode.key in old(Tree.ModelRec(sk))
          && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
          && ModelRec(newSk) == old(ModelRec(sk)) - {removedNode.key})
        && (removedNode == null <==> k !in old(ModelRec(sk)))
      by {
        reveal Tree.ModelRec();
      }
    } else {
      if node.key > k {
        assert k !in Tree.ModelRec(sk.right) by {
          assert k !in Tree.TreeKeys(sk.right);
          Tree.ModelLemmas(node.right, sk.right);
        }
        newNode := node;
        newSk := sk;
        ghost var newSkLeft;
        newNode.left, newSkLeft, removedNode := RemoveRec(newNode.left, newSk.left, k);
        newSk := Node(newSkLeft, newNode, newSk.right);

        assert
          && ModelRec(newSk) == old(ModelRec(sk)) - {k}
          && (removedNode != null ==>
            && removedNode.key in old(Tree.ModelRec(sk))
            && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
            && ModelRec(newSk) == old(ModelRec(sk)) - {removedNode.key})
          && (removedNode == null <==> k !in old(ModelRec(sk)))
        by {
          reveal Tree.ModelRec();
          assert k !in old(Tree.ModelRec(sk.right));
          if removedNode != null {
            calc == {
              Tree.ModelRec(newSk);
              Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
              old(Tree.ModelRec(sk.left)) - {removedNode.key} + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
              {
                assert removedNode.key !in Tree.ModelRec(newSk.right);
                SubAddToAddSub(old(Tree.ModelRec(sk.left)), Tree.ModelRec(newSk.right), removedNode.key);
              }
              old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) - {removedNode.key} + map[newNode.key := newNode.value];
              {
                assert removedNode.key != newNode.key;
                SubAddToAddSub(Tree.ModelRec(newSk.right), map[newNode.key := newNode.value], removedNode.key);
              }
              old(Tree.ModelRec(sk.left)) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value] - {removedNode.key};
              old(Tree.ModelRec(sk)) - {removedNode.key};
            }
          }
        }
      } else {
        newNode := node;
        newSk := sk;

        if k == newNode.key && newNode.right == null {
          assert node.key !in ModelRec(sk.left) by {
            Tree.ModelLemmas(node, sk);
          }
          assert elems(sk) == elems(newSk) == elems(newSk.left) + {newNode};
          assert elems(sk) - {newNode} == elems(newSk) - {newNode} == elems(newSk.left);
          removedNode := newNode;
          newNode := newNode.left;
          newSk := newSk.left;
          assert Tree.ValidRec(node, sk);
          assert elems(newSk) == elems(sk) - {removedNode};
          assert
            && ModelRec(newSk) == old(ModelRec(sk)) - {k}
            && (removedNode != null ==>
              && removedNode.key in old(Tree.ModelRec(sk))
              && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
              && ModelRec(newSk) == old(ModelRec(sk)) - {removedNode.key})
            && (removedNode == null <==> k !in old(ModelRec(sk)))
          by {
            reveal Tree.ModelRec();
            calc == {
              ModelRec(newSk);
              old(ModelRec(sk.left));
              old(ModelRec(sk.left)) + (map[node.key := node.value] - {k});
              { assert node.key !in ModelRec(sk.left); }
              old(ModelRec(sk.left)) + map[node.key := node.value] - {k};
              { assert old(ModelRec(sk.right)) == map[]; }
              old(ModelRec(sk.left) + ModelRec(sk.right) + map[node.key := node.value]) - {k};
              old(ModelRec(sk)) - {k};
            }
          }
          return;
        }

        if k != newNode.key {
          assert k !in Tree.ModelRec(sk.left) by {
            assert k !in Tree.TreeKeys(sk.left);
            Tree.ModelLemmas(node.left, sk.left);
          }
          ghost var newSkRight;
          newNode.right, newSkRight, removedNode := RemoveRec(newNode.right, newSk.right, k);
          newSk := Node(newSk.left, newNode, newSkRight);
          assert
            && ModelRec(newSk) == old(ModelRec(sk)) - {k}
            && (removedNode != null ==>
              && removedNode.key in old(Tree.ModelRec(sk))
              && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
              && ModelRec(newSk) == old(ModelRec(sk)) - {removedNode.key})
            && (removedNode == null <==> k !in old(ModelRec(sk)))
          by {
            reveal Tree.ModelRec();
            assert k !in old(Tree.ModelRec(sk.left));
            if removedNode != null {
              calc == {
                Tree.ModelRec(newSk);
                Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
                Tree.ModelRec(newSk.left) + old(Tree.ModelRec(sk.right)) - {removedNode.key} + map[newNode.key := newNode.value];
                {
                  assert removedNode.key != newNode.key;
                  SubAddToAddSub(old(Tree.ModelRec(sk.right)), map[newNode.key := newNode.value], removedNode.key);
                }
                Tree.ModelRec(newSk.left) + old(Tree.ModelRec(sk.right)) + map[newNode.key := newNode.value] - {removedNode.key};
                old(Tree.ModelRec(sk)) - {removedNode.key};
              }
            }
          }
        } else {
          assert newNode.right != null;
          assert k !in ModelRec(sk.left) && k !in ModelRec(sk.right) by {
            Tree.ModelLemmas(node, sk);
          }
          removedNode := newNode;
          ghost var oldNewSkLeft := newSk.left;
          var oldNewNodeLeft := newNode.left;
          ghost var newSkRight;
          var newNodeRight;
          var minNode;
          newNodeRight, newSkRight, minNode := RemoveMinRec(newNode.right, newSk.right);
          newNode := minNode;
          newNode.left := oldNewNodeLeft;
          newNode.right := newNodeRight;
          ghost var goodSk := Node(oldNewSkLeft, newNode, newSkRight);
          newSk := goodSk;
          assert
            && ModelRec(newSk) == old(ModelRec(sk)) - {k}
            && (removedNode != null ==>
              && removedNode.key in old(Tree.ModelRec(sk))
              && old(Tree.ModelRec(sk))[removedNode.key] == removedNode.value
              && ModelRec(newSk) == old(ModelRec(sk)) - {removedNode.key})
            && (removedNode == null <==> k !in old(ModelRec(sk)))
          by {
            reveal Tree.ModelRec();
            calc == {
              Tree.ModelRec(newSk);
              Tree.ModelRec(newSk.left) + Tree.ModelRec(newSk.right) + map[newNode.key := newNode.value];
              Tree.ModelRec(newSk.left) + old(Tree.ModelRec(sk.right)) - {minNode.key} + map[minNode.key := minNode.value];
              { idem(old(Tree.ModelRec(sk.right)), minNode.key, minNode.value); }
              Tree.ModelRec(newSk.left) + old(Tree.ModelRec(sk.right));
              old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right));
              old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right)) + map[];
              { assert map[removedNode.key := removedNode.value] - {removedNode.key} == map[]; }
              old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right)) + (map[removedNode.key := removedNode.value] - {removedNode.key});
              { idem2(old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right)), removedNode.key, removedNode.value); }
              old(Tree.ModelRec(sk.left)) + old(Tree.ModelRec(sk.right)) + map[removedNode.key := removedNode.value] - {removedNode.key};
              old(Tree.ModelRec(sk)) - {removedNode.key};
            }
          }
        }
      }
    }
  }

  method {:verify true} Remove(k: K)
    modifies this, tree, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) - {k}

    requires forall x | x in Repr() :: allocated(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var z;
    tree.root, tree.skeleton, z := RemoveRec(tree.root, tree.skeleton, k);
  }
}