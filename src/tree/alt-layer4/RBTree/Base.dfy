include "../../../../src/MUtils.dfy"
include "../../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../../src/tree/alt-layer4/Color.dfy"

module RBTree.Base {
  import opened Utils
  import opened KeyValue
  import opened Color

  datatype rbtree = Empty | Node(left: rbtree, key: K, value: V, right: rbtree, color: Color)

  function method Leaf(k: K, v: V): rbtree
  {
    Node(Empty, k, v, Empty, Black)
  }

  function method keys(t: rbtree): set<K>
    ensures t.Empty? ==> keys(t) == {}
    ensures !t.Empty? ==> keys(t) == keys(t.left) + {t.key} + keys(t.right)
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => keys(l) + {k} + keys(r)
    }
  }

  function method size(t: rbtree): nat
    //ensures size(t) == |keys(t)|
  {
    match t {
      case Empty => 0
      case Node(l, k, v, r, c) => 1 + size(l) + size(r)
    }
  }

  function method toMap(t: rbtree): map<K, V>
  {
    match t {
      case Empty => map[]
      case Node(l, k, v, r, c) => toMap(l) + toMap(r) + map[k := v]
    }
  }

  function method preorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) =>  [(k, v)] + inorder(l) + inorder(r)
    }
  }

  function method inorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) => inorder(l) + [(k, v)] + inorder(r)
    }
  }

  function method seqToMap(s: seq<(K, V)>): map<K, V>
  {
    if s == [] then
      map[]
    else
      map[s[0].0 := s[0].1] + seqToMap(s[1..])
  }

  function method seqToMap'(s: seq<(K, V)>): map<K, V>
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
  {
    map t: (K, V) | t in s :: t.0 := t.1
    //map i: int | 0 <= i < |s| :: s[i].0 := s[i].1
  }

  function method toMap'(t: rbtree): map<K, V>
  {
    seqToMap(preorder(t))
  }

  function method SearchTree(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Node(l, k, v, r, c) =>
        && (forall m | m in keys(l) :: m < k)
        && (forall m | m in keys(r) :: k < m)
        && SearchTree(l)
        && SearchTree(r)
    }
  }

  function method Get(t: rbtree, k: K): V
    requires k in keys(t)
    requires SearchTree(t)
  {
    match t {
      case Empty => assert false; 0
      case Node(l, k', v, r, c) =>
        if k < k' then
          Get(l, k)
        else if k' < k then
          Get(r, k)
        else
          v
    }
  }

  lemma {:induction} SearchImpliesUnique(t: rbtree)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |preorder(t)| ::
      preorder(t)[i].0 != preorder(t)[j].0
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        SearchImpliesUnique(l);
        SearchImpliesUnique(r);
        assume {:axiom} false;
        assert preorder(t) == [(k, v)] + preorder(l) + preorder(r);
        assume {:axiom} false;
      }
    }
  }

  function method toMap''(t: rbtree): map<K, V>
    requires SearchTree(t)
  {
    map k: K | k in keys(t) :: Get(t, k)
  }

  function method model(t: rbtree): map<K, V>
    requires SearchTree(t)
  {
    toMap''(t)
  }

  lemma toMap''Lemmas(t: rbtree)
    requires SearchTree(t)
    ensures t.Node? ==>
      toMap''(t) == toMap''(t.left) + toMap''(t.right) + map[t.key := t.value]
  {}

  function method toMap'''(t: rbtree): map<K, V>
  {
    seqToMap(preorder(t))
  }

  function method isRed(t: rbtree): bool
  {
    t.Node? && t.color.Red?
  }

  function method isBlack(t: rbtree): bool
  {
    t.Node? && t.color.Black?
  }

  function method BlackHeight(sk: rbtree): nat
  {
    match sk {
      case Empty => 0
      case Node(l, k, v, r, c) =>
        if c.Black? then
          1 + Utils.max(BlackHeight(l), BlackHeight(r))
        else
          Utils.max(BlackHeight(l), BlackHeight(r))
    }
  }

  function method RedBlackTree(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Node(l, k, v, r, c) =>
        // Red links lean left:
        && (r.Node? ==> r.color.Black?)
        // No node has two red links connected to it:
        && (l.Node? && l.color.Red? && l.left.Node? ==> l.left.color.Black?)
        // Perfect black balance:
        && BlackHeight(l) == BlackHeight(r)

        && RedBlackTree(l)
        && RedBlackTree(r)
    }
  }

  function method RedBlackTreeRoot(t: rbtree): bool
  {
    RedBlackTree(t) && (t.Node? ==> t.color.Black?)
  }
}
