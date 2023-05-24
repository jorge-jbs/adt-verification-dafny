include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"

module RBTree.SInsert {
  import opened Utils
  import opened KeyValue
  import opened Color

  import opened Base

  function method SInsert(t: rbtree, k': K, v': V): rbtree
  {
    match t {
      case Empty => Leaf(k', v')
      case Node(l, k, v, r, c) =>
        if k < k' then
          Node(l, k, v, SInsert(r, k', v'), c)
        else if k' < k then
          Node(SInsert(l, k', v'), k, v, r, c)
        else
          Node(l, k, v', r, c)
    }
  }

  lemma {:induction} SInsertSpec(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    ensures keys(t) + {k} == keys(SInsert(t, k, v))
    ensures SearchTree(SInsert(t, k, v))
  {}

  lemma {:verify false} SInsertModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires SearchTree(SInsert(t, k, v))
    ensures toMap(t)[k := v] == toMap(SInsert(t, k, v))
  {
    match t {
      case Empty => {
      }
      case Node(l, k', v', r, c) => {
        if k' < k {
          SInsertSpec(r, k, v);
          assume {:axiom} false;
        } else if k < k' {
          SInsertSpec(l, k, v);
          calc == {
            toMap(SInsert(Node(l, k', v', r, c), k, v));
            toMap(Node(SInsert(l, k, v), k', v', r, c));
            { toMapLemmas(Node(SInsert(l, k, v), k', v', r, c)); }
            toMap(SInsert(l, k, v)) + map[k' := v'] + toMap(r);
            toMap(l)[k := v] + map[k' := v'] + toMap(r);
            toMap(l) + map[k := v] + map[k' := v'] + toMap(r);
            toMap(l) + map[k' := v'] + toMap(r) + map[k := v];
            toMap(t) + map[k := v];
          }
        } else {
        }
      }
    }
  }
}
