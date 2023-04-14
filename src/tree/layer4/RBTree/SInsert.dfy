include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/KeyValue.dfy"
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
    ensures model(t)[k := v] == model(SInsert(t, k, v))
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
            model(SInsert(Node(l, k', v', r, c), k, v));
            model(Node(SInsert(l, k, v), k', v', r, c));
            { toMap''Lemmas(Node(SInsert(l, k, v), k', v', r, c)); }
            model(SInsert(l, k, v)) + map[k' := v'] + model(r);
            model(l)[k := v] + map[k' := v'] + model(r);
            model(l) + map[k := v] + map[k' := v'] + model(r);
            model(l) + map[k' := v'] + model(r) + map[k := v];
            model(t) + map[k := v];
          }
        } else {
        }
      }
    }
  }
}
