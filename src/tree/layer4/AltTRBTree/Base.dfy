include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module {:options "-functionSyntax:4"} TRBTree.Base {
  import opened Utils
  import opened Utils.Printer
  import opened KeyValue
  import opened Color
  import opened OrderedSetUtils

  datatype trbtreeOrThread
    = Empty
    | Thread(thread: K)
    | Node(left: trbtreeOrThread, key: K, value: V, right: trbtreeOrThread, color: Color)

  type trbtree = t: trbtreeOrThread | t.Empty? || t.Node? witness Empty
  type netrbtree
    = t: trbtreeOrThread
    | t.Node?
    witness Node(Empty, 0, 0, Empty, Black)

  function ident(): string
  {
    "|   "
  }

  function trbtreeToString'(prefix: string, t: trbtreeOrThread): string
    decreases t
  {
    match t {
      case Empty => prefix + "Empty"
      case Thread(k) => prefix + "Thread(" + intToString(k) + ")"
      case Node(l, k, v, r, c) =>
        prefix + "Node(\n" +
        trbtreeToString'(prefix + ident(), l) + ",\n" +
        prefix + ident() + intToString(k) + ",\n" +
        prefix + ident() + intToString(v) + ",\n" +
        trbtreeToString'(prefix + ident(), r) + ",\n" +
        prefix + ident() + colorToString(c) + "\n" +
        prefix + ")"
    }
  }

  function trbtreeToString(t: trbtreeOrThread): string
  {
    trbtreeToString'("", t)
  }

  function keys(t: trbtreeOrThread): set<K>
  {
    match t {
      case Empty => {}
      case Thread(k) => {}
      case Node(l, k, v, r, c) => keys(l) + {k} + keys(r)
    }
  }

  function threads(t: trbtreeOrThread): set<K>
  {
    match t {
      case Empty => {}
      case Thread(k) => {k}
      case Node(l, k, v, r, c) => threads(l) + threads(r)
    }
  }

  function keysAndThreads(t: trbtreeOrThread): set<K>
  {
    match t {
      case Empty => {}
      case Thread(k) => {k}
      case Node(l, k, v, r, c) => keysAndThreads(l) + {k} + keysAndThreads(r)
    }
  }

/*
  lemma KeysLemmasAll()
    ensures forall p: pointer | p.Child? ::
      && (keys(p.child) == keys(p))
      && (p.child.Node? && p.child.left.Child? && p.child.right.Child? ==>
        keys(p.child) == keys(p.child.left.child) + {p.child.key} + keys(p.child.right.child))
      && (p.child.Node? && p.child.left.Child? && p.child.right.Thread? ==>
        keys(p.child) == keys(p.child.left.child) + {p.child.key})
      && (p.child.Node? && p.child.left.Thread? && p.child.right.Child? ==>
        keys(p.child) == {p.child.key} + keys(p.child.right.child))
      && (p.child.Node? && p.child.left.Thread? && p.child.right.Thread? ==>
        keys(p.child) == {p.child.key})
    ensures forall t: trbtree | t.Node? ::
      && (t.left.Child? && t.right.Child? ==>
        keys(t) == keys(t.left.child) + {t.key} + keys(t.right.child))
      && (t.left.Child? && t.right.Thread? ==>
        keys(t) == keys(t.left.child) + {t.key})
      && (t.left.Thread? && t.right.Child? ==>
        keys(t) == {t.key} + keys(t.right.child))
      && (t.left.Thread? && t.right.Thread? ==>
        keys(t) == {t.key})
  {}

  lemma KeysLemmas(t: trbtree)
    ensures t.Node? ==>
      && (t.left.Child? && t.right.Child? ==>
        keys(t) == keys(t.left.child) + {t.key} + keys(t.right.child))
      && (t.left.Child? && t.right.Thread? ==>
        keys(t) == keys(t.left.child) + {t.key})
      && (t.left.Thread? && t.right.Child? ==>
        keys(t) == {t.key} + keys(t.right.child))
      && (t.left.Thread? && t.right.Thread? ==>
        keys(t) == {t.key})
  {}
  */

  function values(t: trbtreeOrThread): set<V>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => values(l) + {v} + values(r)
    }
  }

  function pairs(t: trbtreeOrThread): set<(K, V)>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => pairs(l) + {(k, v)} + pairs(r)
    }
  }

  function size(t: trbtreeOrThread): nat
  {
    match t {
      case Empty => 0
      case Thread(_) => 0
      case Node(l, k, v, r, c) => 1 + size(l) + size(r)
    }
  }

  /*
  function toMapRec(t: trbtree): map<K, V>
  {
    match t {
      case Empty => map[]
      case Node(l, k, v, r, c) => toMapRec(l) + toMapRec(r) + map[k := v]
    }
  }
  */

  function preorder(t: trbtreeOrThread): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(l, k, v, r, c) =>  [(k, v)] + preorder(l) + preorder(r)
    }
  }

  function inorder(t: trbtreeOrThread): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(l, k, v, r, c) => inorder(l) + [(k, v)] + inorder(r)
    }
  }

  function smallerInorder(t: trbtreeOrThread, k': K): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(l, k, v, r, c) =>
        if k < k' then
          inorder(l) + [(k, v)] + smallerInorder(r, k')
        else if k' < k then
          smallerInorder(l, k')
        else
          inorder(l)
    }
  }

  function smallerKeys(t: trbtreeOrThread, k': K): set<K>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) =>
        if k < k' then
          keys(l) + {k} + smallerKeys(r, k')
        else if k' < k then
          smallerKeys(l, k')
        else
          keys(l)
    }
  }

  function sizeSmaller(t: trbtreeOrThread, k': K): nat
  {
    match t {
      case Empty => 0
      case Thread(_) => 0
      case Node(l, k, v, r, c) =>
        if k < k' then
          1 + size(l) + sizeSmaller(r, k')
        else if k' < k then
          sizeSmaller(l, k')
        else
          size(l)
    }
  }

  function minimumKey(t: netrbtree): K
  {
    match t {
      case Node(Thread(_), k, v, r, c) => k
      case Node(Empty(), k, v, r, c) => k
      case Node(l, k, v, r, c) => minimumKey(l)
    }
  }

  function orderKeysToSet(s: seq<(K, V)>): set<K>
  {
    set p | p in s :: p.0
  }

  function orderToSet(s: seq<(K, V)>): set<(K, V)>
  {
    set p | p in s :: p
  }

  function orderKeysToSeq(s: seq<(K, V)>): seq<K>
  {
    seq(|s|, i requires 0 <= i < |s| => s[i].0)
  }

  function orderToMap(s: seq<(K, V)>): map<K, V>
  {
    if s == [] then
      map[]
    else
      map[s[0].0 := s[0].1] + orderToMap(s[1..])
  }

  function orderToMap'(s: seq<(K, V)>): map<K, V>
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
  {
    map t: (K, V) | t in s :: t.0 := t.1
    //map i: int | 0 <= i < |s| :: s[i].0 := s[i].1
  }

  function toMapSeq(t: trbtree): map<K, V>
  {
    orderToMap(preorder(t))
  }

  function SearchTree(t: trbtreeOrThread): bool
  {
    match t {
      case Empty => true
      case Thread(_) => true
      case Node(l, k, v, r, c) =>
        && (forall m | m in keys(l) :: m < k)
        && (forall m | m in keys(r) :: k < m)
        && SearchTree(l)
        && SearchTree(r)
    }
  }

  function Get(t: trbtreeOrThread, k: K): V
    requires k in keys(t)
    requires SearchTree(t)
  {
    if k < t.key then
      assert k !in keys(t.right);
      Get(t.left, k)
    else if t.key < k then
      assert k !in keys(t.left);
      Get(t.right, k)
    else
      t.value
  }

  function GetSubtree(t: trbtreeOrThread, k: K): trbtree
    requires k in keys(t)
    requires SearchTree(t)
    ensures Subtree(GetSubtree(t, k), t)
    ensures GetSubtree(t, k).Node?
    ensures GetSubtree(t, k).key == k
  {
    if k < t.key then
      assert k !in keys(t.right);
      GetSubtree(t.left, k)
    else if t.key < k then
      assert k !in keys(t.left);
      GetSubtree(t.right, k)
    else
      t
  }

  function minSubtree(t: trbtree): trbtree
    requires keys(t) != {}
    ensures Subtree(minSubtree(t), t)
    ensures minSubtree(t).Node?
    ensures inorder(t)[0].0 == minSubtree(t).key
  {
    if t.left.Node? then
      minSubtree(t.left)
    else
      t
  }

  function maxSubtree(t: trbtree): trbtree
    requires keys(t) != {}
    requires SearchTree(t)
    ensures Subtree(maxSubtree(t), t)
    ensures maxSubtree(t).Node?
  {
    if t.right.Node? then
      maxSubtree(t.right)
    else
      t
  }

  function toMap(t: trbtree): map<K, V>
    requires SearchTree(t)
  {
    map k: K | k in keys(t) :: Get(t, k)
  }

  predicate Subtree(node: trbtree, root: trbtreeOrThread)
    ensures Subtree(node, root) ==> keys(node) <= keys(root)
    ensures Subtree(node, root) ==> keysAndThreads(node) <= keysAndThreads(root)
    ensures Subtree(node, root) && SearchTree(root) ==> SearchTree(node)
  {
    || root == node
    || (
      && root.Node?
      && (Subtree(node, root.left) || Subtree(node, root.right))
    )
  }

  lemma orderKeysToSetAdd(r: seq<(K, V)>, s: seq<(K, V)>)
    ensures orderKeysToSet(r) + orderKeysToSet(s) == orderKeysToSet(r + s)
  {}

  lemma orderKeysToSetCardBase(s: seq<(K, V)>)
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
    requires s != []
    ensures orderKeysToSet(s) == {s[0].0} + orderKeysToSet(s[1..])
    ensures |orderKeysToSet(s)| == 1 + |orderKeysToSet(s[1..])|
  {
    orderKeysToSetAdd([s[0]], s[1..]);
    calc == {
      {s[0].0} + orderKeysToSet(s[1..]);
      orderKeysToSet([s[0]]) + orderKeysToSet(s[1..]);
      orderKeysToSet([s[0]] + s[1..]);
      orderKeysToSet(s);
    }
  }

  lemma addCard<A>(r: set<A>, s: set<A>)
    requires r !! s
    ensures |r + s| == |r| + |s|
  {}

  lemma subCard<A>(r: set<A>, s: set<A>)
    requires s <= r
    ensures |r - s| == |r| - |s|
  {}

  lemma setDisjoint<A>(r: set<A>, s: set<A>)
    requires forall x, y | x in r && y in s :: x != y
    ensures r !! s
  {}

  lemma orderKeysToSetCard(s: seq<(K, V)>)
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
    ensures |s| == |orderKeysToSet(s)|
  {
    if s == [] {
    } else {
      orderKeysToSetCard(s[1..]);
      calc == {
        |s|;
        1 + |s[1..]|;
        1 + |orderKeysToSet(s[1..])|;
        |{s[0].0}| + |orderKeysToSet(s[1..])|;
        { assert orderKeysToSet([s[0]]) == {s[0].0}; }
        |orderKeysToSet([s[0]])| + |orderKeysToSet(s[1..])|;
        |orderKeysToSet([s[0]]) + orderKeysToSet(s[1..])|;
        { assert orderKeysToSet([s[0]]) + orderKeysToSet(s[1..]) == orderKeysToSet([s[0]] + s[1..]); }
        |orderKeysToSet([s[0]] + s[1..])|;
        { assert [s[0]] + s[1..] == s; }
        |orderKeysToSet(s)|;
      }
    }
  }

  lemma {:verify false} orderToSetCard(s: seq<(K, V)>)
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
    ensures |s| == |orderToSet(s)|
  {
    if s == [] {
    } else {
      orderToSetCard(s[1..]);
      calc == {
        |s|;
        1 + |s[1..]|;
        1 + |orderToSet(s[1..])|;
        |{s[0].0}| + |orderToSet(s[1..])|;
        { assert orderToSet([s[0]]) == {s[0]}; }
        |orderToSet([s[0]])| + |orderToSet(s[1..])|;
        |orderToSet([s[0]]) + orderToSet(s[1..])|;
        { assert orderToSet([s[0]]) + orderToSet(s[1..]) == orderToSet([s[0]] + s[1..]); }
        |orderToSet([s[0]] + s[1..])|;
        { assert [s[0]] + s[1..] == s; }
        |orderToSet(s)|;
      }
    }
  }

  lemma NonEmptyOrderKeysToSet(s: seq<(K, V)>)
    requires s != []
    ensures orderKeysToSet(s) != {}
  {
    assert s[0] in s;
    assert s[0].0 in orderKeysToSet(s);
  }

  lemma OrderKeysIsTreeKeys(t: trbtreeOrThread)
    ensures orderKeysToSet(inorder(t)) == keys(t)
  {}

  lemma {:verify false} OrderSetIsTreePairs(t: trbtree)
    ensures orderToSet(inorder(t)) == pairs(t)
  {}

  lemma SmallerOrderKeysIsTreeKeys(t: trbtreeOrThread, k': K)
    ensures orderKeysToSet(smallerInorder(t, k')) == smallerKeys(t, k')
  {
    match t {
      case Empty => {
      }
      case Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          //keys(l) + {k} + smallerKeys(r, k')
          OrderKeysIsTreeKeys(l);
          SmallerOrderKeysIsTreeKeys(r, k');
        } else if k' < k {
          //smallerKeys(l, k')
          SmallerOrderKeysIsTreeKeys(l, k');
        } else {
          //keys(l)
          OrderKeysIsTreeKeys(l);
        }
      }
    }
  }

  lemma KeySetSeq(s: seq<(K, V)>)
    ensures orderKeysToSet(s)
      == (set k | k in orderKeysToSeq(s))
      == (set i | 0 <= i < |s| :: orderKeysToSeq(s)[i])
    ensures forall k ::
      && (k in orderKeysToSet(s)
        <==> k in orderKeysToSeq(s))
      && (k in orderKeysToSet(s)
        <==> exists i | 0 <= i < |s| :: orderKeysToSeq(s)[i] == k)
  {
    forall k
      ensures (k in orderKeysToSet(s)
        <==> k in orderKeysToSeq(s))
      ensures (k in orderKeysToSet(s)
        <==> exists i | 0 <= i < |s| :: orderKeysToSeq(s)[i] == k)
    {
      if k in orderKeysToSet(s) {
        var v :| (k, v) in s;
        var n :| 0 <= n < |s| && s[n] == (k, v);
        assert orderKeysToSeq(s)[n] == k;
      } else {
      }
    }
  }

  lemma KeyInOrder(t: trbtree, k': K)
    requires k' in keys(t)
    ensures exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k'
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => {
        if k' in keys(l) {
          KeyInOrder(l, k');
          var i :| 0 <= i < |inorder(l)| && inorder(l)[i].0 == k';
          assert inorder(t)[i].0 == k';
        } else if k' in keys(r) {
          KeyInOrder(r, k');
          var i :| 0 <= i < |inorder(r)| && inorder(r)[i].0 == k';
          var j := i+|inorder(l)|+1;
          assert 0 <= j < |inorder(t)|;
          assert inorder(t)[j].0 == k';
        } else {
          assert k == k';
          assert inorder(t)[|inorder(l)|].0 == k';
        }
      }
    }
  }

  lemma ForallKeyInOrder(t: trbtree)
    ensures forall k | k in keys(t) ::
      exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k
  {
    forall k | k in keys(t)
      ensures (exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k)
    {
      KeyInOrder(t, k);
    }
    assert forall k | k in keys(t) :: (exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k);
  }

  lemma OrderInKeysAndValues(t: trbtree)
    ensures forall i | 0 <= i < |inorder(t)| ::
      && inorder(t)[i].0 in keys(t)
      && inorder(t)[i].1 in values(t)
  {}

  lemma KeySetIsOrderKeysR(t: trbtreeOrThread, P: K -> bool)
    requires forall k | k in keys(t) :: P(k)
    ensures forall i | 0 <= i < |inorder(t)| :: P(inorder(t)[i].0)
  {
    forall i | 0 <= i < |inorder(t)|
      ensures P(inorder(t)[i].0)
    {
      OrderInKeysAndValues(t);
      assert inorder(t)[i].0 in keys(t);
    }
  }

  lemma KeySetIsOrderKeys(t: trbtree, P: K -> bool)
    ensures
      (forall k | k in keys(t) :: P(k))
        ==> (forall i | 0 <= i < |inorder(t)| :: P(inorder(t)[i].0))
    ensures
      (forall i | 0 <= i < |inorder(t)| :: P(inorder(t)[i].0))
        ==> (forall k | k in keys(t) :: P(k))
  {
    if (forall k | k in keys(t) :: P(k)) {
      forall i | 0 <= i < |inorder(t)|
        ensures P(inorder(t)[i].0)
      {
        OrderInKeysAndValues(t);
        assert inorder(t)[i].0 in keys(t);
      }
    }
    if (forall i | 0 <= i < |inorder(t)| :: P(inorder(t)[i].0)) {
      forall k | k in keys(t)
        ensures P(k)
      {
        ForallKeyInOrder(t);
        assert (exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k);
      }
    }
  }

  lemma SearchImpliesOrdered(t: trbtreeOrThread)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |inorder(t)| ::
      inorder(t)[i].0 < inorder(t)[j].0
  {
    match t {
      case Empty => {
      }
      case Thread(_) => {
      }
      case Node(l, k, v, r, c) => {
        assert keys(l) == keys(l);
        KeySetIsOrderKeysR(l, m => m < k);
        assert keys(r) == keys(r);
        KeySetIsOrderKeysR(r, m => k < m);
      }
    }
  }

  lemma GetInorder(t: trbtree, i: nat)
    requires 0 <= i < |inorder(t)|
    requires SearchTree(t)
    ensures keys(t) == orderKeysToSet(inorder(t))
    ensures Get(t, inorder(t)[i].0) == inorder(t)[i].1
  {
    var k := inorder(t)[i].0;
    SearchImpliesOrdered(t);
    OrderKeysIsTreeKeys(t);
    assert t.key == inorder(t)[|inorder(t.left)|].0;
    if i < |inorder(t.left)| {
      assert k < t.key;
    } else if |inorder(t.left)| < i {
      assert t.key < k;
      GetInorder(t.right, i - |inorder(t.left)| - 1);
    } else {
      assert i == |inorder(t.left)|;
      assert k == t.key;
    }
  }

  lemma GetOfSubtree(root: trbtree, t: trbtree)
    requires SearchTree(root)
    requires Subtree(t, root)
    requires t.Node?
    ensures keys(t) <= keys(root)
    ensures Get(root, t.key) == t.value
  {
    if t.key < root.key {
      assert t.key in keys(root.left);
      assert Subtree(t, root.left);
      GetOfSubtree(root.left, t);
    } else if root.key < t.key {
      assert t.key in keys(root.right);
      assert Subtree(t, root.right);
      GetOfSubtree(root.right, t);
    } else {
    }
  }

  lemma SearchImpliesUnique(t: trbtree)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |inorder(t)| ::
      inorder(t)[i].0 != inorder(t)[j].0
  {
    SearchImpliesOrdered(t);
  }

/*
  lemma toMapLemmas(t: trbtree)
    requires SearchTree(t)
    ensures t.Node? ==>
      && toMap(t) == toMap(t.left) + toMap(t.right) + map[t.key := t.value]
      && toMap(t) == toMap(t.left) + map[t.key := t.value] + toMap(t.right)
  {}
*/

  lemma DisjointBranches(t: trbtree)
    requires SearchTree(t)
    requires t.Node?
    ensures t.key !in keys(t.left)
    ensures t.key !in keys(t.right)
    ensures keys(t.left) !! keys(t.right)
  {
    var k := t.key;
    var l := t.left;
    var r := t.right;
    assert forall m | m in keys(l) :: m < k;
    assert forall m | m in keys(r) :: k < m;
    assert forall p, q | p in keys(l) && q in keys(r) :: p < k < q;
    assert keys(l) !! keys(r);
  }

  lemma SizeKeys(t: trbtreeOrThread)
    requires SearchTree(t)
    ensures size(t) == |keys(t)|
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => {
        calc == {
          size(t);
          1 + size(l) + size(r);
          {
            SizeKeys(l);
            SizeKeys(r);
          }
          1 + |keys(l)| + |keys(r)|;
          |keys(l)| + |{k}| + |keys(r)|;
          {
            assert k !in keys(l);
            assert k !in keys(r);
            DisjointBranches(t);
            assert keys(l) !! keys(r);
          }
          |keys(l) + {k} + keys(r)|;
          |keys(t)|;
        }
      }
    }
  }

  lemma SizeSmaller(t: trbtreeOrThread, k: K)
    ensures sizeSmaller(t, k) <= size(t)
    ensures SearchTree(t) && k in keys(t) ==>
      sizeSmaller(t, k) < size(t)
  {
    if t.Node? {
      SizeSmaller(t.left, k);
      SizeSmaller(t.right, k);
      if SearchTree(t) && k in keys(t) {
        
        if t.key < k {
          calc {
            sizeSmaller(t, k);
            == 1 + size(t.left) + sizeSmaller(t.right, k);
            < 1 + size(t.left) + size(t.right);
            == size(t);
          }
        } else if k < t.key {
        } else {
        }
      }
    }
  }

  lemma SizeInorder(t: trbtreeOrThread)
    ensures size(t) == |inorder(t)|
  {}

  lemma SizeLemmas(t: trbtree)
    requires SearchTree(t)
    ensures size(t)
      == |inorder(t)|
      == |keys(t)|
      == |toMap(t).Keys|
      == |toMap(t)|
  {
    SizeInorder(t);
    SizeKeys(t);
    assert keys(t) == toMap(t).Keys;
    assert |toMap(t).Keys| == |toMap(t)|;
  }

/*
  lemma OrderKeysIsMapKeys(t: trbtree)
    requires SearchTree(t)
    ensures orderKeysToSet(inorder(t)) == toMap(t).Keys
  {
    OrderKeysIsTreeKeys(t);
  }

  lemma MapTreeEmpty(t: trbtree)
    requires SearchTree(t)
    ensures t.Empty? <==> toMap(t) == map[]
    ensures t.Node? <==> toMap(t) != map[]
  {
    if t.Empty? {
      assert toMap(t) == map[];
    } else {
      assert t.key in toMap(t).Keys;
      assert toMap(t) != map[];
    }
  }

  lemma MapTreeEmptyL(t: trbtree)
    requires SearchTree(t)
    ensures t.Empty? <== toMap(t) == map[]
    ensures t.Node? <== toMap(t) != map[]
  {
    MapTreeEmpty(t);
  }

  lemma SingletonSet<A>(s: set<A>, x: A)
    requires x in s
    requires forall y | y in s :: y == x
    ensures s == {x}
  {}

  lemma SingletonMapItems(k: K, v: V)
    ensures map[k := v].Items == {(k, v)}
  {
    assert forall p | p in map[k := v].Items :: p == (k, v);
    SingletonSet(map[k := v].Items, (k, v));
  }

  lemma OrderSetIsMapItems(t: trbtree)
    requires SearchTree(t)
    ensures orderToSet(inorder(t)) == toMap(t).Items
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => {
        OrderSetIsMapItems(l);
        OrderSetIsMapItems(r);
        assert orderToSet(inorder(l)) == toMap(l).Items;
        assert orderToSet(inorder(r)) == toMap(r).Items;
        toMapLemmas(t);
        calc == {
          toMap(t).Items;
          toMap(l).Items + map[k := v].Items + toMap(r).Items;
          {
            SingletonMapItems(k, v);
            assert map[k := v].Items == {(k, v)};
          }
          toMap(l).Items + {(k, v)} + toMap(r).Items;
          orderToSet(inorder(l)) + {(k, v)} + orderToSet(inorder(r));
          orderToSet(inorder(t));
        }
      }
    }
  }

  lemma HasPeekCondition(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    ensures st != [] <==> orderKeysToSet(traversed) < toMap(t).Keys
    //ensures st != [] <==> |traversed| < |toMap(t)|
  {
    if st != [] {
      SearchImpliesUnique(t);
      assert orderKeysToSet(traversed) <= orderKeysToSet(inorder(t));
      assert forall i | 0 <= i < |traversed| ::
        inorder(t)[i].0 == traversed[i].0;
      assert forall i | 0 <= i < |st| ::
         inorder(t)[|traversed| + i].0 == st[i].0;
      assert forall i, j | 0 <= i < |traversed| && 0 <= j < |st| ::
        traversed[i].0 != st[j].0;
      assert orderKeysToSet(traversed) !! orderKeysToSet(st);
      assert orderKeysToSet(st) != {} by {
        NonEmptyOrderKeysToSet(st);
      }
      assert orderKeysToSet(inorder(t)) == orderKeysToSet(traversed) + orderKeysToSet(st);
      assert orderKeysToSet(traversed) < orderKeysToSet(inorder(t));
      assert orderKeysToSet(inorder(t)) == toMap(t).Keys by {
        OrderKeysIsMapKeys(t);
      }
    } else {
      OrderKeysIsMapKeys(t);
    }
  }

  lemma HasPeekConditionCard(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    ensures st != [] <==> |traversed| < |toMap(t)|
  {
    HasPeekCondition(t, traversed, st);
    SizeLemmas(t);
  }

  lemma PeekInModel(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires st != []
    requires inorder(t) == traversed + st
    ensures st[0] in toMap(t).Items
  {
    OrderSetIsMapItems(t);
  }

  lemma IndexIn<A>(x: A, s: seq<A>) returns (i: nat)
    requires x in s
    ensures 0 <= i < |s|
    ensures s[i] == x
  {
    i :| 0 <= i < |s| && s[i] == x;
  }

  lemma PeekNotInTraversed(t: trbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires st != []
    requires inorder(t) == traversed + st
    ensures st[0] !in traversed
    ensures st[0].0 !in orderKeysToSeq(traversed)
    ensures st[0].0 !in orderKeysToSet(traversed)
  {
    SearchImpliesUnique(t);
    assert st[0] == inorder(t)[|traversed|];
    assert forall i | 0 <= i < |traversed| :: inorder(t)[i] != inorder(t)[|traversed|];
    if inorder(t)[|traversed|] in traversed {
      var i := IndexIn(inorder(t)[|traversed|], traversed);
      assert inorder(t)[i] != inorder(t)[|traversed|];
      assert false;
    }
    if inorder(t)[|traversed|].0 in orderKeysToSeq(traversed) {
      var i := IndexIn(inorder(t)[|traversed|].0, orderKeysToSeq(traversed));
      assert inorder(t)[i].0 != inorder(t)[|traversed|].0;
      assert false;
    }
    KeySetSeq(traversed);
  }

  lemma SubtreeChildren(node: trbtree, root: trbtree)
    requires node.Node?
    requires Subtree(node, root)
    ensures Subtree(node.left, root)
    ensures Subtree(node.right, root)
  {}
  */

  lemma InorderSmallerInorder(t: trbtreeOrThread, k: K)
    ensures |smallerInorder(t, k)| <= |inorder(t)|
    ensures smallerInorder(t, k) == inorder(t)[..|smallerInorder(t, k)|]
  {
    if t.Node? {
      InorderSmallerInorder(t.left, k);
      InorderSmallerInorder(t.right, k);
    }
  }

    /*
  lemma SmallerInorderIndex(t: trbtree, k: K, i: nat)
    requires SearchTree(t)
    requires i < |inorder(t)|
    requires inorder(t)[i].0 == k
    ensures i == |smallerInorder(t, k)|
  {
    assume false;
    SearchImpliesOrdered(t);
    SearchImpliesUnique(t);
    InorderSmallerInorder(t, k);
    assert forall j | 0 <= j < i < |inorder(t)| :: inorder(t)[j].0 < inorder(t)[i].0;
    assert forall j | 0 <= i < j < |inorder(t)| :: inorder(t)[i].0 < inorder(t)[j].0;
    //assert inorder(t)[|smallerInorder(t, k)|].0 == k;
    if t.Node? {
      if t.left.Child? && i < |inorder(t.left)| {
        SmallerInorderIndex(t.left.child, k, i);
        assert i == |smallerInorder(t.left.child, k)| == |smallerInorder(t, k)|;
      }
      if t.right.Child? && i > |inorder(t.left)| {
        SmallerInorderIndex(t.right.child, k, i - |inorder(t.left)| - 1);
      }
    }
  }
    */

  lemma SmallerInorderIndex(t: trbtree, k': K, i: nat)
    requires SearchTree(t)
    requires i < |inorder(t)|
    requires inorder(t)[i].0 == k'
    ensures i == |smallerInorder(t, k')|
  {
    SearchImpliesOrdered(t);
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        assert inorder(t)[|inorder(l)|].0 == k;
        if k < k' {
          //inorder(l) + [(k, v)] + smallerInorder(r, k')
          assert |inorder(l)| < i;
          SmallerInorderIndex(t.right, k', i - |inorder(l)| - 1);
        } else if k' < k {
          //smallerInorder(l, k')
          assert i < |inorder(l)|;
          SmallerInorderIndex(t.left, k', i);
        } else {
          //inorder(l)
          assert i == |inorder(l)|;
        }
      }
    }
  }

  /*
  lemma SmallerInorderRightInd(root: trbtree, node: trbtree)
    requires SearchTree(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.right.Node?
    ensures |smallerInorder(root, node.right.key)| <= |inorder(root)|
    ensures |smallerInorder(root, node.key)| <= |inorder(root)|
    ensures smallerInorder(root, node.right.key)
      == smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right.left);
  {
    SearchImpliesOrdered(root);
    if root == node {
      calc == {
        smallerInorder(root, node.right.key);
        smallerInorder(node, node.right.key);
        inorder(node.left) + [(node.key, node.value)] + smallerInorder(node.right, node.right.key);
        inorder(node.left) + [(node.key, node.value)] + inorder(node.right.left);
        smallerInorder(node, node.key) + [(node.key, node.value)] + inorder(node.right.left);
        smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right.left);
      }
    } else {
      match root {
        case Empty => {}
        case Node(l, k, v, r, c) => {
          if k < node.right.key {
            SmallerInorderRightInd(r, node);
            calc == {
              smallerInorder(root, node.right.key);
              inorder(l) + [(k, v)] + smallerInorder(r, node.right.key);
              inorder(l) + [(k, v)] + smallerInorder(r, node.key) + [(node.key, node.value)] + inorder(node.right.left);
              (inorder(l) + [(k, v)] + smallerInorder(r, node.key)) + [(node.key, node.value)] + inorder(node.right.left);
              { assert k < node.key; }
              smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right.left);
            }
          } else if node.right.key < k {
            SmallerInorderRightInd(root.left, node);
          } else {
          }
        }
      }
    }
  }

  lemma SmallerInorderLeftInd(root: trbtree, node: trbtree)
    requires SearchTree(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.left.Node?
    ensures |smallerInorder(root, node.left.key)| <= |inorder(root)|
    ensures |smallerInorder(root, node.key)| <= |inorder(root)|
    ensures smallerInorder(root, node.key)
      == smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
  {
    SearchImpliesOrdered(root);
    if root == node {
      calc == {
        smallerInorder(root, node.key);
        smallerInorder(node, node.key);
        inorder(node.left);
        inorder(node.left.left) + [(node.left.key, node.left.value)] + inorder(node.left.right);
        smallerInorder(node.left, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
        smallerInorder(node, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
        smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
      }
    } else {
      match root {
        case Empty => {}
        case Node(l, k, v, r, c) => {
          if k < node.left.key {
            SmallerInorderLeftInd(r, node);
            calc == {
              smallerInorder(root, node.key);
              { assert root.key < node.key; }
              inorder(l) + [(k, v)] + smallerInorder(r, node.key);
              inorder(l) + [(k, v)] + (smallerInorder(r, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right));
              inorder(l) + [(k, v)] + smallerInorder(r, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
              smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right);
            }
          } else if node.left.key < k {
            SmallerInorderLeftInd(root.left, node);
          } else {
          }
        }
      }
    }
  }
  */

  lemma InorderOfSmallerInorderSize(t: trbtree, k: K)
    requires SearchTree(t)
    requires k in keys(t)
    ensures |smallerInorder(t, k)| < |inorder(t)|
    ensures inorder(t)[|smallerInorder(t, k)|].0 == k
  {
    SearchImpliesOrdered(t);
    if t.Node? {
      if t.key < k {
        //inorder(l) + [(t.key, v)] + smallerInorder(r, k)
        InorderOfSmallerInorderSize(t.right, k);
      } else if k < t.key {
        //smallerInorder(l, k)
        InorderOfSmallerInorderSize(t.left, k);
      } else {
        //inorder(l)
      }
    }
  }

  lemma SmallerInorderSize(t: trbtreeOrThread, k: K)
    requires SearchTree(t)
    ensures |smallerInorder(t, k)| == sizeSmaller(t, k)
  {
    if t.Node? {
      SizeInorder(t.left);
      SmallerInorderSize(t.left, k);
      SmallerInorderSize(t.right, k);
    }
  }

  lemma SubtreeChildren(a: trbtree, b: trbtree)
    requires a.Node?
    requires Subtree(a, b)
    ensures !a.left.Thread? ==> Subtree(a.left, b)
    ensures !a.right.Thread? ==> Subtree(a.right, b)
  {
    if a == b {
    } else {
      if Subtree(a, b.left) {
        SubtreeChildren(a, b.left);
      } else if Subtree(a, b.right) {
        SubtreeChildren(a, b.right);
      } else {
        assert false;
      }
    }
  }

  lemma SubtreeTrans(a: trbtree, b: trbtree, c: trbtree)
    requires Subtree(a, b)
    requires Subtree(b, c)
    ensures Subtree(a, c)
  {
    if a == b {
    } else {
      if Subtree(a, b.left) {
        assert Subtree(a, b.left);
        assert Subtree(b.left, c) by {
          SubtreeChildren(b, c);
        }
        SubtreeTrans(a, b.left, c);
      } else if Subtree(a, b.right) {
        SubtreeChildren(b, c);
        SubtreeTrans(a, b.right, c);
      } else {
        assert false;
      }
    }
  }

  /* Threaded Tree */

  type threadOrEmpty = t: trbtreeOrThread | t.Thread? || t.Empty? witness Empty

  function IsThreadOrEmpty(t: trbtreeOrThread): bool
  {
    t.Thread? || t.Empty?
  }

  function ForgetThread(t: trbtreeOrThread): trbtree
  {
    match t
    case Thread(_) => Empty()
    case _ => t
  }

/*
  function ThreadedTreeRec(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, onLeft: bool): bool
    ensures p.Child? && !p.child.Empty? ==>
      (ThreadedTreeRec(prev, p, next, onLeft) <==> ThreadedTreeRec(prev, p.child, next))
    decreases p
  {
    match p {
      case Child(Empty) =>
        if onLeft then
          prev.Child? && prev.child.Empty?
        else
          next.Child? && next.child.Empty?
      case Child(t) =>
        ThreadedTreeRec(prev, t, next)
      case Thread(k) =>
        if onLeft then
          prev.Thread? && prev.thread == k
        else
          next.Thread? && next.thread == k
    }
  }

  function ThreadedTreeRec(prev: threadOrEmpty, t: trbtree, next: threadOrEmpty): bool
    decreases t
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRec(prev, l, Thread(k), true)
        && ThreadedTreeRec(Thread(k), r, next, false)
    }
  }
  */

  function ThreadedTreeRecL(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty): bool
    decreases t, 1
  {
    match t {
      case Empty => prev.Empty?
      case Thread(k) => prev.Thread? && prev.thread == k
      //case Node(_, _, _, _, _) => ThreadedTreeNe(prev, t, next)
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRecL(prev, l, Thread(k))
        && ThreadedTreeRecR(Thread(k), r, next)
    }
  }

  function ThreadedTreeRecR(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty): bool
    decreases t, 1
  {
    match t {
      case Empty => next.Empty?
      case Thread(k) => next.Thread? && next.thread == k
      //case Node(_, _, _, _, _) => ThreadedTreeNe(prev, t, next)
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRecL(prev, l, Thread(k))
        && ThreadedTreeRecR(Thread(k), r, next)
    }
  }

  function ThreadedTreeRecCond(
      prev: threadOrEmpty,
      p: trbtreeOrThread,
      next: threadOrEmpty,
      isLeft: bool
    ): bool
  {
    if isLeft then
      ThreadedTreeRecL(prev, p, next)
    else
      ThreadedTreeRecR(prev, p, next)
  }

  function ThreadedTreeNe(prev: threadOrEmpty, t: netrbtree, next: threadOrEmpty): bool
    decreases t, 0
  {
    match t {
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRecL(prev, l, Thread(k))
        && ThreadedTreeRecR(Thread(k), r, next)
    }
  }

  function ThreadedTreeRoot(t: trbtree): bool
  {
    t.Empty? || ThreadedTreeNe(Empty, t, Empty)
  }

  lemma ThreadedKeysRecL(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty)
    decreases size(t), 1
    requires ThreadedTreeRecL(prev, t, next)
    requires !IsThreadOrEmpty(t)
    ensures keysAndThreads(t)
      == keys(t)
      + (if prev.Thread? then {prev.thread} else {})
      + (if next.Thread? then {next.thread} else {})
  {
    ThreadedKeysNe(prev, t, next);
  }

  lemma ThreadedKeysRecR(prev: threadOrEmpty, t: trbtreeOrThread, next: threadOrEmpty)
    decreases size(t), 1
    requires ThreadedTreeRecR(prev, t, next)
    requires !IsThreadOrEmpty(t)
    ensures keysAndThreads(t)
      == keys(t)
      + (if prev.Thread? then {prev.thread} else {})
      + (if next.Thread? then {next.thread} else {})
  {
    ThreadedKeysNe(prev, t, next);
  }

  lemma ThreadedKeysNe(prev: threadOrEmpty, t: netrbtree, next: threadOrEmpty)
    decreases size(t), 0
    requires ThreadedTreeNe(prev, t, next)
    ensures keysAndThreads(t)
      == keys(t)
      + (if prev.Thread? then {prev.thread} else {})
      + (if next.Thread? then {next.thread} else {})
  {
    if !IsThreadOrEmpty(t.left) {
      ThreadedKeysRecL(prev, t.left, Thread(t.key));
    }
    if !IsThreadOrEmpty(t.right) {
      ThreadedKeysRecR(Thread(t.key), t.right, next);
    }
  }

  lemma ThreadedKeys(t: trbtree)
    requires ThreadedTreeRoot(t)
    ensures keys(t) == keysAndThreads(t)
  {
    if t.Node? {
      ThreadedKeysNe(Empty, t, Empty);
    }
  }

  lemma SmallerKeys(t: trbtreeOrThread, k': K)
    requires SearchTree(t)
    ensures smallerKeys(t, k') == set k | k in keys(t) && k < k'
  {
    match t {
      case Empty => {
      }
      case Thread(_) => {
      }
      case Node(l, k, v, r, c) =>
        if k < k' {
          SmallerKeys(r, k');
        } else if k' < k {
          SmallerKeys(l, k');
        } else {
        }
    }
  }

/*
  lemma SmallerKeysLeft(t: trbtree)
    requires SearchTree(t)
    requires t.Node?
    requires t.left.Child?
    ensures smallerKeys(t, t.key) == keys(t.left.child)
  {
    SmallerKeys(t, t.key);
  }

  lemma RightThreadIsBiggerRec(node: trbtree, prev: threadOrEmpty, root: trbtree, next: threadOrEmpty)
    decreases root
    requires SearchTree(root)
    requires root.Node?
    requires ThreadedTreeRec(prev, root, next)
    requires Subtree(node, root)
    requires next.Thread? ==> forall k | k in keys(root) :: k < next.thread
    requires node.Node?
    requires node.right.Thread?
    ensures node.key < node.right.thread
  {
    if node.key < root.key {
      if root.left.Child? {
        RightThreadIsBiggerRec(node, prev, root.left.child, Thread(root.key));
      }
    } else if root.key < node.key {
      if root.right.Child? {
        RightThreadIsBiggerRec(node, Thread(root.key), root.right.child, next);
      }
    } else {
      assert node == root;
    }
  }

  lemma RightThreadIsBiggerRoot(node: trbtree, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.right.Thread?
    ensures node.key < node.right.thread
  {
    RightThreadIsBiggerRec(node, Child(Empty), root, Child(Empty));
  }

  lemma ThreadedInorderRec(it: trbtree, left: seq<(K, V)>, right: seq<(K, V)>, prev: threadOrEmpty, node: trbtree, next: threadOrEmpty, root: trbtree)
      returns (i: nat)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires ThreadedTreeRec(prev, node, next)
    requires Subtree(it, node)
    requires it.Node?
    requires it.right.Thread?

    requires prev.Thread? ==> left != [] && left[|left|-1].0 == prev.thread
    requires next.Thread? ==> right != [] && right[0].0 == next.thread
    requires inorder(root) == left + inorder(node) + right

    ensures i+1 < |inorder(root)|
    ensures inorder(root)[i].0 == it.key
    ensures inorder(root)[i+1].0 == it.right.thread
  {
    if it.key < node.key {
      if node.left.Child? {
        i := ThreadedInorderRec(it, left, [(node.key, node.value)] + inorder(node.right) + right, prev, node.left.child, Thread(node.key), root);
      }
    } else if node.key < it.key {
      if node.right.Child? {
        i := ThreadedInorderRec(it, left + inorder(node.left) + [(node.key, node.value)], right, Thread(node.key), node.right.child, next, root);
      }
    } else {
      assert node == it;
      i := |left| + |inorder(node.left)|;
    }
  }

  lemma ThreadedInorderRoot(it: trbtree, root: trbtree)
      returns (i: nat)
    requires SearchTree(root)
    requires root.Node?
    requires ThreadedTreeRoot(root)
    requires Subtree(it, root)
    requires it.Node?
    requires it.right.Thread?

    ensures i+1 < |inorder(root)|
    ensures inorder(root)[i].0 == it.key
    ensures inorder(root)[i+1].0 == it.right.thread
  {
    i := ThreadedInorderRec(it, [], [], Child(Empty), root, Child(Empty), root);
  }

  lemma SmallerKeysRightThread(node: trbtree, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.right.Thread?
    ensures smallerKeys(root, node.right.thread)
      == smallerKeys(root, node.key) + {node.key}
  {
    var i := ThreadedInorderRoot(node, root);
    calc == {
      smallerKeys(root, node.right.thread);
      { SmallerOrderKeysIsTreeKeys(root, node.right.thread); }
      orderKeysToSet(smallerInorder(root, node.right.thread));
      {
        InorderSmallerInorder(root, node.right.thread);
        SmallerInorderIndex(root, node.right.thread, i+1);
      }
      orderKeysToSet(inorder(root)[..i+1]);
      orderKeysToSet(inorder(root)[..i] + [inorder(root)[i]]);
      orderKeysToSet(inorder(root)[..i]) + orderKeysToSet([inorder(root)[i]]);
      orderKeysToSet(inorder(root)[..i]) + {inorder(root)[i].0};
      orderKeysToSet(inorder(root)[..i]) + {node.key};
      {
        InorderSmallerInorder(root, node.key);
        SmallerInorderIndex(root, node.key, i);
      }
      orderKeysToSet(smallerInorder(root, node.key)) + {node.key};
      { SmallerOrderKeysIsTreeKeys(root, node.key); }
      smallerKeys(root, node.key) + {node.key};
    }
  }

  lemma MinInorderRec(it: trbtree, left: seq<(K, V)>, right: seq<(K, V)>, node: trbtree, root: trbtree)
      returns (i: nat)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires Subtree(it, node)
    requires it.Node?
    requires it.right.Child?
    requires it.right.child.Node?

    requires inorder(root) == left + inorder(node) + right

    ensures i+1 < |inorder(root)|
    ensures inorder(root)[i].0 == it.key
    ensures inorder(root)[i+1].0 == minSubtree(it.right).key
  {
    if it.key < node.key {
      if node.left.Child? {
        i := MinInorderRec(it, left, [(node.key, node.value)] + inorder(node.right) + right, node.left.child, root);
      }
    } else if node.key < it.key {
      if node.right.Child? {
        i := MinInorderRec(it, left + inorder(node.left) + [(node.key, node.value)], right, node.right.child, root);
      }
    } else {
      assert node == it;
      i := |left| + |inorder(node.left)|;
    }
  }

  lemma MinInorderRoot(it: trbtree, root: trbtree)
      returns (i: nat)
    requires SearchTree(root)
    requires root.Node?
    requires Subtree(it, root)
    requires it.Node?
    requires it.right.Child?
    requires it.right.child.Node?

    ensures i+1 < |inorder(root)|
    ensures inorder(root)[i].0 == it.key
    ensures inorder(root)[i+1].0 == minSubtree(it.right).key
  {
    i := MinInorderRec(it, [], [], root, root);
  }

  lemma SmallerKeysMin(node: trbtree, root: trbtree)
    requires SearchTree(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.right.Child?
    requires node.right.child.Node?
    ensures smallerKeys(root, minSubtree(node.right).key)
      == smallerKeys(root, node.key) + {node.key}
  {
    var i := MinInorderRoot(node, root);
    calc == {
      smallerKeys(root, minSubtree(node.right).key);
      { SmallerOrderKeysIsTreeKeys(root, minSubtree(node.right).key); }
      orderKeysToSet(smallerInorder(root, minSubtree(node.right).key));
      {
        InorderSmallerInorder(root, minSubtree(node.right).key);
        SmallerInorderIndex(root, minSubtree(node.right).key, i+1);
      }
      orderKeysToSet(inorder(root)[..i+1]);
      orderKeysToSet(inorder(root)[..i] + [inorder(root)[i]]);
      orderKeysToSet(inorder(root)[..i]) + orderKeysToSet([inorder(root)[i]]);
      orderKeysToSet(inorder(root)[..i]) + {inorder(root)[i].0};
      orderKeysToSet(inorder(root)[..i]) + {node.key};
      {
        InorderSmallerInorder(root, node.key);
        SmallerInorderIndex(root, node.key, i);
      }
      orderKeysToSet(smallerInorder(root, node.key)) + {node.key};
      { SmallerOrderKeysIsTreeKeys(root, node.key); }
      smallerKeys(root, node.key) + {node.key};
    }
  }

  lemma SubtreeLeftEmpty(it: trbtree, prev: threadOrEmpty, node: trbtree, next: threadOrEmpty)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires next.Thread?
    requires ThreadedTreeRec(prev, node, next)
    requires Subtree(it, node)
    requires it.Node?
    ensures it.right != Child(Empty)
  {
    if Subtree(it, node.left) && node.left.Child? && node.left.child.Node? {
      SubtreeLeftEmpty(it, prev, node.left.child, Thread(node.key));
    }
    if Subtree(it, node.right) && node.right.Child? && node.right.child.Node? {
      SubtreeLeftEmpty(it, Thread(node.key), node.right.child, next);
    }
  }

  lemma SubtreeRightEmpty(it: trbtree, prev: threadOrEmpty, node: trbtree)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires ThreadedTreeRec(prev, node, Child(Empty))
    requires Subtree(it, node)
    requires it.Node?
    requires it.right.Child?
    requires it.right.child.Empty?

    ensures it == node || Subtree(it, node.right)
  {
    assert !Subtree(it, node.left) by {
      if Subtree(it, node.left) {
        SubtreeLeftEmpty(it, prev, node.left.child, Thread(node.key));
        assert false;
      }
    }
    if node.right.Child? && node.right.child.Node? {
      SubtreeRightEmpty(it, Thread(node.key), node.right.child);
    }
  }

  lemma InorderRightEmptyRec(it: trbtree, prev: threadOrEmpty, node: trbtree)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires ThreadedTreeRec(prev, node, Child(Empty))
    requires Subtree(it, node)
    requires it.Node?
    requires it.right.Child?
    requires it.right.child.Empty?

    ensures inorder(node)[|inorder(node)|-1].0 == it.key
  {
    assert node.right.Child?;
    assert it == node || Subtree(it, node.right.child) by {
      SubtreeRightEmpty(it, prev, node);
    }
    if node.right.child.Empty? {
      assert it == node;
    } else {
      InorderRightEmptyRec(it, Thread(node.key), node.right.child);
    }
  }

  lemma InorderRightEmptyRoot(it: trbtree, node: trbtree)
    decreases node

    requires SearchTree(node)
    requires node.Node?
    requires ThreadedTreeRoot(node)
    requires Subtree(it, node)
    requires it.Node?
    requires it.right.Child?
    requires it.right.child.Empty?

    ensures inorder(node)[|inorder(node)|-1].0 == it.key
  {
    InorderRightEmptyRec(it, Child(Empty), node);
  }

  lemma {:verify false} SmallerKeysRightEmpty(node: trbtree, root: trbtree)
    requires SearchTree(root)
    requires Subtree(node, root)
    requires ThreadedTreeRoot(root)
    requires node.Node?
    requires node.right.Child?
    requires node.right.child.Empty?
    ensures keys(root) == smallerKeys(root, node.key) + {node.key}
  {
    calc == {
      keys(root);
      { OrderKeysIsTreeKeys(root); }
      orderKeysToSet(inorder(root));
      {
        assert forall s: seq<(K, V)> | s != [] :: s == s[..|s|-1] + [s[|s|-1]];
        assert inorder(root) == inorder(root)[..|inorder(root)|-1] + [inorder(root)[|inorder(root)|-1]];
        assert forall a, b: seq<(K, V)> | a == b :: orderKeysToSet(a) == orderKeysToSet(b);
      }
      orderKeysToSet(inorder(root)[..|inorder(root)|-1] + [inorder(root)[|inorder(root)|-1]]);
      orderKeysToSet(inorder(root)[..|inorder(root)|-1]) + orderKeysToSet([inorder(root)[|inorder(root)|-1]]);
      orderKeysToSet(inorder(root)[..|inorder(root)|-1]) + {inorder(root)[|inorder(root)|-1].0};
      { InorderRightEmptyRoot(node, root); }
      orderKeysToSet(inorder(root)[..|inorder(root)|-1]) + {node.key};
      {
        InorderSmallerInorder(root, node.key);
        InorderRightEmptyRoot(node, root);
        SmallerInorderIndex(root, node.key, |inorder(root)|-1);
      }
      orderKeysToSet(smallerInorder(root, node.key)) + {node.key};
      { SmallerOrderKeysIsTreeKeys(root, node.key); }
      smallerKeys(root, node.key) + {node.key};
    }
  }
  */

  function ThreadedTreeExample1(): trbtree {
    Node(
      Node(
        Node((Empty), 1, 0, Thread(2), Black),
        2,
        0,
        Node(Thread(2), 3, 0, Thread(4), Black),
        Black
      ),
      4,
      0,
      Node(
        Node(Thread(4), 5, 0, Thread(6), Black),
        6,
        0,
        Node(Thread(6), 7, 0, (Empty), Black),
        Black
      ),
      Black
    )
  }

  lemma ThreadedExamples()
    ensures ThreadedTreeRoot(ThreadedTreeExample1())
  {}

  /* Red Black Tree */

  function isRed(t: trbtreeOrThread): bool
  {
    t.Node? && t.color.Red?
  }

  function isBlack(t: trbtreeOrThread): bool
  {
    t.Node? && t.color.Black?
  }

  function BlackenRoot(t: trbtree): trbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) => Node(l, k, v, r, Black)
    }
  }

  function ConditionalReddenRoot(t: trbtree): trbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) =>
        if isRed(l) then
          Node(l, k, v, r, c)
        else
          Node(l, k, v, r, Red)
    }
  }

  function BlackHeight(t: trbtreeOrThread): nat
  {
    match t {
      case Empty => 0
      case Thread(_) => 0
      case Node(l, k, v, r, c) =>
        if c.Black? then
          1 + Utils.max(BlackHeight(l), BlackHeight(r))
        else
          Utils.max(BlackHeight(l), BlackHeight(r))
    }
  }

  function RedBlackTree(t: trbtreeOrThread): bool
  {
    match t {
      case Empty => true
      case Thread(_) => true
      case Node(l, k, v, r, c) =>
        // Red links lean left:
        && (r.Node? ==> r.color.Black?)
        // No node has two red links connected to it:
        && (isRed(l) && l.left.Node? ==> l.left.color.Black?)
        // Perfect black balance:
        && BlackHeight(l) == BlackHeight(r)

        && RedBlackTree(l)
        && RedBlackTree(r)
    }
  }

  function RedBlackTreeRoot(t: trbtree): bool
  {
    RedBlackTree(t) && (t.Node? ==> t.color.Black?)
  }
}
