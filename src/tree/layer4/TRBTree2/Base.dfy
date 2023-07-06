include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer1/OrderedSetUtils.dfy"

module TRBTree.Base {
  import opened Utils
  import opened KeyValue
  import opened Color
  import opened OrderedSetUtils

  datatype rbtree
    = Empty
    | Thread(K)
    | Node(left: rbtree, key: K, value: V, right: rbtree, color: Color)

  function method fromThread(t: rbtree): K
    requires t.Thread?
  {
    match t {
      case Thread(k) => k
    }
  }

  function method keys(t: rbtree): set<K>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => keys(l) + {k} + keys(r)
    }
  }

  function method values(t: rbtree): set<V>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => values(l) + {v} + values(r)
    }
  }

  function method pairs(t: rbtree): set<(K, V)>
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => pairs(l) + {(k, v)} + pairs(r)
    }
  }

  function method size(t: rbtree): nat
  {
    match t {
      case Empty => 0
      case Thread(_) => 0
      case Node(l, k, v, r, c) => 1 + size(l) + size(r)
    }
  }

  /*
  function method toMapRec(t: rbtree): map<K, V>
  {
    match t {
      case Empty => map[]
      case Node(l, k, v, r, c) => toMapRec(l) + toMapRec(r) + map[k := v]
    }
  }
  */

  function method preorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(l, k, v, r, c) =>  [(k, v)] + preorder(l) + preorder(r)
    }
  }

  function method inorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(l, k, v, r, c) => inorder(l) + [(k, v)] + inorder(r)
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

  function method orderToMap(s: seq<(K, V)>): map<K, V>
  {
    if s == [] then
      map[]
    else
      map[s[0].0 := s[0].1] + orderToMap(s[1..])
  }

  function method orderToMap'(s: seq<(K, V)>): map<K, V>
    requires forall i, j | 0 <= i < j < |s| :: s[i].0 != s[j].0
  {
    map t: (K, V) | t in s :: t.0 := t.1
    //map i: int | 0 <= i < |s| :: s[i].0 := s[i].1
  }

  function method toMapSeq(t: rbtree): map<K, V>
  {
    orderToMap(preorder(t))
  }

  function method SearchTree(t: rbtree): bool
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

  function method Get(t: rbtree, k: K): V
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

  function method toMap(t: rbtree): map<K, V>
    requires SearchTree(t)
  {
    map k: K | k in keys(t) :: Get(t, k)
  }

  predicate Subtree(node: rbtree, root: rbtree)
    //ensures Subtree(node, root) ==> keys(node) <= keys(root)
    //ensures Subtree(node, root) && SearchTree(root) ==> SearchTree(node)
  {
    || root == node
    || (
      && root.Node?
      && (Subtree(node, root.left) || Subtree(node, root.right)))
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

  lemma orderToSetCard(s: seq<(K, V)>)
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

  lemma OrderKeysIsTreeKeys(t: rbtree)
    ensures orderKeysToSet(inorder(t)) == keys(t)
  {}

  lemma OrderSetIsTreePairs(t: rbtree)
    ensures orderToSet(inorder(t)) == pairs(t)
  {}

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

  lemma KeyInOrder(t: rbtree, k': K)
    requires k' in keys(t)
    ensures exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k'
  {
    match t {
      case Empty => {}
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

  lemma ForallKeyInOrder(t: rbtree)
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

  lemma OrderInKeysAndValues(t: rbtree)
    ensures forall i | 0 <= i < |inorder(t)| ::
      && inorder(t)[i].0 in keys(t)
      && inorder(t)[i].1 in values(t)
  {}

  lemma KeySetIsOrderKeysR(t: rbtree, P: K -> bool)
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

  lemma KeySetIsOrderKeys(t: rbtree, P: K -> bool)
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

  lemma SearchImpliesOrdered(t: rbtree)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |inorder(t)| ::
      inorder(t)[i].0 < inorder(t)[j].0
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
      case Node(l, k, v, r, c) => {
        KeySetIsOrderKeysR(l, m => m < k);
        KeySetIsOrderKeysR(r, m => k < m);
      }
    }
  }

  lemma GetInorder(t: rbtree, i: nat)
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

  lemma SearchImpliesUnique(t: rbtree)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |inorder(t)| ::
      inorder(t)[i].0 != inorder(t)[j].0
  {
    SearchImpliesOrdered(t);
  }

  lemma DisjointBranches(t: rbtree)
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

  lemma SizeKeys(t: rbtree)
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

  lemma SizeInorder(t: rbtree)
    requires SearchTree(t)
    ensures size(t) == |inorder(t)|
  {}

  lemma toMapLemmas(t: rbtree)
    requires SearchTree(t)
    ensures t.Node? ==>
      && toMap(t) == toMap(t.left) + toMap(t.right) + map[t.key := t.value]
      && toMap(t) == toMap(t.left) + map[t.key := t.value] + toMap(t.right)
  {}

  lemma SizeLemmas(t: rbtree)
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

  lemma OrderKeysIsMapKeys(t: rbtree)
    requires SearchTree(t)
    ensures orderKeysToSet(inorder(t)) == toMap(t).Keys
  {
    OrderKeysIsTreeKeys(t);
  }

  lemma MapTreeEmpty(t: rbtree)
    requires SearchTree(t)
    ensures t.Empty? || t.Thread? <==> toMap(t) == map[]
    ensures t.Node? <==> toMap(t) != map[]
  {
    if t.Empty? {
      assert toMap(t) == map[];
    } else if t.Thread? {
      assert toMap(t) == map[];
    } else {
      assert t.key in toMap(t).Keys;
      assert toMap(t) != map[];
    }
  }

  lemma MapTreeEmptyL(t: rbtree)
    requires SearchTree(t)
    ensures t.Empty? || t.Thread? <== toMap(t) == map[]
    ensures t.Node? <== toMap(t) != map[]
  {
    MapTreeEmpty(t);
  }

  lemma ElemthInorder0(t: rbtree)
    requires SearchTree(t)
    requires keys(t) != {} || t.Node?
    ensures elemth(toMap(t).Keys, 0) == inorder(t)[0].0
  {
    assert elemth(toMap(t).Keys, 0) == minimum(toMap(t).Keys);
    SearchImpliesOrdered(t);
    var s := inorder(t);
    assert forall x | x in s :: s[0].0 <= x.0;
    assert forall x | x in orderKeysToSet(s) :: s[0].0 <= x;
    OrderKeysIsTreeKeys(t);
    assert orderKeysToSet(s) == toMap(t).Keys;
    if minimum(toMap(t).Keys) != s[0].0 {
      assert s[0].0 in toMap(t).Keys;
      lmin(toMap(t).Keys, s[0].0);
      assert minimum(toMap(t).Keys) <= s[0].0;

      assert minimum(toMap(t).Keys) in orderKeysToSet(s);
      assert s[0].0 <= minimum(toMap(t).Keys);

      assert minimum(toMap(t).Keys) < s[0].0;
      assert s[0].0 < minimum(toMap(t).Keys);

      assert false;
    }
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

  lemma OrderSetIsMapItems(t: rbtree)
    requires SearchTree(t)
    ensures orderToSet(inorder(t)) == toMap(t).Items
  {
    match t {
      case Empty => {}
      case Thread(_) => {}
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

  lemma HasPeekCondition(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
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

  lemma HasPeekConditionCard(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
    requires SearchTree(t)
    requires inorder(t) == traversed + st
    ensures st != [] <==> |traversed| < |toMap(t)|
  {
    HasPeekCondition(t, traversed, st);
    SizeLemmas(t);
  }

  lemma PeekInModel(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
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

  lemma PeekNotInTraversed(t: rbtree, traversed: seq<(K, V)>, st: seq<(K, V)>)
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

  lemma SubtreeChildren(node: rbtree, root: rbtree)
    requires node.Node?
    requires Subtree(node, root)
    ensures Subtree(node.left, root)
    ensures Subtree(node.right, root)
  {}

  datatype option<A> = Some(A) | Nothing

  function method fromSome<A>(ox: option<A>): A
    requires ox.Some?
  {
    match ox {
      case Some(x) => x
    }
  }

  function method threadedInorder(t: rbtree): seq<(option<K>, K, V, option<K>)>
  {
    match t {
      case Empty => []
      case Thread(_) => []
      case Node(Thread(lt), k, v, Thread(rt), c) =>
        [(Some(lt), k, v, Some(rt))]
      case Node(Thread(lt), k, v, r, c) =>
        [(Some(lt), k, v, Nothing)] + threadedInorder(r)
      case Node(l, k, v, Thread(rt), c) =>
        threadedInorder(l) + [(Nothing, k, v, Some(rt))]
      case Node(l, k, v, r, c) =>
        threadedInorder(l) + [(Nothing, k, v, Nothing)] + threadedInorder(r)
    }
  }

  function method ThreadedTreeRec(t: rbtree): bool
  {
    var s := threadedInorder(t);
    && (forall i | 0 <= i < |s|-1 ::
      && (s[i].0.Some? ==> fromSome(s[i].0) == s[i+1].1)
      && (s[i+1].3.Some? ==> fromSome(s[i+1].3) == s[i].1)
    )
  }

  function method ThreadedTreeRoot(t: rbtree): bool
  {
    var s := threadedInorder(t);
    && ThreadedTreeRec(t)
    && (s != [] ==> s[0].0.Nothing? && s[|s|-1].3.Nothing?)
  }

  function method treeToThread(t: rbtree): option<K>
    requires !t.Node?
  {
    match t {
      case Empty => Nothing
      case Thread(k) => Some(k)
    }
  }

  function method threads(t: rbtree): (option<K>, option<K>)
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        ( if l.Node? then
            threads(l).0
          else
            treeToThread(l)
        , if r.Node? then
            threads(r).1
          else
            treeToThread(r)
        )
    }
  }

  function method ThreadedTreeRec'(lt: option<K>, t: rbtree, rt: option<K>): bool
    decreases t
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        && (
          if l.Node? then
            ThreadedTreeRec'(lt, l, Some(k))
          else
            treeToThread(l) == lt
        )
        && (
          if r.Node? then
            ThreadedTreeRec'(Some(k), r, rt)
          else
            treeToThread(r) == rt
        )
    }
  }

  function method ThreadedTreeRoot'(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Thread(_) => false
      case Node(_, _, _, _, _) => ThreadedTreeRec'(Nothing, t, Nothing)
    }
  }

  lemma EqThreadedDefs(lt: option<K>, t: rbtree, rt: option<K>)
    decreases t
    requires t.Node?
    ensures ThreadedTreeRec(t) && threads(t) == (lt, rt) <==> ThreadedTreeRec'(lt, t, rt)
  {
    match t {
      case Node(l, k, v, r, c) => {
        if l.Node? {
          EqThreadedDefs(lt, l, Some(k));
        } else {
        }
        if r.Node? {
          EqThreadedDefs(Some(k), r, rt);
          assert ThreadedTreeRec(r) && threads(r) == (Some(k), rt) <==> ThreadedTreeRec'(Some(k), r, rt);
          if ThreadedTreeRec(t) && threads(t) == (lt, rt) {
            assume false;
            assert ThreadedTreeRec(r) && threads(r) == (Some(k), rt);
            assert ThreadedTreeRec'(Some(k), r, rt);
          }
          if ThreadedTreeRec'(lt, t, rt) {
            assert ThreadedTreeRec'(Some(k), r, rt);
            assert ThreadedTreeRec(r) && threads(r) == (Some(k), rt);
            assert threads(t) == (lt, rt);
            assume false;
            assert ThreadedTreeRec(t);
          }
        } else {
          assume false;
          if ThreadedTreeRec'(lt, t, rt) {
            assert ThreadedTreeRec(t);
          }
        }
      }
    }
  }

  /*
  function method ThreadedTreeRec(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Thread(_) => true
      case Node(l, k, v, r, c) => true
        //threadedInorder(l) + [(Nothing, k, v, Nothing)] + threadedInorder(r)
    }
  }
  */

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
      case Thread(_) => 0
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
      case Thread(_) => true
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
