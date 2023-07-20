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
    | Node(left: pointer, key: K, value: V, right: pointer, color: Color)

  datatype pointer = Child(child: rbtree) | Thread(thread: K)

/*
  datatype option<A> = Some(A) | Nothing

  function method fromSome<A>(ox: option<A>): A
    requires ox.Some?
  {
    match ox {
      case Some(x) => x
    }
  }
 
  function method optionTo(oP: option<K>): pointer
  {
    match o {
      case Nothing => Child(Empty())
      case Some(k) => Thread(k)
    }
  }
  */

  function method applyToChild<A>(p: pointer, f: rbtree -> A, d: A): A
  {
    match p {
      case Child(t) => f(t)
      case Thread(_) => d
    }
  }

  function method keysP(p: pointer): set<K>
    ensures p.Child? ==> keys(p.child) == keysP(p)
  {
    match p {
      case Child(t) => keys(t)
      case Thread(_) => {}
    }
  }

  function method keys(t: rbtree): set<K>
    ensures t.Node? ==>
      keys(t) == keysP(t.left) + {t.key} + keysP(t.right)
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => keysP(l) + {k} + keysP(r)
    }
  }
  
  function method keysAndThreadsP(p: pointer): set<K>
    ensures p.Child? ==> keysAndThreads(p.child) == keysAndThreadsP(p)
  {
    match p {
      case Child(t) => keysAndThreads(t)
      case Thread(k) => {k}
    }
  }

  function method keysAndThreads(t: rbtree): set<K>
    ensures t.Node? ==>
      keysAndThreads(t) == keysAndThreadsP(t.left) + {t.key} + keysAndThreadsP(t.right)
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => keysAndThreadsP(l) + {k} + keysAndThreadsP(r)
    }
  }
  
  lemma KeysLemmasAll()
    ensures forall p: pointer | p.Child? ::
      && (keys(p.child) == keysP(p))
      && (p.child.Node? && p.child.left.Child? && p.child.right.Child? ==>
        keys(p.child) == keys(p.child.left.child) + {p.child.key} + keys(p.child.right.child))
      && (p.child.Node? && p.child.left.Child? && p.child.right.Thread? ==>
        keys(p.child) == keys(p.child.left.child) + {p.child.key})
      && (p.child.Node? && p.child.left.Thread? && p.child.right.Child? ==>
        keys(p.child) == {p.child.key} + keys(p.child.right.child))
      && (p.child.Node? && p.child.left.Thread? && p.child.right.Thread? ==>
        keys(p.child) == {p.child.key})
    ensures forall t: rbtree | t.Node? ::
      && (t.left.Child? && t.right.Child? ==>
        keys(t) == keys(t.left.child) + {t.key} + keys(t.right.child))
      && (t.left.Child? && t.right.Thread? ==>
        keys(t) == keys(t.left.child) + {t.key})
      && (t.left.Thread? && t.right.Child? ==>
        keys(t) == {t.key} + keys(t.right.child))
      && (t.left.Thread? && t.right.Thread? ==>
        keys(t) == {t.key})
  {}
  
  lemma KeysLemmas(t: rbtree)
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

  function method valuesP(p: pointer): set<K>
  {
    match p {
      case Child(t) => values(t)
      case Thread(_) => {}
    }
  }

  function method values(t: rbtree): set<V>
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => valuesP(l) + {v} + valuesP(r)
    }
  }

  function method pairsP(p: pointer): set<(K, V)>
  {
    match p {
      case Child(t) => pairs(t)
      case Thread(_) => {}
    }
  }

  function method pairs(t: rbtree): set<(K, V)>
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => pairsP(l) + {(k, v)} + pairsP(r)
    }
  }

  function method sizeP(p: pointer): nat
  {
    match p {
      case Child(t) => size(t)
      case Thread(_) => 0
    }
  }

  function method size(t: rbtree): nat
  {
    match t {
      case Empty => 0
      case Node(l, k, v, r, c) => 1 + sizeP(l) + sizeP(r)
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

  function method preorderP(p: pointer): seq<(K, V)>
  {
    match p {
      case Child(t) => preorder(t)
      case Thread(_) => []
    }
  }

  function method preorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) =>  [(k, v)] + preorderP(l) + preorderP(r)
    }
  }

  function method inorderP(p: pointer): seq<(K, V)>
    ensures p.Child? ==> inorder(p.child) == inorderP(p)
  {
    match p {
      case Child(t) => inorder(t)
      case Thread(_) => []
    }
  }

  function method inorder(t: rbtree): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) => inorderP(l) + [(k, v)] + inorderP(r)
    }
  }
  
  function smallerInorderP(p: pointer, k': K): seq<(K, V)>
  {
    match p {
      case Child(t) => smallerInorder(t, k')
      case Thread(_) => []
    }
  }

  function smallerInorder(t: rbtree, k': K): seq<(K, V)>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) =>
        if k < k' then
          inorderP(l) + [(k, v)] + smallerInorderP(r, k')
        else if k' < k then
          smallerInorderP(l, k')
        else
          inorderP(l)
    }
  }

  function smallerKeysP(p: pointer, k': K): set<K>
  {
    match p {
      case Child(t) => smallerKeys(t, k')
      case Thread(_) => {}
    }
  }

  function smallerKeys(t: rbtree, k': K): set<K>
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) =>
        if k < k' then
          keysP(l) + {k} + smallerKeysP(r, k')
        else if k' < k then
          smallerKeysP(l, k')
        else
          keysP(l)
    }
  }

  function sizeSmallerP(p: pointer, k': K): nat
  {
    match p {
      case Child(t) => sizeSmaller(t, k')
      case Thread(_) => 0
    }
  }

  function sizeSmaller(t: rbtree, k': K): nat
  {
    match t {
      case Empty => 0
      case Node(l, k, v, r, c) =>
        if k < k' then
          1 + sizeP(l) + sizeSmallerP(r, k')
        else if k' < k then
          sizeSmallerP(l, k')
        else
          sizeP(l)
    }
  }

  function minimumP(p: pointer): K
    requires keysP(p) != {}
  {
    match p {
      case Child(t) => minimum(t)
    }
  }

  function minimum(t: rbtree): K
    requires keys(t) != {}
  {
    match t {
      case Node(Thread(_), k, v, r, c) => k
      case Node(Child(Empty()), k, v, r, c) => k
      case Node(l, k, v, r, c) =>
        minimumP(l)
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

  function method SearchTreeP(p: pointer): bool
    ensures p.Child? ==> (SearchTreeP(p) <==> SearchTree(p.child))
    //ensures p.Thread? ==> SearchTreeP(p)
  {
    match p {
      case Child(t) => SearchTree(t)
      case Thread(_) => true
    }
  }

  function method SearchTree(t: rbtree): bool
    ensures t.Node? && SearchTree(t) ==> (SearchTreeP(t.left) && SearchTreeP(t.right))
  {
    match t {
      case Empty => true
      case Node(l, k, v, r, c) =>
        && (forall m | m in keysP(l) :: m < k)
        && (forall m | m in keysP(r) :: k < m)
        && SearchTreeP(l)
        && SearchTreeP(r)
    }
  }

  function method GetP(p: pointer, k: K): V
    requires k in keysP(p)
    requires SearchTreeP(p)
  {
    match p {
      case Child(t) => Get(t, k)
    }
  }

  function method Get(t: rbtree, k: K): V
    requires k in keys(t)
    requires SearchTree(t)
  {
    if k < t.key then
      assert k !in keysP(t.right);
      GetP(t.left, k)
    else if t.key < k then
      assert k !in keysP(t.left);
      GetP(t.right, k)
    else
      t.value
  }

  function method GetSubtreeP(p: pointer, k: K): rbtree
    requires k in keysP(p)
    requires SearchTreeP(p)
  {
    match p {
      case Child(t) => GetSubtree(t, k)
    }
  }

  function method GetSubtree(t: rbtree, k: K): rbtree
    requires k in keys(t)
    requires SearchTree(t)
    ensures Subtree(GetSubtree(t, k), t)
    ensures GetSubtree(t, k).Node?
    ensures GetSubtree(t, k).key == k
  {
    if k < t.key then
      assert k !in keysP(t.right);
      GetSubtreeP(t.left, k)
    else if t.key < k then
      assert k !in keysP(t.left);
      GetSubtreeP(t.right, k)
    else
      t
  }

  function method minSubtreeP(p: pointer): rbtree
    requires p.Child? && p.child.Node?
  {
    match p {
      case Child(t) => minSubtree(t)
    }
  }

  function method minSubtree(t: rbtree): rbtree
    requires keys(t) != {}
    ensures Subtree(minSubtree(t), t)
    ensures minSubtree(t).Node?
  {
    if t.left.Child? && t.left.child.Node? then
      minSubtreeP(t.left)
    else
      t
  }

  function method maxSubtreeP(p: pointer): rbtree
    requires p.Child? && p.child.Node?
    requires SearchTreeP(p)
  {
    match p {
      case Child(t) => maxSubtree(t)
    }
  }

  function method maxSubtree(t: rbtree): rbtree
    requires keys(t) != {}
    requires SearchTree(t)
    ensures Subtree(maxSubtree(t), t)
    ensures maxSubtree(t).Node?
  {
    if t.right.Child? && t.right.child.Node? then
      maxSubtreeP(t.right)
    else
      t
  }

  function method toMap(t: rbtree): map<K, V>
    requires SearchTree(t)
  {
    map k: K | k in keys(t) :: Get(t, k)
  }

  predicate SubtreeP(node: rbtree, proot: pointer)
    ensures SubtreeP(node, proot) ==> keys(node) <= keysP(proot)
    ensures SubtreeP(node, proot) ==> keysAndThreads(node) <= keysAndThreadsP(proot)
    ensures SubtreeP(node, proot) && SearchTreeP(proot) ==> SearchTree(node)
  {
    match proot {
      case Child(root) => Subtree(node, root)
      case Thread(_) => false
    }
  }

  predicate Subtree(node: rbtree, root: rbtree)
    ensures Subtree(node, root) ==> keys(node) <= keys(root)
    ensures Subtree(node, root) ==> keysAndThreads(node) <= keysAndThreads(root)
    ensures Subtree(node, root) && SearchTree(root) ==> SearchTree(node)
  {
    || root == node
    || (
      && root.Node?
      && (SubtreeP(node, root.left) || SubtreeP(node, root.right)))
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

  lemma OrderKeysIsTreeKeysP(p: pointer)
    ensures orderKeysToSet(inorderP(p)) == keysP(p)
  {}

  lemma OrderKeysIsTreeKeys(t: rbtree)
    ensures orderKeysToSet(inorder(t)) == keys(t)
  {}

  lemma OrderSetIsTreePairs(t: rbtree)
    ensures orderToSet(inorder(t)) == pairs(t)
  {}

  lemma SmallerOrderKeysIsTreeKeysP(p: pointer, k': K)
    ensures orderKeysToSet(smallerInorderP(p, k')) == smallerKeysP(p, k')
  {
    if p.Child? {
      SmallerOrderKeysIsTreeKeys(p.child, k');
    }
  }

  lemma SmallerOrderKeysIsTreeKeys(t: rbtree, k': K)
    ensures orderKeysToSet(smallerInorder(t, k')) == smallerKeys(t, k')
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          //keysP(l) + {k} + smallerKeysP(r, k')
          OrderKeysIsTreeKeysP(l);
          SmallerOrderKeysIsTreeKeysP(r, k');
        } else if k' < k {
          //smallerKeysP(l, k')
          SmallerOrderKeysIsTreeKeysP(l, k');
        } else {
          //keysP(l)
          OrderKeysIsTreeKeysP(l);
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

  lemma KeyInOrderP(p: pointer, k': K)
    requires k' in keysP(p)
    ensures exists i :: 0 <= i < |inorderP(p)| && inorderP(p)[i].0 == k'
  {
    match p {
      case Child(t) => {
        assert inorderP(p) == inorder(t);
        KeyInOrder(t, k');
      }
      case Thread(_) => {}
    }
  }

  lemma KeyInOrder(t: rbtree, k': K)
    requires k' in keys(t)
    ensures exists i :: 0 <= i < |inorder(t)| && inorder(t)[i].0 == k'
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => {
        if k' in keysP(l) {
          KeyInOrderP(l, k');
          var i :| 0 <= i < |inorderP(l)| && inorderP(l)[i].0 == k';
          assert inorder(t)[i].0 == k';
        } else if k' in keysP(r) {
          KeyInOrderP(r, k');
          var i :| 0 <= i < |inorderP(r)| && inorderP(r)[i].0 == k';
          var j := i+|inorderP(l)|+1;
          assert 0 <= j < |inorder(t)|;
          assert inorder(t)[j].0 == k';
        } else {
          assert k == k';
          assert inorder(t)[|inorderP(l)|].0 == k';
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
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if l.Child? {
          assert keysP(l) == keys(l.child);
          KeySetIsOrderKeysR(l.child, m => m < k);
        }
        if r.Child? {
          assert keysP(r) == keys(r.child);
          KeySetIsOrderKeysR(r.child, m => k < m);
        }
      }
    }
  }

/*
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
  */

  lemma SearchImpliesUnique(t: rbtree)
    requires SearchTree(t)
    ensures forall i, j | 0 <= i < j < |inorder(t)| ::
      inorder(t)[i].0 != inorder(t)[j].0
  {
    SearchImpliesOrdered(t);
  }

/*
  lemma toMapLemmas(t: rbtree)
    requires SearchTree(t)
    ensures t.Node? ==>
      && toMap(t) == toMap(t.left) + toMap(t.right) + map[t.key := t.value]
      && toMap(t) == toMap(t.left) + map[t.key := t.value] + toMap(t.right)
  {}
*/

  lemma DisjointBranches(t: rbtree)
    requires SearchTree(t)
    requires t.Node?
    ensures t.key !in keysP(t.left)
    ensures t.key !in keysP(t.right)
    ensures keysP(t.left) !! keysP(t.right)
  {
    var k := t.key;
    var l := t.left;
    var r := t.right;
    assert forall m | m in keysP(l) :: m < k;
    assert forall m | m in keysP(r) :: k < m;
    assert forall p, q | p in keysP(l) && q in keysP(r) :: p < k < q;
    assert keysP(l) !! keysP(r);
  }

  lemma SizeKeysP(p: pointer)
    requires SearchTreeP(p)
    ensures sizeP(p) == |keysP(p)|

  lemma SizeKeys(t: rbtree)
    requires SearchTree(t)
    ensures size(t) == |keys(t)|
  {
    match t {
      case Empty => {}
      case Node(l, k, v, r, c) => {
        calc == {
          size(t);
          1 + sizeP(l) + sizeP(r);
          {
            SizeKeysP(l);
            SizeKeysP(r);
          }
          1 + |keysP(l)| + |keysP(r)|;
          |keysP(l)| + |{k}| + |keysP(r)|;
          {
            assert k !in keysP(l);
            assert k !in keysP(r);
            DisjointBranches(t);
            assert keysP(l) !! keysP(r);
          }
          |keysP(l) + {k} + keysP(r)|;
          |keys(t)|;
        }
      }
    }
  }

  lemma SizeSmallerP(p: pointer, k: K)
    ensures sizeSmallerP(p, k) <= sizeP(p)
    ensures SearchTreeP(p) && k in keysP(p) ==>
      sizeSmallerP(p, k) < sizeP(p)
  {
    if p.Child? {
      SizeSmaller(p.child, k);
    }
  }

  lemma SizeSmaller(t: rbtree, k: K)
    ensures sizeSmaller(t, k) <= size(t)
    ensures SearchTree(t) && k in keys(t) ==>
      sizeSmaller(t, k) < size(t)
  {
    if t.Node? {
      SizeSmallerP(t.left, k);
      SizeSmallerP(t.right, k);
    }
  }

  lemma SizeInorder(t: rbtree)
    ensures size(t) == |inorder(t)|
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

/*
  lemma OrderKeysIsMapKeys(t: rbtree)
    requires SearchTree(t)
    ensures orderKeysToSet(inorder(t)) == toMap(t).Keys
  {
    OrderKeysIsTreeKeys(t);
  }

  lemma MapTreeEmpty(t: rbtree)
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

  lemma MapTreeEmptyL(t: rbtree)
    requires SearchTree(t)
    ensures t.Empty? <== toMap(t) == map[]
    ensures t.Node? <== toMap(t) != map[]
  {
    MapTreeEmpty(t);
  }

  lemma ElemthInorder0(t: rbtree)
    requires SearchTree(t)
    requires toMap(t) != map[] || t.Node?
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
  */

  lemma InorderSmallerInorderP(p: pointer, k: K)
    ensures |smallerInorderP(p, k)| <= |inorderP(p)|
    ensures smallerInorderP(p, k) == inorderP(p)[..|smallerInorderP(p, k)|]
  {
    if p.Child? {
      InorderSmallerInorder(p.child, k);
    }
  }

  lemma InorderSmallerInorder(t: rbtree, k: K)
    ensures |smallerInorder(t, k)| <= |inorder(t)|
    ensures smallerInorder(t, k) == inorder(t)[..|smallerInorder(t, k)|]
  {
    if t.Node? {
      InorderSmallerInorderP(t.left, k);
      InorderSmallerInorderP(t.right, k);
    }
  }

    /*
  lemma SmallerInorderIndex(t: rbtree, k: K, i: nat)
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
      if t.left.Child? && i < |inorderP(t.left)| {
        SmallerInorderIndex(t.left.child, k, i);
        assert i == |smallerInorder(t.left.child, k)| == |smallerInorder(t, k)|;
      }
      if t.right.Child? && i > |inorderP(t.left)| {
        SmallerInorderIndex(t.right.child, k, i - |inorderP(t.left)| - 1);
      }
    }
  }
    */

  lemma SmallerInorderIndex(t: rbtree, k': K, i: nat)
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
        assert inorder(t)[|inorderP(l)|].0 == k;
        if k < k' {
          //inorderP(l) + [(k, v)] + smallerInorderP(r, k')
          assert |inorderP(l)| < i;
          if t.right.Child? {
            SmallerInorderIndex(t.right.child, k', i - |inorderP(l)| - 1);
          }
        } else if k' < k {
          //smallerInorderP(l, k')
          assert i < |inorderP(l)|;
          if t.left.Child? {
            SmallerInorderIndex(t.left.child, k', i);
          }
        } else {
          //inorderP(l)
          assert i == |inorderP(l)|;
        }
      }
    }
  }

  /*
  lemma SmallerInorderRightInd(root: rbtree, node: rbtree)
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

  lemma SmallerInorderLeftInd(root: rbtree, node: rbtree)
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

  lemma SubtreeChildren(a: rbtree, b: rbtree)
    requires a.Node?
    requires Subtree(a, b)
    ensures a.left.Child? ==> Subtree(a.left.child, b)
    ensures a.right.Child? ==> Subtree(a.right.child, b)
  {
    if a == b {
    } else {
      if SubtreeP(a, b.left) {
        if b.left.Child? {
          SubtreeChildren(a, b.left.child);
        }
      } else if SubtreeP(a, b.right) {
        if b.right.Child? {
          SubtreeChildren(a, b.right.child);
        }
      } else {
        assert false;
      }
    }
  }

  lemma SubtreeTrans(a: rbtree, b: rbtree, c: rbtree)
    requires Subtree(a, b)
    requires Subtree(b, c)
    ensures Subtree(a, c)
  {
    if a == b {
    } else {
      if SubtreeP(a, b.left) {
        if b.left.Child? {
          assert Subtree(a, b.left.child);
          assert Subtree(b.left.child, c) by {
            SubtreeChildren(b, c);
          }
          SubtreeTrans(a, b.left.child, c);
        }
      } else if SubtreeP(a, b.right) {
        if b.right.Child? {
          SubtreeChildren(b, c);
          SubtreeTrans(a, b.right.child, c);
        }
      } else {
        assert false;
      }
    }
  }

  /* Threaded Tree */

  type threadOrEmpty = p: pointer | p.Thread? || (p.Child? && p.child.Empty?) witness Child(Empty)

/*
  function method ThreadedTreeRecP(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, onLeft: bool): bool
    ensures p.Child? && !p.child.Empty? ==>
      (ThreadedTreeRecP(prev, p, next, onLeft) <==> ThreadedTreeRec(prev, p.child, next))
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

  function method ThreadedTreeRec(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty): bool
    decreases t
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRecP(prev, l, Thread(k), true)
        && ThreadedTreeRecP(Thread(k), r, next, false)
    }
  }
  */

  function method ThreadedTreeRecPL(prev: threadOrEmpty, p: pointer, next: threadOrEmpty): bool
    decreases p
    ensures p.Child? && !p.child.Empty? ==>
      (ThreadedTreeRecPL(prev, p, next) <==> ThreadedTreeRec(prev, p.child, next))
  {
    match p {
      case Child(Empty) => prev.Child? && prev.child.Empty?
      case Child(t) => ThreadedTreeRec(prev, t, next)
      case Thread(k) => prev.Thread? && prev.thread == k
    }
  }

  function method ThreadedTreeRecPR(prev: threadOrEmpty, p: pointer, next: threadOrEmpty): bool
    decreases p
    ensures p.Child? && !p.child.Empty? ==>
      (ThreadedTreeRecPR(prev, p, next) <==> ThreadedTreeRec(prev, p.child, next))
  {
    match p {
      case Child(Empty) => next.Child? && next.child.Empty?
      case Child(t) => ThreadedTreeRec(prev, t, next)
      case Thread(k) => next.Thread? && next.thread == k
    }
  }

  function method ThreadedTreeRec(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty): bool
    decreases t
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        && ThreadedTreeRecPL(prev, l, Thread(k))
        && ThreadedTreeRecPR(Thread(k), r, next)
    }
  }

  function method ThreadedTreeRoot(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Node(_, _, _, _, _) => ThreadedTreeRec(Child(Empty), t, Child(Empty))
    }
  }

  lemma ThreadedKeys(t: rbtree)
    requires ThreadedTreeRoot(t)
    ensures keys(t) == keysAndThreads(t)

  lemma SmallerKeysP(p: pointer, k': K)
    requires SearchTreeP(p)
    ensures smallerKeysP(p, k') == set k | k in keysP(p) && k < k'
  {
    match p {
      case Child(t) => {
        SmallerKeys(t, k');
      }
      case Thread(_) => {
      }
    }
  }

  lemma SmallerKeys(t: rbtree, k': K)
    requires SearchTree(t)
    ensures smallerKeys(t, k') == set k | k in keys(t) && k < k'
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) =>
        if k < k' {
          SmallerKeysP(r, k');
        } else if k' < k {
          SmallerKeysP(l, k');
        } else {
        }
    }
  }

  lemma SmallerKeysLeft(t: rbtree)
    requires SearchTree(t)
    requires t.Node?
    requires t.left.Child?
    ensures smallerKeys(t, t.key) == keys(t.left.child)
  {
    SmallerKeys(t, t.key);
  }

  lemma RightThreadIsBiggerRec(node: rbtree, prev: threadOrEmpty, root: rbtree, next: threadOrEmpty)
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

  lemma RightThreadIsBiggerRoot(node: rbtree, root: rbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires Subtree(node, root)
    requires node.Node?
    requires node.right.Thread?
    ensures node.key < node.right.thread
  {
    RightThreadIsBiggerRec(node, Child(Empty), root, Child(Empty));
  }

  lemma ThreadedInorderRec(it: rbtree, left: seq<(K, V)>, right: seq<(K, V)>, prev: threadOrEmpty, node: rbtree, next: threadOrEmpty, root: rbtree)
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
        i := ThreadedInorderRec(it, left, [(node.key, node.value)] + inorderP(node.right) + right, prev, node.left.child, Thread(node.key), root);
      }
    } else if node.key < it.key {
      if node.right.Child? {
        i := ThreadedInorderRec(it, left + inorderP(node.left) + [(node.key, node.value)], right, Thread(node.key), node.right.child, next, root);
      }
    } else {
      assert node == it;
      i := |left| + |inorderP(node.left)|;
    }
  }

  lemma ThreadedInorderRoot(it: rbtree, root: rbtree)
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

  lemma SmallerKeysOfThreadedRoot(node: rbtree, root: rbtree)
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

  function ThreadedTreeExample1(): rbtree {
    Node(
      Child(Node(
        Child(Node(Child(Empty), 1, 0, Thread(2), Black)),
        2,
        0,
        Child(Node(Thread(2), 3, 0, Thread(4), Black)),
        Black
      )),
      4,
      0,
      Child(Node(
        Child(Node(Thread(4), 5, 0, Thread(6), Black)),
        6,
        0,
        Child(Node(Thread(6), 7, 0, Child(Empty), Black)),
        Black
      )),
      Black
    )
  }

  lemma ThreadedExamples()
    ensures ThreadedTreeRoot(ThreadedTreeExample1())
  {}

  /* Red Black Tree */

  function method isRed(t: rbtree): bool
  {
    t.Node? && t.color.Red?
  }

  function method isRedP(p: pointer): bool
  {
    p.Child? && p.child.Node? && p.child.color.Red?
  }

  function method isBlack(t: rbtree): bool
  {
    t.Node? && t.color.Black?
  }

  function method isBlackP(p: pointer): bool
  {
    p.Child? && p.child.Node? && p.child.color.Black?
  }

  function method BlackHeightP(p: pointer): nat
    ensures p.Child? ==> (BlackHeightP(p) == BlackHeight(p.child))
  {
    match p {
      case Child(t) => BlackHeight(t)
      case Thread(_) => 0
    }
  }

  function method BlackHeight(t: rbtree): nat
  {
    match t {
      case Empty => 0
      case Node(l, k, v, r, c) =>
        if c.Black? then
          1 + Utils.max(BlackHeightP(l), BlackHeightP(r))
        else
          Utils.max(BlackHeightP(l), BlackHeightP(r))
    }
  }

  function method isNode(p: pointer): bool
  {
    p.Child? && p.child.Node?
  }

  function method RedBlackTreeP(p: pointer): bool
    ensures p.Child? ==> (RedBlackTreeP(p) <==> RedBlackTree(p.child))
  {
    match p {
      case Child(t) => RedBlackTree(t)
      case Thread(_) => true
    }
  }

  function method RedBlackTree(t: rbtree): bool
  {
    match t {
      case Empty => true
      case Node(l, k, v, r, c) =>
        // Red links lean left:
        && (isNode(r) ==> isBlackP(r))
        // No node has two red links connected to it:
        && (isRedP(l) && isNode(l.child.left) ==> isBlackP(l.child.left))
        // Perfect black balance:
        && BlackHeightP(l) == BlackHeightP(r)

        && RedBlackTreeP(l)
        && RedBlackTreeP(r)
    }
  }

  function method RedBlackTreeRoot(t: rbtree): bool
  {
    RedBlackTree(t) && (t.Node? ==> t.color.Black?)
  }
}
