include "../../../../src/Collections/Set.dfy"
include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/Collections/SetInt.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/RemoveElemAt.dfy"

module ThreadedLinkedTree.Model.Iterator {
  import opened Set
  import opened SetInt
  import opened KeyValue
  import opened Color
  import opened Base
  import opened RemoveElemAt

  datatype iter
    = Null
    | Link(link: K)

  predicate Valid(it: iter, root: trbtree)
  {
    it.Link? ==> it.link in keys(root)
  }

  predicate HasPeek(it: iter)
  {
    it.Link?
  }

  function Peek(it: iter, root: trbtree): (K, V)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    ToMapRecKeys(root);
    (it.link, toMapRec(root)[it.link])
  }

  function Before(it: iter, root: trbtree): set<K>
    requires HasPeek(it)
  {
    smallerKeys(root, it.link)
  }

  lemma BeforeSpec(it: iter, root: trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    requires SearchTree(root)
    ensures Before(it, root) < toMapRec(root).Keys
    ensures |Before(it, root)| < |toMapRec(root)|
  {
    SmallerKeys(root, it.link);
    ToMapRecKeys(root);
    SizeLemmas(root);
  }

  lemma PeekSpec(it: iter, root: trbtree)
    requires HasPeek(it)
    requires Valid(it, root)
    requires SearchTree(root)
    ensures Peek(it, root) in toMapRec(root).Items
    ensures Peek(it, root).0 !in Before(it, root)
    ensures forall x <- Before(it, root) :: x < Peek(it, root).0
    ensures forall x <- toMapRec(root) | x !in Before(it, root) :: Peek(it, root).0 <= x
  {
    SmallerKeys(root, it.link);
    ToMapRecKeys(root);
  }

  function Traversed(it: iter, root: trbtree): set<K>
  {
    match it {
      case Null => keys(root)
      case Link(k) => Before(it, root)
    }
  }

  function After(it: iter, root: trbtree): set<K>
    requires HasPeek(it)
  {
    biggerKeys(root, it.link)
  }

  lemma AfterSpec(it: iter, root: trbtree)
    requires SearchTree(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures After(it, root) == (toMapRec(root).Keys - {it.link}) - Before(it, root)
  {
    BiggerKeys(root, it.link);
    SmallerKeys(root, it.link);
    ToMapRecKeys(root);
  }

  function RTraversed(it: iter, root: trbtree): set<K>
  {
    match it {
      case Null => keys(root)
      case Link(k) => After(it, root)
    }
  }

  lemma RTraversedSpec(it: iter, root: trbtree)
    ensures RTraversed(it, root) == if HasPeek(it) then After(it, root) else toMapRec(root).Keys
  {
    ToMapRecKeys(root);
  }

  function First(root: trbtree): iter
  {
    if root.Node? then
      Link(minimumKey(root))
    else
      Null
  }

  lemma FirstSpec(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Valid(First(root), root)
  {}

  lemma FirstTraversed(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Traversed(First(root), root) == {}
  {
    if root.Node? {
      SearchImpliesOrdered(root);
      SmallerKeys(root, First(root).link);
      forall k | k in keys(root)
        ensures !(k < minimumKey(root))
      {
        KeyInOrder(root, k);
      }
    }
  }

  function Last(root: trbtree): iter
  {
    if root.Node? then
      Link(maximumKey(root))
    else
      Null
  }

  lemma LastSpec(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures Valid(Last(root), root)
  {}

  lemma LastRTraversed(root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    ensures RTraversed(Last(root), root) == {}
  {
    if root.Node? {
      SearchImpliesOrdered(root);
      BiggerKeys(root, Last(root).link);
      forall k | k in keys(root)
        ensures !(maximumKey(root) < k)
      {
        KeyInOrder(root, k);
      }
    }
  }

  function Find(k: K, root: trbtree): iter
  {
    if k in keys(root) then
      Link(k)
    else
      Null
  }

  lemma FindPeek(k: K, root: trbtree)
    requires k in keys(root)
    requires SearchTree(root)
    ensures Peek(Find(k, root), root) == (k, Get'(root, k))
  {
    Get'ToMapRec(root, k);
  }

  lemma FindAfterInsert(k: K, v: V, root: trbtree)
    requires SearchTree(root)
    requires k in keys(root)
    requires assert keys(root) == toMapRec(root).Keys by {ToMapRecKeys(root);} true
    requires toMapRec(root)[k] == v
    ensures Peek(Find(k, root), root) == (k, v)
  {
    assert Peek(Find(k, root), root).0 == k;
    assert Peek(Find(k, root), root).1 == v by {
      Get'ToMapRec(root, k);
    }
  }

  function Next(it: iter, root: trbtree): iter
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty => Null
    case Thread(k) =>
      assert k in keys(root) by {
        assert k in keysAndThreads(t);
        assert k in keysAndThreads(root);
        ThreadedKeys(root);
      }
      Link(k)
    case Node(_, _, _, _, _) =>
      Link(minimumKey(t.right))
  }

  lemma NextSpec(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Valid(Next(it, root), root)
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty =>
    case Thread(k) =>
      assert k in keysAndThreads(t);
      assert k in keysAndThreads(root);
      ThreadedKeys(root);
    case Node(_, _, _, _, _) =>
  }

  lemma NextTraversed(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Traversed(Next(it, root), root)
      == Before(it, root) + {Peek(it, root).0}
  {
    var t := GetSubtree(root, it.link);
    match t.right
    case Empty =>
      SmallerKeysRightEmpty(t, root);
    case Thread(k) =>
      SmallerKeysRightThread(t, root);
    case Node(_, _, _, _, _) =>
      SmallerKeysMin(t, root);
  }

  function Prev(it: iter, root: trbtree): iter
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
  {
    var t := GetSubtree(root, it.link);
    match t.left
    case Empty => Null
    case Thread(k) =>
      assert k in keys(root) by {
        assert k in keysAndThreads(t);
        assert k in keysAndThreads(root);
        ThreadedKeys(root);
      }
      Link(k)
    case Node(_, _, _, _, _) =>
      Link(maximumKey(t.left))
  }

  lemma PrevRTraversed(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures RTraversed(Prev(it, root), root)
      == After(it, root) + {Peek(it, root).0}
  {
    var t := GetSubtree(root, it.link);
    match t.left
    case Empty =>
      BiggerKeysLeftEmpty(t, root);
    case Thread(k) =>
      BiggerKeysLeftThread(t, root);
    case Node(_, _, _, _, _) =>
      BiggerKeysMax(t, root);
  }


  lemma PrevSpec(it: iter, root: trbtree)
    requires SearchTree(root)
    requires ThreadedTreeRoot(root)
    requires HasPeek(it)
    requires Valid(it, root)
    ensures Valid(Prev(it, root), root)
  {
    var t := GetSubtree(root, it.link);
    match t.left
    case Empty =>
    case Thread(k) =>
      assert k in keysAndThreads(t);
      assert k in keysAndThreads(root);
      ThreadedKeys(root);
    case Node(_, _, _, _, _) =>
  }

  lemma ModelAfterInsert(it: iter, k: K, v: V, root: trbtree, root': trbtree)
    requires SearchTree(root)
    requires SearchTree(root')
    requires Valid(it, root)
    requires toMapRec(root') == toMapRec(root)[k := v]

    ensures Valid(it, root')
    ensures HasPeek(it) ==>
      && Peek(it, root').0 == Peek(it, root).0
      && if k in keys(root) && k == it.link then
        Peek(it, root').1 == v
      else
        Peek(it, root').1 == Peek(it, root).1
    ensures
      if k in keys(root) || (it.Link? && it.link < k) then
        && Traversed(it, root') == Traversed(it, root)
        && |Traversed(it, root')| == |Traversed(it, root)|
      else
        && Traversed(it, root') == Traversed(it, root) + {k}
        && |Traversed(it, root')| == |Traversed(it, root)| + 1
  {
    ToMapRecKeys(root);
    ToMapRecKeys(root');
    assert Valid(it, root');
    if HasPeek(it) {
      assert Peek(it, root').0 == Peek(it, root).0;
      if k in keys(root) && k == it.link {
        assert Peek(it, root').1 == v;
      } else {
        calc == {
          Peek(it, root').1;
          toMapRec(root')[it.link];
          toMapRec(root)[it.link];
          Peek(it, root).1;
        }
      }
    }
    if it.Link? {
      SmallerKeys(root, it.link);
      SmallerKeys(root', it.link);
    }
    if k in keys(root) {
      assert Traversed(it, root') == Traversed(it, root) by {
      }
    } else if !it.Link? || k < it.link {
      assert Traversed(it, root') == Traversed(it, root) + {k} by {
      }
    } else {
      assert Traversed(it, root') == Traversed(it, root) by {
      }
    }
  }

  lemma ModelAfterRemove(it: iter, k: K, root: trbtree, root': trbtree)
    requires SearchTree(root)
    requires SearchTree(root')
    requires Valid(it, root)
    requires toMapRec(root') == toMapRec(root) - {k}

    ensures Valid(it, root') <==> (it.Link? ==> it.link != k)
    ensures HasPeek(it) && k != it.link ==>
      Peek(it, root') == Peek(it, root)
    ensures
      if k in keys(root) && (it.Link? ==> k < it.link) then
        && Traversed(it, root') == Traversed(it, root) - {k}
        && |Traversed(it, root')| == |Traversed(it, root)| - 1
      else
        && Traversed(it, root') == Traversed(it, root)
        && |Traversed(it, root')| == |Traversed(it, root)|
  {
    ToMapRecKeys(root);
    ToMapRecKeys(root');
    assert Valid(it, root') <==> !(it.Link? && it.link == k);

    if HasPeek(it) && k != it.link {
      calc == {
        Peek(it, root');
        (it.link, toMapRec(root')[it.link]);
        (it.link, toMapRec(root)[it.link]);
        Peek(it, root);
      }
    }

    if it.Link? {
      SmallerKeys(root, it.link);
      SmallerKeys(root', it.link);
    }
    if k in keys(root) && (it.Link? ==> k < it.link) {
      assert Traversed(it, root') == Traversed(it, root) - {k};
      assert |Traversed(it, root')| == |Traversed(it, root)| - 1;
    } else {
      assert Traversed(it, root') == Traversed(it, root);
      assert |Traversed(it, root')| == |Traversed(it, root)|;
    }
  }
}
