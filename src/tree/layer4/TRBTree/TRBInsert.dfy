include "../../../../src/MUtils.dfy"
include "../../../../src/tree/KeyValue.dfy"
include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"

module TRBTree.TRBInsert {
  //import opened Utils
  import opened KeyValue
  import opened Color
  import opened Base

  function method FlipColors(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    Node(
      Child(Node(
        t.left.child.left,
        t.left.child.key,
        t.left.child.value,
        t.left.child.right,
        NegColor(t.left.child.color)
      )),
      t.key,
      t.value,
      Child(Node(
        t.right.child.left,
        t.right.child.key,
        t.right.child.value,
        t.right.child.right,
        NegColor(t.right.child.color)
      )),
      NegColor(t.color)
    )
  }

  function method RotateLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.right.Child?
    requires t.right.child.Node?
  {
    Node(
      Child(Node(
        t.left,
        t.key,
        t.value,
        if t.right.child.left.Thread? then
          Thread(t.right.child.key)
        else
          t.right.child.left,
        Red
      )),
      t.right.child.key,
      t.right.child.value,
      t.right.child.right,
      t.color
    )
  }

  function method RotateRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
  {
    Node(
      t.left.child.left,
      t.left.child.key,
      t.left.child.value,
      Child(Node(
        if t.left.child.right.Thread? then
          Thread(t.left.child.key)
        else
          t.left.child.right,
        t.key,
        t.value,
        t.right,
        Red
      )),
      t.color
    )
  }

  function method Restore(t: rbtree): rbtree
    requires t.Node?
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    if isRedP(t''.left) && isRedP(t''.right) then
      FlipColors(t'')
    else
      t''
  }

  function method TRBInsertP(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V): pointer
    decreases p
  {
    match p {
      case Child(t) => Child(TRBInsert(prev, t, next, k', v'))
      case Thread(k) => Child(Node(prev, k', v', next, Red))
    }
  }

  function method TRBInsert(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V): rbtree
    decreases t
  {
    match t {
      case Empty => Node(prev, k', v', next, Red)
      case Node(l, k, v, r, c) =>
        if k < k' then
          Restore(Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c))
        else if k' < k then
          Restore(Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c))
        else
          Node(l, k, v', r, c)
    }
  }

  function method BlackenRoot(t: rbtree): rbtree
  {
    match t {
      case Empty => Empty
      case Node(l, k, v, r, c) =>
        Node(l, k, v, r, Black)
    }
  }

  function method TRBInsertRoot(t: rbtree, k: K, v: V): rbtree
  {
    BlackenRoot(TRBInsert(Child(Empty), t, Child(Empty), k, v))
  }

  lemma FlipColorsSpec(t: rbtree)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires t.left.child.color == NegColor(t.color)
    requires t.right.child.color == NegColor(t.color)
    requires SearchTree(t)
    //requires BlackBalanced(t)
    ensures keys(t) == keys(FlipColors(t))
    ensures SearchTree(FlipColors(t))
    //ensures BlackBalanced(FlipColors(t))
    ensures BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma RotateLeftSpec(t: rbtree)
    requires t.Node?
    requires isRedP(t.right)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateLeft(t))
    ensures SearchTree(RotateLeft(t))
    ensures BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {
    if t.right.child.left.Thread? {
      assert PointerSearchTree(RotateLeft(t).left.child.right);
      assert PointerBlackHeight(RotateLeft(t).left.child.right) == PointerBlackHeight(t.right.child.left);
    }
  }

  lemma RotateLeftThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.right.Child?
    requires t.right.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, RotateLeft(t), next)
  {
    assert ThreadedTreeRecPL(prev, RotateLeft(t).left, Thread(RotateLeft(t).key)) by {
      assert ThreadedTreeRec(prev, RotateLeft(t).left.child, Thread(RotateLeft(t).key)) by {
        assert ThreadedTreeRecPL(prev, RotateLeft(t).left.child.left, Thread(RotateLeft(t).left.child.key));
        assert ThreadedTreeRecPR(Thread(RotateLeft(t).left.child.key), RotateLeft(t).left.child.right, Thread(RotateLeft(t).key)) by {
          assert ThreadedTreeRecPL(Thread(t.key), t.right.child.left, Thread(t.right.child.key));
        }
      }
    }
    assert ThreadedTreeRecPR(Thread(RotateLeft(t).key), RotateLeft(t).right, next);
  }

  lemma RotateRightSpec(t: rbtree)
    requires t.Node?
    requires isRedP(t.left)
    requires SearchTree(t)
    ensures keys(t) == keys(RotateRight(t))
    ensures SearchTree(RotateRight(t))
    ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    if t.left.child.right.Thread? {
      assert PointerSearchTree(RotateRight(t).right.child.left);
      assert PointerBlackHeight(RotateRight(t).right.child.left) == PointerBlackHeight(t.left.child.right);
    }
  }

  lemma RotateRightThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires t.left.Child?
    requires t.left.child.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, RotateRight(t), next)
  {
    assert ThreadedTreeRecPL(prev, RotateRight(t).left, Thread(RotateRight(t).key));
    assert ThreadedTreeRecPR(Thread(RotateRight(t).key), RotateRight(t).right, next) by {
      assert ThreadedTreeRec(Thread(RotateRight(t).key), RotateRight(t).right.child, next) by {
        assert ThreadedTreeRecPL(Thread(RotateRight(t).key), RotateRight(t).right.child.left, Thread(RotateRight(t).right.child.key)) by {
          assert ThreadedTreeRecPR(Thread(t.left.child.key), t.left.child.right, Thread(t.key));
        }
        assert ThreadedTreeRecPR(Thread(RotateRight(t).right.child.key), RotateRight(t).right.child.right, next);
      }
    }
  }

  lemma AllFlipColorsSpec()
    ensures forall t: rbtree
        | t.Node?
        && t.left.Child?
        && t.left.child.Node?
        && t.right.Child?
        && t.right.child.Node?
        && t.left.child.color == NegColor(t.color)
        && t.right.child.color == NegColor(t.color)
        && SearchTree(t)
      :: keys(t) == keys(FlipColors(t))
      && SearchTree(FlipColors(t))
      && BlackHeight(t) == BlackHeight(FlipColors(t))
  {}

  lemma AllRotateLeftSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRedP(t.right)
        && SearchTree(t)
        && RedBlackTree(t)
      :: keys(t) == keys(RotateLeft(t))
      && SearchTree(RotateLeft(t))
      && BlackHeight(RotateLeft(t)) == BlackHeight(t)
  {}

  lemma AllRotateRightSpec()
    ensures forall t: rbtree
        | t.Node?
        && isRedP(t.left)
        && SearchTree(t)
      :: keys(t) == keys(RotateRight(t))
      && SearchTree(RotateRight(t))
      && BlackHeight(RotateRight(t)) == BlackHeight(t)
  {
    forall t: rbtree
        | t.Node?
        && isRedP(t.left)
        && SearchTree(t)
      ensures keys(t) == keys(RotateRight(t))
      ensures SearchTree(RotateRight(t))
      ensures BlackHeight(RotateRight(t)) == BlackHeight(t)
    {
      RotateRightSpec(t);
    }
  }

  lemma RestoreSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRedP(t.right) && isRedP(t.right.child.left) ==>
      isBlack(t) && isRedP(t.left)
    requires !(
      && isRed(t)
      && isRedP(t.left)
      && isRedP(t.right)
    )
    requires !(
      && isRed(t)
      && isRedP(t.left)
      && isRedP(t.left.child.left)
    )
    requires PointerBlackHeight(t.left) == PointerBlackHeight(t.right)
    requires PointerRedBlackTree(t.left)
    requires PointerRedBlackTree(t.right)

    ensures keys(t) == keys(Restore(t))
    ensures SearchTree(Restore(t))
    ensures RedBlackTree(Restore(t))

    ensures BlackHeight(Restore(t)) == BlackHeight(t)
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRedP(Restore(t).left)
    ensures isRed(t) ==> isRed(Restore(t))
    ensures isRed(Restore(t)) && isRedP(Restore(t).left) ==>
      isRed(t) && (isRedP(t.left) || isRedP(t.right))
    ensures isRed(Restore(t)) && isBlack(t) ==>
      || (isRedP(t.left) && isRedP(t.right))
      || (isRedP(t.left) && isRedP(t.left.child.left))
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRedP(t''.left) && isRedP(t''.right) then
        FlipColors(t'')
      else
        t'';
    if isRedP(t.right) {
      RotateLeftSpec(t);
    }
    if isRedP(t'.left) && isRedP(t'.left.child.left) {
      RotateRightSpec(t');
    }
    if isRedP(t''.left) && isRedP(t''.right) {
      FlipColorsSpec(t'');
    }
  }

  lemma RestoreThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty)
    requires t.Node?
    requires ThreadedTreeRec(prev, t, next)
    ensures ThreadedTreeRec(prev, Restore(t), next)
  {
    var t' :=
      if isRedP(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRedP(t'.left) && isRedP(t'.left.child.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRedP(t''.left) && isRedP(t''.right) then
        FlipColors(t'')
      else
        t'';
    if isRedP(t.right) {
      RotateLeftThreaded(prev, t, next);
    }
    if isRedP(t'.left) && isRedP(t'.left.child.left) {
      RotateRightThreaded(prev, t', next);
    }
  }

  lemma TRBInsertPSpec(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V)
    decreases p
    requires PointerSearchTree(p)
    requires PointerRedBlackTree(p)
    requires !(isRedP(p) && isRedP(p.child.left))
    ensures isBlackP(p) && isRed(Restore(p.child)) ==>
      !isRedP(Restore(p.child).left)
    ensures pointerKeys(p) + {k'} == pointerKeys(TRBInsertP(prev, p, next, k', v'))
    ensures PointerSearchTree(TRBInsertP(prev, p, next, k', v'))
    ensures PointerRedBlackTree(TRBInsertP(prev, p, next, k', v'))
    ensures PointerBlackHeight(p) == PointerBlackHeight(TRBInsertP(prev, p, next, k', v'))
  {
    match p {
      case Child(t) => {
        TRBInsertSpec(prev, t, next, k', v');
      }
      case Thread(k) => {
      }
    }
  }

  // 7"
  lemma {:verify false} TRBInsertSpec(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRedP(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRedP(Restore(t).left)
    ensures keys(t) + {k'} == keys(TRBInsert(prev, t, next, k', v'))
    ensures SearchTree(TRBInsert(prev, t, next, k', v'))
    ensures RedBlackTree(TRBInsert(prev, t, next, k', v'))
    ensures BlackHeight(t) == BlackHeight(TRBInsert(prev, t, next, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertPSpec(Thread(k), r, next, k', v');
          RestoreSpec(Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c));
        } else if k' < k {
          TRBInsertPSpec(prev, l, Thread(k), k', v');
          RestoreSpec(Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma TRBInsertPThreaded(prev: threadOrEmpty, p: pointer, next: threadOrEmpty, k': K, v': V)
    decreases p
    requires ThreadedTreeRecPL(prev, p, next) || ThreadedTreeRecPR(prev, p, next)
    ensures TRBInsertP(prev, p, next, k', v').Child?
    ensures TRBInsertP(prev, p, next, k', v').child.Node?
    ensures ThreadedTreeRecPR(prev, TRBInsertP(prev, p, next, k', v'), next)
    ensures ThreadedTreeRecPL(prev, TRBInsertP(prev, p, next, k', v'), next)
  {
    match p {
      case Child(t) => {
        TRBInsertThreaded(prev, t, next, k', v');
      }
      case Thread(k) => {
      }
    }
  }

  lemma TRBInsertThreaded(prev: threadOrEmpty, t: rbtree, next: threadOrEmpty, k': K, v': V)
    decreases t
    requires t.Node? ==> ThreadedTreeRec(prev, t, next)
    ensures TRBInsert(prev, t, next, k', v').Node?
    ensures ThreadedTreeRec(prev, TRBInsert(prev, t, next, k', v'), next)
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          TRBInsertPThreaded(Thread(k), r, next, k', v');
          RestoreThreaded(prev, Node(l, k, v, TRBInsertP(Thread(k), r, next, k', v'), c), next);
        } else if k' < k {
          TRBInsertPThreaded(prev, l, Thread(k), k', v');
          RestoreThreaded(prev, Node(TRBInsertP(prev, l, Thread(k), k', v'), k, v, r, c), next);
        } else {
        }
      }
    }
  }

/*
  // 58"
  lemma {:verify false} FlipColorsModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(FlipColors(t))
    ensures toMap(t) == toMap(FlipColors(t))
  {
    calc == {
      toMap(FlipColors(t));
      toMap(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)),
          NegColor(t.color)
        )
      );
      toMap(Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)))
        + map[t.key := t.value]
        + toMap(Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)));
      toMap(t.left.left) + map[t.left.key := t.left.value] + toMap(t.left.right)
        + map[t.key := t.value]
        + toMap(t.right.left) + map[t.right.key := t.right.value] + toMap(t.right.right);
      toMap(Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color))
        + map[t.key := t.value]
        + toMap(Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color));
      toMap(
        Node(
          Node(t.left.left, t.left.key, t.left.value, t.left.right, t.left.color),
          t.key,
          t.value,
          Node(t.right.left, t.right.key, t.right.value, t.right.right, t.right.color),
          t.color
        )
      );
      toMap(t);
    }
  }

  lemma {:verify false} RotateLeftModel(t: rbtree)
    requires t.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires SearchTree(RotateLeft(t))
    ensures toMap(t) == toMap(RotateLeft(t))
  {
    calc == {
      toMap(RotateLeft(t));
      toMap(
        Node(
          Node(t.left, t.key, t.value, t.right.left, Red),
          t.right.key,
          t.right.value,
          t.right.right,
          t.color
        )
      );
      toMap(Node(t.left, t.key, t.value, t.right.left, Red))
        + map[t.right.key := t.right.value]
        + toMap(t.right.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right.left)
        + map[t.right.key := t.right.value]
        + toMap(t.right.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t);
    }
  }

  lemma {:verify false} RotateRightModel(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires SearchTree(t)
    requires SearchTree(RotateRight(t))
    ensures toMap(t) == toMap(RotateRight(t))
  {
    calc == {
      toMap(RotateRight(t));
      toMap(
        Node(
          t.left.left,
          t.left.key,
          t.left.value,
          Node(t.left.right, t.key, t.value, t.right, Red),
          t.color
        )
      );
      toMap(t.left.left)
        + map[t.left.key := t.left.value]
        + toMap(Node(t.left.right, t.key, t.value, t.right, Red));
      toMap(t.left.left)
        + map[t.left.key := t.left.value]
        + toMap(t.left.right)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t.left)
        + map[t.key := t.value]
        + toMap(t.right);
      toMap(t);
    }
  }

  lemma {:verify false} RestoreModel(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    requires isRed(t.right) && isRed(t.right.left) ==>
      isBlack(t) && isRed(t.left)
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.right)
    )
    requires !(
      && isRed(t)
      && isRed(t.left)
      && isRed(t.left.left)
    )
    requires BlackHeight(t.left) == BlackHeight(t.right)
    requires RedBlackTree(t.left)
    requires RedBlackTree(t.right)

    ensures SearchTree(Restore(t))
    ensures toMap(t) == toMap(Restore(t))
  {
    RestoreSpec(t);
    var t' :=
      if isRed(t.right) then
        RotateLeft(t)
      else
        t;
    var t'' :=
      if isRed(t'.left) && isRed(t'.left.left) then
        RotateRight(t')
      else
        t';
    var t''' :=
      if isRed(t''.left) && isRed(t''.right) then
        FlipColors(t'')
      else
        t'';


    if isRed(t.right) {
      RotateLeftModel(t);
      assert toMap(RotateLeft(t)) == toMap(t);
    }
    assert toMap(t) == toMap(t');

    if isRed(t'.left) && isRed(t'.left.left) {
      RotateRightModel(t');
      assert toMap(RotateRight(t')) == toMap(t');
    }
    assert toMap(t') == toMap(t'');

    if isRed(t''.left) && isRed(t''.right) {
      FlipColorsModel(t'');
      assert toMap(FlipColors(t'')) == toMap(t'');
    }
    assert toMap(t'') == toMap(t''');

    assert t''' == Restore(t);
  }

  // 43"
  lemma {:verify false} TRBInsertModel(lt: option<K>, t: rbtree, rt: option<K>, k': K, v': V)
    decreases t
    requires !t.Thread?
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    requires SearchTree(TRBInsert(lt, t, rt, k', v'))
    ensures toMap(t)[k' := v'] == toMap(TRBInsert(lt, t, rt, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          if r.Thread? {
            RestoreSpec(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c));
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)));
              { RestoreModel(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)); }
              toMap(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c));
              { toMapLemmas(Node(l, k, v, Node(Thread(k), k', v', Thread(fromThread(r)), Red), c)); }
              toMap(l) + map[k := v] + toMap(Node(Thread(k), k', v', Thread(fromThread(r)), Red));
              { toMapLemmas(Node(Thread(k), k', v', Thread(fromThread(r)), Red)); }
              toMap(l) + map[k := v] + (map[] + map[k' := v'] + map[]);
              toMap(l) + map[k := v] + map[k' := v'];
              (toMap(l) + map[k := v]) + map[k' := v'];
              (toMap(l) + map[k := v] + toMap(r)) + map[k' := v'];
              { toMapLemmas(t); }
              toMap(t) + map[k' := v'];
            }
          } else {
            TRBInsertSpec(Some(k), r, rt, k', v');
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)));
              { RestoreModel(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)); }
              toMap(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c));
              { toMapLemmas(Node(l, k, v, TRBInsert(Some(k), r, rt, k', v'), c)); }
              toMap(l) + map[k := v] + toMap(TRBInsert(Some(k), r, rt, k', v'));
              { TRBInsertModel(Some(k), r, rt, k', v'); }
              toMap(l) + map[k := v] + toMap(r)[k' := v'];
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          }
        } else if k' < k {
          if l.Thread? {
            RestoreSpec(Node(Node(Thread(fromThread(l)), k', v', Thread(k), Red), k, v, r, c));
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Node(Node(Thread(fromThread(l)), k', v', Thread(k), Red), k, v, r, c));
              toMap(Node(Thread(fromThread(l)), k', v', Thread(k), Red)) + map[k := v] + toMap(r);
              { toMapLemmas(Node(Thread(fromThread(l)), k', v', Thread(k), Red)); }
              (map[] + map[k' := v'] + map[]) + map[k := v] + toMap(r);
              map[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          } else {
            TRBInsertSpec(lt, l, Some(k), k', v');
            calc == {
              toMap(TRBInsert(lt, Node(l, k, v, r, c), rt, k', v'));
              toMap(Restore(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)));
              { RestoreModel(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)); }
              toMap(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c));
              { toMapLemmas(Node(TRBInsert(lt, l, Some(k), k', v'), k, v, r, c)); }
              toMap(TRBInsert(lt, l, Some(k), k', v')) + map[k := v] + toMap(r);
              { TRBInsertModel(lt, l, Some(k), k', v'); }
              toMap(l)[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k' := v'] + map[k := v] + toMap(r);
              toMap(l) + map[k := v] + toMap(r) + map[k' := v'];
              toMap(t) + map[k' := v'];
            }
          }
        } else {
        }
      }
    }
  }
  */

  lemma TRBInsertRootSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(TRBInsertRoot(t, k', v'))
    ensures SearchTree(TRBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertSpec(Child(Empty), t, Child(Empty), k', v');
  }

  lemma TRBInsertRootThreaded(t: rbtree, k': K, v': V)
    decreases t
    requires ThreadedTreeRoot(t)
    ensures ThreadedTreeRoot(TRBInsertRoot(t, k', v'))
  {
    TRBInsertThreaded(Child(Empty), t, Child(Empty), k', v');
  }

  lemma TRBInsertRootModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    requires SearchTree(TRBInsertRoot(t, k, v))
    ensures toMap(t)[k := v] == toMap(TRBInsertRoot(t, k, v))
/*
  {
    TRBInsertModel(Nothing, t, Nothing, k, v);
  }
  */
}