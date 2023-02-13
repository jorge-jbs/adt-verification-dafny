include "../../../src/MUtils.dfy"

module RBTreeData {

  import opened Utils

  type K = int
  type V = int

  datatype Color = Red | Black

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
        assume false;
        assert preorder(t) == [(k, v)] + preorder(l) + preorder(r);
        assume false;
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
          assume false;
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

  function method BlackHeight(sk: rbtree): nat
  {
    match sk {
      case Empty() => 0
      case Node(l, k, v, r, c) =>
        if c.Black? then
          1 + max(BlackHeight(l), BlackHeight(r))
        else
          max(BlackHeight(l), BlackHeight(r))
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

  function method NegColor(c: Color): Color
  {
    match c {
      case Black => Red
      case Red => Black
    }
  }

  function method FlipColors(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
  {
    Node(
      Node(t.left.left, t.left.key, t.left.value, t.left.right, NegColor(t.left.color)),
      t.key,
      t.value,
      Node(t.right.left, t.right.key, t.right.value, t.right.right, NegColor(t.right.color)),
      NegColor(t.color)
    )
  }

  function method RotateLeft(t: rbtree): rbtree
    requires t.Node?
    requires t.right.Node?
  {
    Node(
      Node(t.left, t.key, t.value, t.right.left, Red),
      t.right.key,
      t.right.value,
      t.right.right,
      t.color
    )
  }

  function method RotateRight(t: rbtree): rbtree
    requires t.Node?
    requires t.left.Node?
  {
    Node(
      t.left.left,
      t.left.key,
      t.left.value,
      Node(t.left.right, t.key, t.value, t.right, Red),
      t.color
    )
  }

  function method isRed(t: rbtree): bool
  {
    t.Node? && t.color.Red?
  }

  function method isBlack(t: rbtree): bool
  {
    t.Node? && t.color.Black?
  }

  function method Restore(t: rbtree): rbtree
    requires t.Node?
  {
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
    if isRed(t''.left) && isRed(t''.right) then
      FlipColors(t'')
    else
      t''
  }

  function method RBInsert(t: rbtree, k': K, v': V): rbtree
  {
    match t {
      case Empty => Node(Empty, k', v', Empty, Red)
      case Node(l, k, v, r, c) =>
        if k < k' then
          Restore(Node(l, k, v, RBInsert(r, k', v'), c))
        else if k' < k then
          Restore(Node(RBInsert(l, k', v'), k, v, r, c))
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

  function method RBInsertRoot(t: rbtree, k: K, v: V): rbtree
  {
    BlackenRoot(RBInsert(t, k, v))
  }

  lemma FlipColorsSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.right.Node?
    requires SearchTree(t)
    requires RedBlackTree(t)
    ensures keys(t) == keys(FlipColors(t))
    ensures SearchTree(FlipColors(t))
    ensures RedBlackTree(t)
  {}

  lemma RotateLeftSpec(t: rbtree)
    requires t.Node?
    requires t.right.Node?
    requires t.right.color.Red?
    requires SearchTree(t)
    requires RedBlackTree(t)
    ensures keys(t) == keys(RotateLeft(t))
    ensures SearchTree(RotateLeft(t))
    ensures RedBlackTree(t)
  {}

  lemma RotateRightSpec(t: rbtree)
    requires t.Node?
    requires t.left.Node?
    requires t.left.color.Red?
    requires SearchTree(t)
    requires RedBlackTree(t)
    ensures keys(t) == keys(RotateRight(t))
    ensures SearchTree(RotateRight(t))
    ensures RedBlackTree(t)
  {}

  lemma {:verify false} RestoreSpec(t: rbtree)
    requires t.Node?
    requires SearchTree(t)
    //requires RedBlackTree(t)
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

    ensures keys(t) == keys(Restore(t))
    ensures SearchTree(Restore(t))
    ensures RedBlackTree(Restore(t))

    ensures BlackHeight(Restore(t)) == BlackHeight(t)
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures isRed(t) ==> isRed(Restore(t))
    ensures isRed(Restore(t)) && isRed(Restore(t).left) ==>
      isRed(t) && (isRed(t.left) || isRed(t.right))
    ensures isRed(Restore(t)) && isBlack(t) ==>
      || (isRed(t.left) && isRed(t.right))
      || (isRed(t.left) && isRed(t.left.left))
  {
    /*
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
      assert !(
        && isRed(t')
        && isRed(t'.left)
        && isRed(t'.left.left));
      assert RedBlackTree(t'.right);
      assert t'.left.right == t.right.left;
      assert t'.left.right.Node? ==>
        t'.left.right.color == t.right.left.color;
      assert !isRed(t'.left.right) || (
        && isBlack(t)
        && isRed(t.left)
        && isRed(t.right)
        && isRed(t.right.left)
      );
    } else {
      assert RedBlackTree(t'.left);
      assert RedBlackTree(t'.right);
    }

    /*
    assert !(
      && isRed(t')
      && isRed(t'.left)
      && isRed(t'.right));

    assert !isRed(t'.right);
    assert RedBlackTree(t'.right);
    if t'.left.Node? {
      assert RedBlackTree(t'.left.left);
      assert RedBlackTree(t'.left.right);
    }
    */

    if isRed(t'.left) && isRed(t'.left.left) {
      assert isRed(t''.left);
      assert isRed(t''.right);
      assert !isRed(t'');
      assert RedBlackTree(t''.right);
      assert RedBlackTree(t''.left);
    } else {
      assert RedBlackTree(t''.right);
      if t''.left.Node? {
        assert RedBlackTree(t''.left.left);
        assert RedBlackTree(t''.left.right);
        assert BlackHeight(t''.left.left) == BlackHeight(t''.left.right);
        assert (t''.left.left.Node? && t''.left.left.color.Red? && t''.left.left.left.Node? ==> t''.left.left.left.color.Black?);
        assert (t''.left.right.Node? ==> t''.left.right.color.Black?) by {
          if t''.left.right.Node? {
            assert t''.left.right == t''.left.right;
            assert !isRed(t''.left.right);
          }
        }
      }
    }

    assert BlackHeight(t''') == BlackHeight(t);
    assert RedBlackTree(t''') by {
      assert t'''.right.Node? ==> t'''.right.color.Black? by {
        assert !isRed(t'''.right);
      }
      assert t'''.left.Node? && t'''.left.color.Red? && t'''.left.left.Node?
          ==> t'''.left.left.color.Black? by {
        if t'''.left.Node? {
          assert !(isRed(t'''.left) && isRed(t'''.left.left));
        }
      }
      assert BlackHeight(t'''.left) == BlackHeight(t'''.right);
      assert RedBlackTree(t'''.left);
      assert RedBlackTree(t'''.right);
    }
    */
    //assume false;
  }

  lemma RBInsertSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTree(t)
    requires !(isRed(t) && isRed(t.left))
    ensures isBlack(t) && isRed(Restore(t)) ==>
      !isRed(Restore(t).left)
    ensures keys(t) + {k'} == keys(RBInsert(t, k', v'))
    ensures SearchTree(RBInsert(t, k', v'))
    ensures RedBlackTree(RBInsert(t, k', v'))
    ensures BlackHeight(t) == BlackHeight(RBInsert(t, k', v'))
  {
    match t {
      case Empty => {
      }
      case Node(l, k, v, r, c) => {
        if k < k' {
          RBInsertSpec(l, k, v);
          RestoreSpec(Node(l, k, v, RBInsert(r, k', v'), c));
        } else if k' < k {
          RBInsertSpec(r, k, v);
          RestoreSpec(Node(RBInsert(l, k', v'), k, v, r, c));
        } else {
        }
      }
    }
  }

  lemma {:verify false} RBInsertModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires SearchTree(RBInsert(t, k, v))
    ensures model(t)[k := v] == model(RBInsert(t, k, v))

  lemma RBInsertRootSpec(t: rbtree, k': K, v': V)
    requires SearchTree(t)
    requires RedBlackTreeRoot(t)
    ensures keys(t) + {k'} == keys(RBInsert(t, k', v'))
    ensures SearchTree(RBInsertRoot(t, k', v'))
    ensures RedBlackTreeRoot(RBInsertRoot(t, k', v'))
  {
    RBInsertSpec(t, k', v');
  }

  lemma RBInsertRootModel(t: rbtree, k: K, v: V)
    requires SearchTree(t)
    requires SearchTree(RBInsertRoot(t, k, v))
    ensures model(t)[k := v] == model(RBInsertRoot(t, k, v))
  {
    RBInsertModel(t, k, v);
  }
}
