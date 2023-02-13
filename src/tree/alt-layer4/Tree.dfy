include "../../../src/tree/alt-layer4/RBTreeData.dfy"
include "../../../src/tree/alt-layer4/TreeData.dfy"
include "../../../src/MUtils.dfy"

module Tree {
  import opened RB = RBTreeData
  import opened T = TreeData
  import opened Utils

  class TNode {
    var key: K;
    var value: V;
    var left: TNode?;
    var right: TNode?;
    var color: Color;

    constructor(l: TNode?, k: K, v: V, r: TNode?)
      ensures left == l
      ensures key == k
      ensures value == v
      ensures right == r
      ensures color == Black
    {
      key := k;
      value := v;
      left := l;
      right := r;
      color := Black;
    }

    constructor RedBlack(l: TNode?, k: K, v: V, r: TNode?, c: Color)
      ensures left == l
      ensures key == k
      ensures value == v
      ensures right == r
      ensures color == c
    {
      key := k;
      value := v;
      left := l;
      right := r;
      color := c;
    }

    constructor Leaf(k: K, v: V)
      ensures left == null
      ensures key == k
      ensures value == v
      ensures right == null
    {
      key := k;
      value := v;
      left := null;
      right := null;
      color := Black;
    }
  }

  class Tree {
    var root: TNode?;
    ghost var skeleton: tree<TNode>;

    function Repr(): set<object>
      reads this
    {
      elems(skeleton)
    }

    static predicate ValidRec(node: TNode?, sk: tree<TNode>)
      reads set x | x in elems(sk) :: x`left
      reads set x | x in elems(sk) :: x`right
    {
      match sk {
        case Empty => node == null
        case Node(l, x, r) =>
          && x == node
          && x !in elems(l)
          && x !in elems(r)
          && elems(l) !! elems(r)
          && ValidRec(node.left, l)
          && ValidRec(node.right, r)
      }
    }

    predicate Valid()
      reads this, Repr()
    {
      ValidRec(root, skeleton)
    }

    static function TreeModelRec(sk: tree<TNode>): rbtree
      reads elems(sk)
      ensures (set n | n in elems(sk) :: n.key) == keys(TreeModelRec(sk))
    {
      match sk {
        case Empty => RB.Empty
        case Node(l, n, r) => RB.Node(TreeModelRec(l), n.key, n.value, TreeModelRec(r), n.color)
      }
    }

    static predicate SearchTreeRec(sk: tree<TNode>)
      reads elems(sk)
    {
      RB.SearchTree(TreeModelRec(sk))
    }

    predicate SearchTree()
      reads this, Repr()
      requires Valid()
    {
      SearchTreeRec(skeleton)
    }

    function TreeModel(): rbtree
      reads this, elems(skeleton)
    {
      TreeModelRec(skeleton)
    }

    function MapModel(): map<K, V>
      reads this, elems(skeleton)
      requires Valid()
      requires SearchTree()
    {
      model(TreeModel())
    }

    static method {:verify false} InsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
        returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode: TNode)
      modifies set x | x in elems(sk) :: x`left
      modifies set x | x in elems(sk) :: x`right
      modifies set x | x in elems(sk) :: x`value

      requires ValidRec(node, sk)
      requires SearchTreeRec(sk)

      ensures ValidRec(newNode, newSk)
      ensures SearchTreeRec(newSk)
      ensures TreeModelRec(newSk) == SInsert(old(TreeModelRec(sk)), k, v)

      ensures elems(newSk) == elems(sk)+{insertedNode}
      ensures insertedNode.key == k && insertedNode.value == v
      ensures forall n | n in elems(sk) && old(n.key) != k ::
        n.key == old(n.key) && n.value == old(n.value)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-old(elems(sk)))
      ensures allocated(elems(newSk))
    {
      if node == null {
        newNode := new TNode(null, k, v, null);
        newSk := T.Node(T.Empty, newNode, T.Empty);
        insertedNode := newNode;
      } else {
        assert sk.data == node;
        newNode := node;
        if k == node.key {
          node.value := v;
          newSk := sk;
          insertedNode := node;
        } else if node.key < k {
          ghost var newSkRight;
          node.right, newSkRight, insertedNode := InsertRec(node.right, sk.right, k, v);
          newSk := T.Node(sk.left, node, newSkRight);
          /*
          assert TreeModelRec(newSkRight) == SInsert(old(TreeModelRec(sk.right)), k, v);
          assert TreeModelRec(sk.left) == old(TreeModelRec(sk.left));
          calc == {
            TreeModelRec(newSk);
            RB.Node(TreeModelRec(sk.left), node.key, node.value, TreeModelRec(newSkRight), node.color);
            RB.Node(TreeModelRec(sk.left), node.key, node.value, SInsert(old(TreeModelRec(sk.right)), k, v), node.color);
            SInsert(RB.Node(TreeModelRec(sk.left), node.key, node.value, old(TreeModelRec(sk.right)), node.color), k, v);
            SInsert(old(TreeModelRec(sk)), k, v);
          }
          assert TreeModelRec(newSk) == SInsert(old(TreeModelRec(sk)), k, v);
          */
          //assume false;
        } else if k < node.key {
          ghost var newSkLeft;
          node.left, newSkLeft, insertedNode := InsertRec(node.left, sk.left, k, v);
          newSk := T.Node(newSkLeft, node, sk.right);
          //assume false;
        } else {
          assert false;
        }
      }
    }

    method {:verify false} Insert(k: K, v: V)
      modifies this, Repr()
      requires Valid()
      requires SearchTree()
      ensures Valid()
      ensures SearchTree()
      ensures MapModel() == old(MapModel())[k := v]

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := InsertRec(root, skeleton, k, v);
      SInsertSpec(old(TreeModelRec(skeleton)), k, v);
      SInsertModel(old(TreeModelRec(skeleton)), k, v);
    }

    static function method isRed(node: TNode?): bool
      reads node
    {
      node != null && node.color.Red?
    }

    static lemma isRedProp(node: TNode?, sk: tree<TNode>)
      requires ValidRec(node, sk)
      ensures isRed(node) <==> RB.isRed(TreeModelRec(sk))
    {}

    static function method isBlack(node: TNode?): bool
      reads node
    {
      node != null && node.color.Black?
    }

    static function BlackHeight(sk: tree<TNode>): nat
      reads elems(sk)
    {
      RB.BlackHeight(TreeModelRec(sk))
    }

    static predicate RedBlackTreeRec(sk: tree<TNode>)
      reads elems(sk)
    {
      RB.RedBlackTree(TreeModelRec(sk))
    }

    predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      RB.RedBlackTreeRoot(TreeModelRec(skeleton))
    }

    // 67"
    static method FlipColors(node: TNode, ghost sk: tree<TNode>)
      modifies node`color, node.left`color, node.right`color

      requires ValidRec(node, sk)
      requires node.left != null
      requires node.right != null
      requires TreeModelRec(sk).left.Node?  /* redundant */
      requires TreeModelRec(sk).right.Node?  /* redundant */

      ensures ValidRec(node, sk)
      ensures TreeModelRec(sk) == RB.FlipColors(old(TreeModelRec(sk)))

      requires allocated(elems(sk))
      ensures allocated(elems(sk))
    {
      node.color := NegColor(node.color);
      node.left.color := NegColor(node.left.color);
      node.right.color := NegColor(node.right.color);
    }

    // 22"
    static method RotateLeft(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

      modifies node`color
      modifies node`right
      modifies node.right`left
      modifies node.right`color

      requires ValidRec(node, sk)
      requires node.right != null
      requires TreeModelRec(sk).right.Node?  /* redundant */

      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk) == RB.RotateLeft(old(TreeModelRec(sk)))
      ensures elems(newSk) == elems(sk)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-elems(sk))
      ensures allocated(elems(newSk))
    {
      newNode := node.right;
      node.right := newNode.left;
      newNode.left := node;
      newNode.color := node.color;
      node.color := Red;
      newSk := T.Node(T.Node(sk.left, node, sk.right.left), newNode, sk.right.right);
    }

    // 10"
    static method RotateRight(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

      modifies node`color
      modifies node`left
      modifies node.left`right
      modifies node.left`color

      requires ValidRec(node, sk)
      requires node.left != null
      requires TreeModelRec(sk).left.Node?  /* redundant */

      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk) == RB.RotateRight(old(TreeModelRec(sk)))
      ensures elems(newSk) == elems(sk)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-elems(sk))
      ensures allocated(elems(newSk))
    {
      newNode := node.left;
      node.left := newNode.right;
      newNode.right := node;
      newNode.color := node.color;
      node.color := Red;
      newSk := T.Node(sk.left.left, newNode, T.Node(sk.left.right, node, sk.right));
    }

    // 4"
    static method Restore(node: TNode, ghost sk: tree<TNode>)
      returns (newNode: TNode, ghost newSk: tree<TNode>)

      modifies set x | x in elems(sk) :: x`left
      modifies set x | x in elems(sk) :: x`right
      modifies set x | x in elems(sk) :: x`color

      requires ValidRec(node, sk)

      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk) == RB.Restore(old(TreeModelRec(sk)))
      ensures elems(newSk) == elems(sk)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-elems(sk))
      ensures allocated(elems(newSk))
    {
      ghost var t := TreeModelRec(sk);
      ghost var t' :=
        if RB.isRed(t.right) then
          RB.RotateLeft(t)
        else
          t;
      ghost var t'' :=
        if RB.isRed(t'.left) && RB.isRed(t'.left.left) then
          RB.RotateRight(t')
        else
          t';
      ghost var t''' :=
        if RB.isRed(t''.left) && RB.isRed(t''.right) then
          RB.FlipColors(t'')
        else
          t'';
      newNode := node;
      newSk := sk;

      if isRed(newNode.right) {
        newNode, newSk := RotateLeft(newNode, newSk);
      }

      assert TreeModelRec(newSk) == t';

      isRedProp(newNode.left, newSk.left);
      assert isRed(newNode.left) <==> RB.isRed(t'.left);
      if newNode.left != null {
        assert TreeModelRec(newSk.left.left) == t'.left.left;
        isRedProp(newNode.left.left, newSk.left.left);
        assert isRed(newNode.left.left) <==> RB.isRed(t'.left.left);
      }
      if isRed(newNode.left) && isRed(newNode.left.left) {
        newNode, newSk := RotateRight(newNode, newSk);
        assert TreeModelRec(newSk) == RB.RotateRight(t');
      }

      assert TreeModelRec(newSk) == t'';

      if isRed(newNode.left) && isRed(newNode.right) {
        FlipColors(newNode, newSk);
      }

      assert TreeModelRec(newSk) == t''';
    }

    // 4'41"
    static method RBInsertRec(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
      returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

      modifies set x | x in elems(sk) :: x`left
      modifies set x | x in elems(sk) :: x`right
      modifies set x | x in elems(sk) :: x`value
      modifies set x | x in elems(sk) :: x`color

      requires ValidRec(node, sk)
      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk) == RB.RBInsert(old(TreeModelRec(sk)), k, v)

      ensures elems(newSk) == elems(sk) + {insertedNode}
      ensures insertedNode.key == k && insertedNode.value == v
      ensures forall n | n in elems(sk) && old(n.key) != k ::
        n.key == old(n.key) && n.value == old(n.value)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-elems(sk))
      ensures allocated(elems(newSk))
    {
      if node == null {
        newNode := new TNode.RedBlack(null, k, v, null, Red);
        newSk := T.Node(T.Empty, newNode, T.Empty);
        insertedNode := newNode;
      } else {
        assert sk.data == node;
        newNode := node;
        if k == node.key {
          node.value := v;
          newSk := sk;
          insertedNode := node;
        } else if node.key < k {
          ghost var newSkRight;
          node.right, newSkRight, insertedNode := RBInsertRec(node.right, sk.right, k, v);
          newSk := T.Node(sk.left, node, newSkRight);
          newNode, newSk := Restore(newNode, newSk);
        } else if k < node.key {
          ghost var newSkLeft;
          node.left, newSkLeft, insertedNode := RBInsertRec(node.left, sk.left, k, v);
          newSk := T.Node(newSkLeft, node, sk.right);
          newNode, newSk := Restore(newNode, newSk);
        } else {
          assert false;
        }
      }
    }

    // 5"
    static method RBInsertRoot(node: TNode?, ghost sk: tree<TNode>, k: K, v: V)
      returns (newNode: TNode, ghost newSk: tree<TNode>, ghost insertedNode:TNode)

      modifies set x | x in elems(sk) :: x`left
      modifies set x | x in elems(sk) :: x`right
      modifies set x | x in elems(sk) :: x`value
      modifies set x | x in elems(sk) :: x`color

      requires ValidRec(node, sk)
      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk) == RB.RBInsertRoot(old(TreeModelRec(sk)), k, v)

      ensures elems(newSk) == elems(sk) + {insertedNode}
      ensures insertedNode.key == k && insertedNode.value == v
      ensures forall n | n in elems(sk) && old(n.key) != k ::
        n.key == old(n.key) && n.value == old(n.value)

      requires allocated(elems(sk))
      ensures fresh(elems(newSk)-elems(sk))
      ensures allocated(elems(newSk))
    {
      newNode, newSk, insertedNode := RBInsertRec(node, sk, k, v);
      newNode.color := Black;
    }

    // 26"
    method RBInsert(k: K, v: V)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures MapModel() == old(MapModel())[k := v]

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := RBInsertRoot(root, skeleton, k, v);
      RBInsertRootSpec(old(TreeModelRec(skeleton)), k, v);
      RBInsertRootModel(old(TreeModelRec(skeleton)), k, v);
    }
  }
}