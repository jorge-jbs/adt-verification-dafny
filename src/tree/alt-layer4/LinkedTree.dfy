include "../../../src/tree/alt-layer4/RBTree.dfy"
include "../../../src/tree/alt-layer4/Tree.dfy"
include "../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../src/tree/alt-layer4/TNode.dfy"
include "../../../src/tree/alt-layer4/LinkedTree/SInsert.dfy"
include "../../../src/tree/alt-layer4/LinkedTree/RBInsert.dfy"
//include "../../../src/MUtils.dfy"

module LinkedTree {
  import opened TNode
  import RB = RBTree
  import opened T = Tree
  import opened KeyValue
  import opened SInsert
  import opened RBInsert

  class LinkedTree {
    var root: TNode?;
    ghost var skeleton: tree<TNode>;

    function Repr(): set<object>
      reads this
    {
      elems(skeleton)
    }

    predicate Valid()
      reads this, Repr()
    {
      ValidRec(root, skeleton)
    }

    predicate SearchTree()
      reads this, Repr()
      requires Valid()
    {
      SearchTreeRec(skeleton)
    }

    function TreeModel(): RB.rbtree
      reads this, elems(skeleton)
    {
      TreeModelRec(skeleton)
    }

    function MapModel(): map<K, V>
      reads this, elems(skeleton)
      requires Valid()
      requires SearchTree()
    {
      RB.model(TreeModel())
    }

    method Insert(k: K, v: V)
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
      root, skeleton, z := SInsertRec(root, skeleton, k, v);
      RB.SInsertSpec(old(TreeModelRec(skeleton)), k, v);
      RB.SInsertModel(old(TreeModelRec(skeleton)), k, v);
    }

    predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      RB.RedBlackTreeRoot(TreeModelRec(skeleton))
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
      RB.RBInsertRootSpec(old(TreeModelRec(skeleton)), k, v);
      RB.RBInsertRootModel(old(TreeModelRec(skeleton)), k, v);
    }
  }
}