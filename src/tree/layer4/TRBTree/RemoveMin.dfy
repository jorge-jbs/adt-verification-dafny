include "../../../../src/tree/layer4/Color.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/UpdatePrev.dfy"

module TRBTree.RemoveMin {
  import opened Color
  import opened Base
  import opened UP = UpdatePrev

  function RemoveMinP(p: pointer): pointer
    requires p.Child?
    requires p.child.Node?
  {
    RemoveMin(p.child)
  }

  function RemoveMin(t: rbtree): pointer
    requires t.Node?
  {
    match t {
      case Node(l, k, v, r, c) =>
        if l.Thread? || l == Child(Empty) then
          UpdatePrevP(l, r)
        else
          Child(Node(l, k, v, r, c))
    }
  }
}
