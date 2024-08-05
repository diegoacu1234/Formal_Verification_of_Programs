datatype Tree<T> = Node(left: Tree<T>, value: T, right: Tree<T>) | Leaf

function Mirror<T>(t: Tree<T>) : Tree<T>
  decreases t
  ensures Mirror(t) == Leaf ==> t == Leaf
  ensures Mirror(t) != Leaf ==> t != Leaf && Mirror(t) == Node(Mirror(t.right), t.value, Mirror(t.left))
{
  match t {
    case Leaf => t
    case Node(left, value, right) => Node(Mirror(right), value, Mirror(left))
  }
}

function Size<T>(t: Tree<T>) : nat
  ensures Size(t) == 0 ==> t == Leaf
  ensures Size(t) > 0 ==> t != Leaf && Size(t) == (1 + Size(t.left) + Size(t.right))
  decreases t
{
  match t {
    case Leaf => 0
    case Node(left, _, right) => 1 + Size(left) + Size(right)
  }
}

function max(a: nat, b: nat) : nat
  ensures max(a, b) == a ==> a >= b
  ensures max(a, b) == b ==> b >= a
{
  if a >= b then a else b
}

function Depth<T>(t: Tree<T>) : nat
  ensures Depth(t) == 0 ==> t == Leaf
  ensures Depth(t) > 0 ==> t != Leaf && Depth(t) == 1 + max(Depth(t.left), Depth(t.right))
  decreases t
{
  match t {
    case Leaf => 0
    case Node(left, _, right) => 1 + max(Depth(left), Depth(right))
  }
}

method Test()
{
  var t := Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf));
  assert Depth(t) == 2;
  assert Size(t) == 3;
  assert Mirror(t) == Node(Node(Leaf, 3, Leaf), 2, Node(Leaf, 1, Leaf));
  assert Mirror(Mirror(t)) == t;
}