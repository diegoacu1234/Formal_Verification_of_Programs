datatype List<T> = Cons(head: T, tail: List<T>) | Nil

function Length<T>(l: List<T>) : nat
  ensures Length(l) == 0 ==> l == Nil
  ensures Length(l) > 0 ==> l != Nil && Length(l) == 1 + Length(l.tail)
  decreases l
{
  match l {
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
  }
}

method ComputeLength<T>(l:List<T>) returns (n:nat)
  ensures n == Length(l)
{
  n := 0;
  var t := l;
  while t != Nil
    invariant n + Length(t) == Length(l)
    decreases t
  {
    n := n + 1;
    t := t.tail;
  }
}


function Append<T>(l1: List<T>, l2: List<T>) : List<T>
  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)
  decreases l1
{
  match l1 {
    case Nil => l2
    case Cons(head, tail) => Cons(head, Append(tail, l2))
  }
}

function Reverse<T>(l: List<T>) : List<T>
  ensures Length(Reverse(l)) == Length(l)
  decreases l
{
  match l {
    case Nil => Nil
    case Cons(head, tail) => Append(Reverse(tail), Cons(head, Nil))
  }
}


function min(a: nat, b: nat) : nat
  ensures min(a, b) == a ==> a <= b
  ensures min(a, b) == b ==> b <= a
{
  if a <= b then a else b
}

method computeMinArray(l: array<nat>) returns (m:nat)
  requires l.Length > 0
  ensures forall i :: 0 <= i < l.Length ==> m <= l[i]
  decreases l
{
  m := l[0];
  var i := 1;
  while i < l.Length
    invariant 0 <= i <= l.Length
    invariant forall j :: 0 <= j < i ==> m <= l[j]
    decreases l.Length - i
  {
    m := min(m, l[i]);
    i := i + 1;
  }
}

function Zip<T1, T2>(l1: List<T1>, l2: List<T2>) : List<(T1, T2)>
  ensures Length(Zip(l1, l2)) == min(Length(l1), Length(l2))
  decreases l1, l2
{
  match l1 {
    case Nil => Nil
    case Cons(head1, tail1) =>
      match l2 {
        case Nil => Nil
        case Cons(head2, tail2) => Cons((head1, head2), Zip(tail1, tail2))
      }
  }
}

method Test()
{
  var l1 := Cons(1, Cons(2, Cons(3, Nil))); //[1, 2, 3]
  var l2 := Cons("a", Cons("b", Cons("c", Nil))); //["a", "b", "c"]
  var l3 := Cons(1, Cons(2, Nil)); //[1, 2]
  var l4 := Cons("a", Cons("b", Cons("c", Cons("d", Nil)))); //["a", "b", "c", "d"]
  assert Length(l1) == 3;
  assert Length(l2) == 3;
  assert Length(l3) == 2;
  assert Length(l4) == 4;
  assert Reverse(l1) == Cons(3, Cons(2, Cons(1, Nil)));
  assert Reverse(l2) == Cons("c", Cons("b", Cons("a", Nil)));
  assert Reverse(l3) == Cons(2, Cons(1, Nil));
  assert Reverse(l4) == Cons("d", Cons("c", Cons("b", Cons("a", Nil))));
  assert Zip(l1, l2) == Cons((1, "a"), Cons((2, "b"), Cons((3, "c"), Nil)));
  assert Zip(l3, l4) == Cons((1, "a"), Cons((2, "b"), Nil));
}