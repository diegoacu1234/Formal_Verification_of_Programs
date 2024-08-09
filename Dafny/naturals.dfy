datatype N = O | S (n: N)

function not(b: bool) : bool
{
  if b then false else true
}

//Using nat
function isEven(n:nat) :bool
  ensures isEven(n) == true <==> n % 2 == 0
  ensures isEven(n) == false <==> n % 2 != 0
  decreases n
{
  match n
  {
    case 0 => true
    case _ => not(isEven(n-1))
  }
}

//Using N
function isEven'(n:N) :bool
  decreases n
{
  match n
  {
    case O => true
    case S(n') => not(isEven'(n'))
  }
}

function sum(m:N,n:N) : N
  decreases m
{
  match m
  {
    case O => n
    case S(x) => S(sum(x,n))
  }
}

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
    decreases n - i
  {
    a, b := b, a + b;
    i := i + 1;
  }
}