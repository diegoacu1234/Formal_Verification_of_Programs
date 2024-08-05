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