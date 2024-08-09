
function not(b: bool) : bool
  ensures not(b) == true <==> b == false
  ensures not(b) == false <==> b == true
{
  if b then false else true
}

function isEvenRecursive(n:nat) :bool
  ensures isEvenRecursive(n) == true <==> n % 2 == 0
  ensures isEvenRecursive(n) == false <==> n % 2 != 0
{
  match n
  {
    case 0 => true
    case _ => not(isEvenRecursive(n-1))
  }
}

function doubleNegative(b: bool) : bool
  ensures doubleNegative(b) == b
{
  not(not(b))
}

function deMorganAnd(a: bool, b: bool) : bool
  ensures deMorganAnd(a, b) == not(a) || not(b)
{
  not(a && b)
}


