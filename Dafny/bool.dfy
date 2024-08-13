function not(b: bool) : bool
  ensures not(b) == true <==> b == false
  ensures not(b) == false <==> b == true
{
  if b then false else true
}

function IsEvenRecursive(n:nat) :bool
  ensures IsEvenRecursive(n) == true <==> n % 2 == 0
  ensures IsEvenRecursive(n) == false <==> n % 2 != 0
{
  match n
  {
    case 0 => true
    case _ => not(IsEvenRecursive(n-1))
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


