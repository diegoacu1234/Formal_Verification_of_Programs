//This is a Dafny program that contains the solutions to the exercises in "Getting Started with Dafny: A Guide".

//Exercise 0 Write a method Max that takes two integer parameters and returns their maximum. Add appropriate annotations and make sure your code verifies.

method Max(a:int,b:int) returns (m:int)
  ensures m == a <==> a >= b
  ensures m == b <==> b >= a
{
  if (a>=b){
    m := a;
  }
  else{
    m := b;
  }
}

//Exercise 1 Write a test method that calls your Max method from Exercise 0 and then asserts something about the

method TestMax()
{
  var res := Max(1,2);
  assert res == 2;
}

/* Exercise 2 Using a precondition, change Abs to say it can only be called on negative values.
Simplify the body of Abs into just one assignment statement and make sure the method still verifies */

method Abs(x:int) returns (y:int)
  requires x < 0
  ensures y == -x

{
  y := -x;
}

/* Exercise 3 Keeping the postconditions of Abs the same as above, change the body of Abs
to y := x + 2;. What precondition do you need to annotate the method with in order
for the verification to go through? And what precondition do you need if the body is
y := x + 1;? What does that precondition say about calling the method? */

method Abs'(x:int) returns (y:int)
  requires x == -1
  ensures y==-x
{
  y := x + 2;
}

/* Exercise 4 Write a function max that returns the larger of two given integer parameters. 
Write a test method that uses an assert statement to check some property of the value of
max on some arguments (for example, 34 < max(21,55) or max(21,55) == max(55,21)).*/

function max(a:int,b:int) : int
  ensures max(a,b) == a ==> a >= b
  ensures max(a,b) == b ==> b >= a
{
  if a >= b then a else b
}

method TestMax2()
{
  assert 34 < max(21,55);
  assert max(21,55) == max(55,21);
}

/* Exercise 5 Change the test method in Exercise 4 to put the result of max into a local
variable and then use an assert statement to check some property of that local variable. 
Dafny will reject this program, because you’re calling max from real code. Fix this
problem using a function method.
*/
function  max'(a:int,b:int) : int
{
  if a >= b then a else b
}

method TestMax3()
{
  var res := max(21,55);
  assert res == 55;
  assert res == max(55,21);
}

/*Exercise 9 The ComputeFib method above is more complicated than necessary. Write
a simpler program by not introducing a as the Fibonacci number that precedes b, but
instead introducing a variable c that that succeeds b. Verify that your program is correct.*/

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if (n == 0) { return 0; }
  var i := 1;
  var a := 0;
  b := 1;
  while (i < n)
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

/*Exercise 12 Write a method that takes an integer array, which it requires to have at least
one element, and returns an index to the maximum of the array’s elements. Annotate the
method with pre- and postconditions that state the intent of the method, and annotate its
body with loop invariants to verify it.
*/
method MaxArray(l:array<int>) returns (m:int)
  requires l.Length > 0
  ensures 0 <= m < l.Length
  ensures forall i :: 0 <= i < l.Length ==> l[m] >= l[i]
{
  m := 0;
  var i := 1;
  while (i < l.Length)
    invariant 0 <= i <= l.Length
    invariant 0 <= m < l.Length
    invariant forall j :: 0 <= j < i ==> l[m] >= l[j]
    decreases l.Length - i
  {
    if l[i] > l[m]{
      m := i;
    }
    i := i + 1;
  }
}

/*Exercise 13 To get practice with quantifiers, modify the definition of function sorted so
that it returns true only when the array is sorted and all its elements are distinct.*/
function sorted'(a: array<int>) : bool
  requires a.Length > 0
  reads a
{
  (forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]) && (forall j, k :: 0 <= j < k < a.Length ==> a[j] != a[k])
}

