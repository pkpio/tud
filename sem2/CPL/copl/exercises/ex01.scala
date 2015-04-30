/*
  Exercise 01, April 17
*/


/* 
  Task 1: Factorial function in Scala

  Write one factorial function in each of the following styles.
    a) recursion, no mutation
    b) for loop with accumulator variable
    c) folding, no mutation
*/

object FactorialA {
  def factorial(n: Int): Int = ??? //implement this
}


/*
  Task 2: Interpreter for Boolean expressions

  Start by defining the abstract syntax, then write the interpreter
  itself.
*/

abstract class BE
case object True extends BE
case object False extends BE
case class And(e1: BE, e2: BE) extends BE
// more here

abstract class BEValue
// more here

object InterpBE {
  def interp(be: BE) : BEValue =
    be match {
      case True => ??? //implement this
    }

  val e = And(True, False)
}


/*
  Task 3: Scala code style

  Take a look at Scala coding styleguide
  (http://docs.scala-lang.org/style/overview.html).
  Refactor your code above accordingly.

*/

