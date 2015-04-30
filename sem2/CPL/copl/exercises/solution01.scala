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

object Factorial {
  def factorial(n: Int): Int = n match {
    case 0 => 1
    case m if m > 0 => m * factorial(m - 1)
  }

  def factorialB(n: Int): Int = {
    if (n < 0)
      throw new IllegalArgumentException(s"negative value given: $n")

    var res = 1
    for (i <- 1 to n)
      res = res * i
    res
  }

  def factorialC(n: Int): Int = {
    if (n < 0)
      throw new IllegalArgumentException(s"negative value given: $n")

    (1 to n).foldLeft(1)(_ * _)
  } 

  def demo() {
    for (i <- 0 to 5; f <- List(factorial(_), factorialB(_), factorialC(_))) {
        println(f(i));
    }
  }      
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
case class Not(e: BE) extends BE

abstract class BEValue
case object T extends BEValue
case object F extends BEValue

object InterpBE {
  def interp(be: BE): BEValue =
    be match {
      case True => T        
      case False => F
      case And(e1, e2) =>
      	(interp(e1), interp(e2)  ) match {
      		case (T, T) => T
       		case _ => F
       	}        	
        case Not(e) =>        
          interp(e) match {
            case T => F
            case F => T
        }
      }       

  val e = And(True, False)
}


/*
  Task 3: Scala code style

  Take a look at Scala coding styleguide
  (http://docs.scala-lang.org/style/overview.html).
  Refactor your code above accordingly.

*/

