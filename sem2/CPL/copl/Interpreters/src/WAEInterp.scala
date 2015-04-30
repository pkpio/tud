import scala.language.implicitConversions

object WAEInterp extends App {
  sealed abstract class WAE
  case class Num(n: Int) extends WAE
  case class Add(lhs: WAE, rhs: WAE) extends WAE
  case class Sub(lhs: WAE, rhs: WAE) extends WAE
  case class Let(name: Symbol, namedExpr: WAE, body: WAE) extends WAE
  case class Id(name: Symbol) extends WAE

  def subst(expr: WAE, substId: Symbol, value: WAE): WAE = expr match {
    case Num(n) => expr

    case Add(lhs, rhs) =>
      Add(subst(lhs, substId, value), subst(rhs, substId, value))

    case Sub(lhs, rhs) =>
      Sub(subst(lhs, substId, value), subst(rhs, substId, value))

    case Let(boundId, namedExpr, boundExpr) => {
      val substNamedExpr = subst(namedExpr, substId, value)
      if (boundId == substId)
        Let(boundId, substNamedExpr, boundExpr)
      else
        Let(boundId, substNamedExpr, subst(boundExpr, substId, value))
    }

    case Id(name) => {
      if (substId == name) value
      else expr
    }
  }

  def eagerCalc(expr: WAE): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => eagerCalc(lhs) + eagerCalc(rhs)
    case Sub(lhs, rhs) => eagerCalc(lhs) - eagerCalc(rhs)
    case Let(boundId, namedExpr, boundExpr) => {
      eagerCalc(subst(boundExpr, boundId, Num(eagerCalc(namedExpr))))
    }
    case Id(name) => sys.error("found unbound id " + name)
  }

  def lazyCalc(expr: WAE): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => lazyCalc(lhs) + lazyCalc(rhs)
    case Sub(lhs, rhs) => lazyCalc(lhs) - lazyCalc(rhs)
    case Let(boundId, namedExpr, boundExpr) => {
      lazyCalc(subst(boundExpr, boundId, namedExpr))
    }
    case Id(name) => sys.error("found unbound id " + name)
  }

  
  // assertions on the interpreter
  implicit def symbolToWAE(symbol: Symbol) = Id(symbol)
  implicit def intToWAE(n: Int) = Num(n)

  assert(eagerCalc(Let('x, Add(5, 5), Add('x, 'x))) == 20)
  assert(eagerCalc(Let('x, 5, Add('x, 'x))) == 10)
  assert(eagerCalc(Let('x, Add(5, 5),
    Let('y, Sub('x, 3), Add('y, 'y)))) == 14)
  assert(eagerCalc(Let('x, 5, Let('y, Sub('x, 3), Add('y, 'y)))) == 4)
  assert(eagerCalc(Let('x, 5, Add('x, Let('x, 3, 10)))) == 15)
  assert(eagerCalc(Let('x, 5, Add('x, Let('x, 3, 'x)))) == 8)
  assert(eagerCalc(Let('x, 5, Add('x, Let('y, 3, 'x)))) == 10)
  assert(eagerCalc(Let('x, 5, Let('y, 'x, 'y))) == 5)
  assert(eagerCalc(Let('x, 5, Let('x, 'x, 'x))) == 5)
  try {
    eagerCalc(Let('x, Add(3, 'z), Let('y, 100, 'y)))
    assert(false)
  } catch {
    case e: Exception => assert(true)
  }

  assert(lazyCalc(Let('x, Add(5, 5), Add('x, 'x))) == 20)
  assert(lazyCalc(Let('x, 5, Add('x, 'x))) == 10)
  assert(lazyCalc(
      Let('x, Add(5, 5), Let('y, Sub('x, 3), Add('y, 'y)))) == 14)
  assert(lazyCalc(Let('x, 5, Let('y, Sub('x, 3), Add('y, 'y)))) == 4)
  assert(lazyCalc(Let('x, 5, Add('x, Let('x, 3, 10)))) == 15)
  assert(lazyCalc(Let('x, 5, Add('x, Let('x, 3, 'x)))) == 8)
  assert(lazyCalc(Let('x, 5, Add('x, Let('y, 3, 'x)))) == 10)
  assert(lazyCalc(Let('x, 5, Let('y, 'x, 'y))) == 5)
  assert(lazyCalc(Let('x, 5, Let('x, 'x, 'x))) == 5)
  assert(lazyCalc(Let('x, Add(3, 'z), Let('y, 100, 'y))) == 100)
}