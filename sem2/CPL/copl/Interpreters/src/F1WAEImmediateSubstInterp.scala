object F1WAEImmediateSubstInterp extends App {
  sealed abstract class F1WAE
  case class Num(n: Int) extends F1WAE
  case class Add(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class Sub(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class With(name: Symbol, namedExpr: F1WAE, body: F1WAE) extends F1WAE
  case class Id(name: Symbol) extends F1WAE
  case class App(funName: Symbol, arg: F1WAE) extends F1WAE

  case class FunDef(argName: Symbol, body: F1WAE)

  def subst(expr: F1WAE, substId: Symbol, value: F1WAE): F1WAE = expr match {
    case Num(n) => expr

    case Add(lhs, rhs) =>
      Add(subst(lhs, substId, value), subst(rhs, substId, value))

    case Sub(lhs, rhs) =>
      Sub(subst(lhs, substId, value), subst(rhs, substId, value))

    case With(boundId, namedExpr, boundBody) => {
      val substNamedExpr = subst(namedExpr, substId, value)
      if (boundId == substId)
        With(boundId, substNamedExpr, boundBody)
      else
        With(boundId, substNamedExpr, subst(boundBody, substId, value))
    }

    case Id(name) => {
      if (substId == name) value
      else expr
    }

    case App(funName, argExpr) => App(funName, subst(argExpr, substId, value))
  }

  def interp(expr: F1WAE, funDefs: Map[Symbol, FunDef]): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => interp(lhs, funDefs) + interp(rhs, funDefs)
    case Sub(lhs, rhs) => interp(lhs, funDefs) - interp(rhs, funDefs)
    case With(boundId, namedExpr, boundBody) => {
      val body = subst(boundBody, boundId, Num(interp(namedExpr, funDefs)))
      interp(body, funDefs)
    }
    case Id(name) => sys.error("found unbound id " + name)
    case App(funName, argExpr) => funDefs(funName) match {
      case FunDef(argName, body) => {
        interp(subst(body, argName, Num(interp(argExpr, funDefs))), funDefs)
      }
    }
  }

  
  // some assertions on the interpreter
  import scala.language.implicitConversions

  implicit def symbolToExpr(symbol: Symbol) = Id(symbol)
  implicit def intToExpr(n: Int) = Num(n)

  val funDefs = Map(
    'f -> FunDef('n, App('g, Add('n, 5))),
    'g -> FunDef('n, Sub('n, 1)))

  assert(interp(App('f, 5), funDefs) == 9)

  val funDefs2 = Map(
    'f -> FunDef('y, Sub('y, 1)),
    'g -> FunDef('y, Sub('y, 1)),
    'f -> FunDef('x, App('g, Add('x, 3))))

  assert(interp(App('f, 10), funDefs2) == 12)

  assert(interp(With('x, 3, Add(With('x, 4, Add('x, 3)), 'x)), Map()) == 10)

  try {
    interp(With('n, 5, App('f, 10)), Map('f -> FunDef('x, 'n)))
    assert(false)
  } catch { case e: Exception => Unit }
}