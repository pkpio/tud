object F1WAEStaticInterp extends App {
  sealed abstract class F1WAE
  case class Num(n: Int) extends F1WAE
  case class Add(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class Sub(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class With(name: Symbol, namedExpr: F1WAE, body: F1WAE) extends F1WAE
  case class Id(name: Symbol) extends F1WAE
  case class App(funName: Symbol, arg: F1WAE) extends F1WAE

  case class FunDef(argName: Symbol, body: F1WAE)

  type FunDefs = Map[Symbol, FunDef]
  type Emv = Map[Symbol, Int]

  def interp(expr: F1WAE, funDefs: FunDefs, env: Emv): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => {
      interp(lhs, funDefs, env) + interp(rhs, funDefs, env)
    }
    case Sub(lhs, rhs) => {
      interp(lhs, funDefs, env) - interp(rhs, funDefs, env)
    }
    case With(boundId, namedExpr, boundBody) => {
      val newEmv = env + (boundId -> interp(namedExpr, funDefs, env))
      interp(boundBody, funDefs, newEmv)
    }
    case Id(name) => env(name)
    case App(funName, argExpr) => funDefs(funName) match {
      case FunDef(argName, body) => {
        val funEmv = Map(argName -> interp(argExpr, funDefs, env))
        interp(body, funDefs, funEmv)
      }
    }
  }

  
  // some assertions on the interpreter
  import scala.language.implicitConversions

  implicit def symbolToF1WAE(symbol: Symbol) = Id(symbol)
  implicit def intToF1WAE(n: Int) = Num(n)

  val funDefs = Map(
    'f -> FunDef('n, App('g, Add('n, 5))),
    'g -> FunDef('n, Sub('n, 1)))

  assert(interp(App('f, 5), funDefs, Map()) == 9)

  val funDefs2 = Map(
    'f -> FunDef('y, Sub('y, 1)),
    'g -> FunDef('y, Sub('y, 1)),
    'f -> FunDef('x, App('g, Add('x, 3))))

  assert(interp(App('f, 10), funDefs2, Map()) == 12)

  assert(interp(
    With('x, 3, Add(With('x, 4, Add('x, 3)), 'x)), Map(), Map()) == 10)

  try {
    interp(With('n, 5, App('f, 10)), Map('f -> FunDef('x, 'n)), Map())
    assert(false)
  } catch { case e: Exception => Unit }

  try {
    interp(App('f, 4), Map('f -> FunDef('y, Add('x, 'y))), Map())
    assert(false)
  } catch { case e: Exception => Unit }
}