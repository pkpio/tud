object F1WAEDynamicInterp extends App {
  sealed abstract class F1WAE
  case class Num(n: Int) extends F1WAE
  case class Add(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class Sub(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class With(name: Symbol, namedExpr: F1WAE, body: F1WAE) extends F1WAE
  case class Id(name: Symbol) extends F1WAE
  case class App(funName: Symbol, arg: F1WAE) extends F1WAE

  case class FunDef(argName: Symbol, body: F1WAE)

  type FunDefs = Map[Symbol, FunDef]
  type SubRep = Map[Symbol, Int]

  def interp(expr: F1WAE, funDefs: FunDefs, subRep: SubRep): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => {
      interp(lhs, funDefs, subRep) + interp(rhs, funDefs, subRep)
    }
    case Sub(lhs, rhs) => {
      interp(lhs, funDefs, subRep) - interp(rhs, funDefs, subRep)
    }
    case With(boundId, namedExpr, boundBody) => {
      val newSubRep = subRep + (boundId -> interp(namedExpr, funDefs, subRep))
      interp(boundBody, funDefs, newSubRep)
    }
    case Id(name) => subRep(name)
    case App(funName, argExpr) => funDefs(funName) match {
      case FunDef(argName, body) => {
        val funSubRep = subRep + (argName -> interp(argExpr, funDefs, subRep))
        interp(body, funDefs, funSubRep)
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

  assert(interp(With('n, 5, App('f, 10)),
    Map('f -> FunDef('x, 'n)), Map()) == 5)
}