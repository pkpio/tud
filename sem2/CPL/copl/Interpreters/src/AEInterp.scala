
object AEInterp extends App {
  sealed abstract class AE
  case class Num(n: Int) extends AE
  case class Add(lhs: AE, rhs: AE) extends AE
  case class Sub(lhs: AE, rhs: AE) extends AE

  def interp(expr: AE): Int = expr match {
    case Num(n) => n
    case Add(lhs, rhs) => interp(lhs) + interp(rhs)
    case Sub(lhs, rhs) => interp(lhs) - interp(rhs)
  }

  implicit def intToAE(n: Int): AE = Num(n)
  
  assert(interp(Add(Num(5), Add(Num(2), Num(3)))) == 10)
  assert(interp(Add(Num(5), Sub(Num(2), Num(3)))) == 4)
  assert(interp(Sub(Num(5), Sub(Num(2), Num(3)))) == 6)

}