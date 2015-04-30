import org.scalatest.FunSuite

import AEInterp._;

class AEInterpTest extends FunSuite {
  def testInterp(e: AE, v: Int) {
    test(s"interp $e")(assert(interp(e) == v))
  }
  
  testInterp(Num(5), 5)
  testInterp(Num(15), 15)
  
  testInterp(Add(1, 2), 3)
  testInterp(Add(5, 15), 20)
  testInterp(Add(Add(1, 2), Add(3, 4)), 10)
  
  testInterp(Sub(15, 5), 10)
  testInterp(Sub(Add(1, 2), 3), 0)
}