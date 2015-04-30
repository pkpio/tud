/**
 * Exercise 02, April 24
 */
object ex02 {
  /**
   * Task 1: Arithmetics
   *
   * 1) Write a recursive function 'sum' that sums up the elements of a list of numbers.
   */

  def sum(l: List[Int]): Int = l match {
    case Nil => 0
    case x :: xs => x + sum(xs)
  }

  /**
   * 2) Write a recursive function 'prod' that builds the product of the elements in list of numbers.
   */

  def prod(l: List[Int]): Int = l match {
    case Nil => 0
    case x :: xs => x * prod(xs)
  }

  /**
   * 3) Can you recognize similarities between 'sum' and 'prod'? Write a higher-order function 'fold' that
   *    abstracts over these similarities. Reimplement 'sum' and 'prod' in terms of 'fold'.
   */

  def fold1[A, B](l: List[A], base: B)(op: (A, B) => B): B = l match {
    case Nil => base
    case x :: xs => op(x, fold1(xs, base)(op))
  }

  def fold1Sum(l: List[Int]) = fold1(l, 0)(_ + _)

  def fold2[A, B](l: List[A], base: B, op: (A, B) => B): B = l match {
    case Nil => base
    case x :: xs => op(x, fold2(xs, base, op))
  }

  def fold2Sum(l: List[Int]) = fold2(l, 0, (a: Int, b: Int) => a + b)
  //def fold2Sum(l: List[Int]) = fold2(l, 0, (_: Int) + (_: Int))
  //def fold2Sum(l: List[Int]) = fold2[Int, Int](l, 0, _ + _)

  def fold3[A, B](l: List[A])(z: B)(f: (B, A) => B): B = {
    var acc = z
    for (x <- l) {
      acc = f(acc, x)
    }
    acc
  }

  def fold3Sum(l: List[Int]) = fold3(l)(0)(_ + _)

  def fold4[A, B](l: List[A])(z: B)(f: (B, A) => B): B = l match {
    case Nil => z
    case x :: xs => fold4(xs)(f(z, x))(f)
  }

  def foldProd(l: List[Int]) = fold1(l, 1)(_ - _)

  /**
   * Task 2: Trees
   */

  abstract class Tree[A]
  case class Leaf[A](a: A) extends Tree[A]
  case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]

  /**
   * 1) Write a recursive function 'sum' that sums up the elements of a tree of numbers.
   */

  def sumTree(l: Tree[Int]): Int = l match {
    case Leaf(a) => a
    case Node(l, r) => sumTree(l) + sumTree(r)
  }

  /**
   * 2) Write a recursive function 'collectTree' that collects all elements stored in the leaves of a tree.
   */

  def collectTree[A](l: Tree[A]): Set[A] = l match {
    case Leaf(a) => Set(a)
    case Node(l, r) => collectTree(l) ++ collectTree(r)
  }

  /**
   * 3) Can you recognize similarities between 'sumTree' and 'collectTree'? Write a higher-order function 'foldTree' that
   *    abstracts over these similarities. Reimplement 'sumTree' and 'collectTree' in terms of 'foldTree'.
   */

  def foldTree[A, B](t: Tree[A])(nodeOp: A => B)(combineOp: (B, B) => B): B = t match {
    case Leaf(a) => nodeOp(a)
    case Node(l, r) => combineOp(foldTree(l)(nodeOp)(combineOp), foldTree(r)(nodeOp)(combineOp))
  }

  def foldSumTree(t: Tree[Int]) = foldTree(t)(identity)(_ + _)
  def foldCollectTree[A](t: Tree[A]) = foldTree(t)(Set(_))(_ ++ _)

  /**
   * Task 3: Programs
   */

  abstract class F1WAE
  case class Num(n: Int) extends F1WAE
  case class Add(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class Sub(lhs: F1WAE, rhs: F1WAE) extends F1WAE
  case class Let(name: Symbol, namedExpr: F1WAE, body: F1WAE) extends F1WAE
  case class Id(name: Symbol) extends F1WAE
  case class App(funName: Symbol, arg: F1WAE) extends F1WAE

  /**
   * 1) Write a function 'progSize' that counts the number of AST nodes in a program.
   */

  def progSize(p: F1WAE): Int = p match {
    case Num(_) => 1
    case Add(l, r) => 1 + progSize(l) + progSize(r)
    case Sub(l, r) => 1 + progSize(l) + progSize(r)
    case Let(name, e1, e2) => 1 + progSize(e1) + progSize(e2)
    case Id(_) => 1
    case App(f, a) => 1 + progSize(a)
    case _ => sys.error("undefined")
  }

  /**
   * 2) Write a function 'freevars' that collects the free (unbound) variables of a program.
   */

  def freevars(p: F1WAE): Set[Symbol] =
    p match {
      case Num(_) => Set()
      case Add(l, r) => freevars(l) ++ freevars(r)
      case Sub(l, r) => freevars(l) ++ freevars(r)
      case Let(name, e1, e2) => (freevars(e1) ++ freevars(e2)) - name
      case Id(name) => Set(name)
      case App(f, a) => freevars(a) + f
      case _ => sys.error("undefined")
    }

  /**
   * 3) Can you recognize similarities between 'progSize' and 'freevars'? Write a higher-order function 'foldF1WAE' that
   *    abstracts over these similarities. Reimplement 'progSize' and 'freevars' in terms of 'foldF1WAE'
   */

  def foldF1WAE[A](
    num: Int => A,
    add: (A, A) => A,
    sub: (A, A) => A,
    wth: (Symbol, A, A) => A,
    id: Symbol => A,
    app: (Symbol, A) => A)(e: F1WAE): A =
    e match {
      case Num(n) => num(n)
      case Add(l, r) => add(foldF1WAE(num, add, sub, wth, id, app)(l), foldF1WAE(num, add, sub, wth, id, app)(r))
      case Sub(l, r) => sub(foldF1WAE(num, add, sub, wth, id, app)(l), foldF1WAE(num, add, sub, wth, id, app)(r))
      case Let(name, e1, e2) => wth(name, foldF1WAE(num, add, sub, wth, id, app)(e1), foldF1WAE(num, add, sub, wth, id, app)(e2))
      case Id(name) => id(name)
      case App(f, a) => app(f, foldF1WAE(num, add, sub, wth, id, app)(a))
    }

  def progSize2 = foldF1WAE[Int](_ => 1, _ + _, _ + _, (_, a, b) => a + b, _ => 1, (_, a) => a + 1) _

  def freevars2 = foldF1WAE[Set[Symbol]](_ => Set(), _ ++ _, _ ++ _, (name, a, b) => (a ++ b) - name, name => Set(name), (f, a) => a + f) _
}
