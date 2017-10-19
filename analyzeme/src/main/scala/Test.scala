package toto

object Test {  
  val a = 3
  case class Foo(a: String)
  def f(foo: Foo): String = foo.a
}