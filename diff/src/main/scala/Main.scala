package scala.meta
package diff


import scalafix.util._

// import scala.meta._
// import scala.meta.parsers._
import scala.meta.inputs._
import scala.meta.contrib.implicits.Equality._
import internal.trees.Origin

object Main {

  def flagSyntax(flags: Long): String = {
    val buf = new StringBuilder
    def append(flag: String) = {
      if (buf.isEmpty) buf ++= flag
      else buf ++= (" " + flag)
    }
    def hasFlag(flag: Long) = (flags & flag) == flag
    if (hasFlag(PRIVATE)) append("PRIVATE")
    if (hasFlag(PROTECTED)) append("PROTECTED")
    if (hasFlag(ABSTRACT)) append("ABSTRACT")
    if (hasFlag(FINAL)) append("FINAL")
    if (hasFlag(SEALED)) append("SEALED")
    if (hasFlag(IMPLICIT)) append("IMPLICIT")
    if (hasFlag(LAZY)) append("LAZY")
    if (hasFlag(CASE)) append("CASE")
    if (hasFlag(COVARIANT)) append("COVARIANT")
    if (hasFlag(CONTRAVARIANT)) append("CONTRAVARIANT")
    if (hasFlag(INLINE)) append("INLINE")
    if (hasFlag(VAL)) append("VAL")
    if (hasFlag(VAR)) append("VAR")
    if (hasFlag(DEF)) append("DEF")
    if (hasFlag(PRIMARYCTOR)) append("PRIMARYCTOR")
    if (hasFlag(SECONDARYCTOR)) append("SECONDARYCTOR")
    if (hasFlag(MACRO)) append("MACRO")
    if (hasFlag(TYPE)) append("TYPE")
    if (hasFlag(PARAM)) append("PARAM")
    if (hasFlag(TYPEPARAM)) append("TYPEPARAM")
    if (hasFlag(OBJECT)) append("OBJECT")
    if (hasFlag(PACKAGE)) append("PACKAGE")
    if (hasFlag(PACKAGEOBJECT)) append("PACKAGEOBJECT")
    if (hasFlag(CLASS)) append("CLASS")
    if (hasFlag(TRAIT)) append("TRAIT")
    buf.toString.toLowerCase
  }

  def nameDenot(sdb: SemanticdbIndex, input: scala.meta.inputs.Input, name: Name, fullDetails: Boolean): String = {
    val syntax = name.syntax
    // workaround for https://github.com/scalameta/scalameta/issues/1083
    val pos =
      if (syntax.startsWith("(") &&
        syntax.endsWith(")") &&
        syntax != name.value)
        scala.meta.inputs.Position.Range(input, name.pos.start + 1, name.pos.end - 1)
      else scala.meta.inputs.Position.Range(input, name.pos.start, name.pos.end)
    val sym = sdb.symbol(pos).get
    val denot = sdb.denotation(sym).get

    val s_info = if (denot.signature != "") ": " + denot.signature else ""
    if(fullDetails) s"${flagSyntax(denot.flags)} ${sym.syntax.init}${s_info}"
    else s"${sym.syntax.init}"
  }

  def tree2Symbol2Tree(sdb: SemanticdbIndex, input: scala.meta.inputs.Input, tree: Tree, fullDetails: Boolean): Tree = tree match {
    case name@(Type.Name(_)) =>
      Type.Name(nameDenot(sdb, input, name, fullDetails))
    case name@(Term.Name(_)) =>
      Term.Name(nameDenot(sdb, input, name, fullDetails))
    case name@Name(_) =>
      Name(nameDenot(sdb, input, name, fullDetails))
    case Importee.Rename(name, t) =>
      Importee.Rename(Name(nameDenot(sdb, input, name, fullDetails)), t)
    case Importee.Name(name) =>
      Importee.Name(Name(nameDenot(sdb, input, name, fullDetails)))
    case Term.Select(t, name @ Name(_)) =>
      Term.Select(t, Term.Name(nameDenot(sdb, input, name, fullDetails)))
    case Type.Select(t, name @ Name(_)) =>
      Term.Select(t, Term.Name(nameDenot(sdb, input, name, fullDetails)))
    case lit: Lit =>
      lit
  }

  def toSemantic(sdb: SemanticdbIndex, src:scala.meta.inputs.Input, target:scala.meta.inputs.Input, diff: Diff, fullDetailsFrom: Boolean = false, fullDetailsTo: Boolean = false): Diff = {
    diff match {
      case Ins(label, d) =>
        // Ins(label, toSemantic(sdb, d))
        label match {
          case ValueLabel(TreeNode(tree)) =>
            Ins(ValueLabel(TreeNode(tree2Symbol2Tree(sdb, target, tree, fullDetailsTo))), toSemantic(sdb, src, target, d, fullDetailsFrom, fullDetailsTo))
        }
      case Del(label, d) =>
        label match {
          case ValueLabel(TreeNode(tree)) =>
            Del(ValueLabel(TreeNode(tree2Symbol2Tree(sdb, src, tree, fullDetailsFrom))), toSemantic(sdb, src, target, d, fullDetailsFrom, fullDetailsTo))
        }
      case Cpy(label, d) => Cpy(label, toSemantic(sdb, src, target, d, fullDetailsFrom, fullDetailsTo))
      case End => End
    }
  }

  def main(args: Array[String]): Unit = {
    // val database = Database.load(Classpath(BuildInfo.classpath), Sourcepath(BuildInfo.sourcepath))
    // println(s"Size: ${database.documents.length}")

    val sdb = SemanticdbIndex.load(Sourcepath(BuildInfo.sourcepath), Classpath(BuildInfo.classpath))
    println(sdb.database)

    val src = sdb.documents(0)
    val srcTree = src.input.text.parse[Source].get.children.head.children.tail.map(TreeNode(_))
    val target = sdb.documents(1)
    val targetTree = target.input.text.parse[Source].get.children.head.children.tail.map(TreeNode(_))
    println(s"srcTree:${srcTree}")
    println(s"target:${targetTree}")

    val diff = Diff(srcTree, targetTree)
    println(s"diff:${diff}")

    val patched = Diff.patch(diff, srcTree)
    println(s"patched: ${patched}")

    val sem0 = toSemantic(sdb, src.input, target.input, diff, fullDetailsFrom = false, fullDetailsTo = false)

    val Right(List(TreeNode(resrc))) = Diff.extractSource(sem0, List())
    val Right(List(TreeNode(retarget))) = Diff.extractTarget(sem0, List())
    println(s"resrc: ${resrc}")
    println(s"retarget: ${retarget}")
    val sem = toSemantic(sdb, src.input, target.input, diff, fullDetailsFrom = true, fullDetailsTo = false)
    // println(s"sem:$sem")

    println(s"SEMANTIC DIFF:\n${DiffSyntax(scala.meta.dialects.Scala212)(sem)}")    

    // def resetAllOrigins[T <: Tree](tree: T): T = {
    //   tree
    //     .transform {
    //       case tree: Tree => tree.withOrigin(Origin.None)
    //     }
    //     .asInstanceOf[T]
    // }

    // val resrc1 = resetAllOrigins(resrc).syntax
    // val retarget1 = resetAllOrigins(retarget).syntax
    
    // val result = scalafix.diff.DiffUtils.unifiedDiff(
    //   "Test.scala"
    // , "Test2.scala"
    // , resrc1.lines.toList
    // , retarget1.lines.toList
    // , 3
    // )

    // println(s"UNIFIED:\n$result")

// object Test {
//   class A
//   trait B
//   object C
//   object D
// }

// object Test {  
//   class A(a: Int) {
//     def b(c: Int): String = {
//       def d(e: Int): String = {
//         def f(g: Int): String = {
//           (g + e + c + a).toString
//         }
//       }
//     }
//   }
// }

  // def foo1(a:Int, b:Int, c:Int, d:Int): Int = a + b + c + d
  // def foo2(a:Int, b:Int, c:Int, d:Int): Int = a + b + c + d
  // def foo3(a:Int, b:Int, c:Int, d:Int): Int = a + b + c + d

// object Test {  
//   class A(a: Int) {
//     def b(c: Int): String = {
//       def d(e: Int): String = {
//         def f(g: Int): String = {
//           (g + e + c + a).toString
//         }
//       }
//     }
//   }
// }

/*
    val tree = q"""
object Test {  
  val a = 2 + 5
  def f(b: String) = { b + a.toString }
}
"""
    // val tree = AbsolutePath(BuildInfo.sourcepath+"/analyzeme/src/main/scala/Test.scala").parse[Source].get
    println(s"tree.syntax: ${tree.syntax}")
    println(s"tree.structure: ${tree.structure}")

    // val src = tree.children.head.children.tail.map(TreeNode(_))
    // val src = tree.children.map(TreeNode(_))
    val src = List(TreeNode(tree))

    val tree2 = q"""
object Test {  
  var b = 3 + 4
  def g(b: String) = { c + a.toString }
}
"""
    // val tree2 = AbsolutePath(BuildInfo.sourcepath+"/analyzeme/src/main/scala/Test2.scala").parse[Source].get
    println(s"tree2.syntax: ${tree2.syntax}")
    println(s"tree2.structure: ${tree2.structure}")

    // val target = tree2.children.head.children.tail.map(TreeNode(_))
    // val target = tree2.map(TreeNode(_))
    val target = List(TreeNode(tree2))

    val basicDiff = Diff(src, target)
    println(s"diff: ${basicDiff}")

    println("\n")

    // val memoDiff = MemoDiff(src, target)
    // println(s"MemoDiff: ${memoDiff.diff}")
    // println("\n")

    // println(s"EQ:${memoDiff.diff == basicDiff}")

    // val diff = memoDiff.diff

    // val patched = Diff.patch(diff, src)
    // println(s"patched: ${patched}")


    // println("\n")

    // val Right(resrc) = Diff.extractSource(diff, List())
    // println(s"src: ${src}")
    // println(s"resrc: ${resrc}")

    // val TreeNode(srcTree) = src.head
    // val TreeNode(resrcTree) = resrc.head
    // assert(resrcTree.isEqual[Structurally](srcTree))

    // val retarget = Diff.extractTarget(diff, List())
    // println(s"retarget: ${retarget}")

    // println(s"SHOW: ${Diff.showDiff(basicDiff)}")

    println(s"${DiffSyntax(scala.meta.dialects.Scala212)(basicDiff)}")
*/
  }
}

