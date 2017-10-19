package scala.meta
package fix

import slamdata.Predef._
import matryoshka._
import matryoshka.data.{Mu}
import matryoshka.implicits._
import matryoshka.patterns._
import scala.meta.contrib.implicits.Equality._

import MetaTree._
import scalaz._, Scalaz._

object Main {

  
  def main(args: Array[String]): Unit = {

    val tree: scala.meta.Tree = q"""
object Test {  
  val a = 2 + 5
}"""

    val metaTree: Mu[MetaTree] = tree.ana[Mu[MetaTree]](MetaTree.coalgebra)
    println(s"metaTree:${ToShowOps(metaTree).show}")
    val cataTree: scala.meta.Tree = metaTree.cata(MetaTree.algebra)
    println(s"cataTree:$cataTree")

    assert(tree.isEqual[Structurally](cataTree))
    assert(tree.isEqual[Syntactically](cataTree))

    val tree2: scala.meta.Tree = q"""
object Test {  
  val a = 2 + 6
}"""

    val metaTree2: Mu[MetaTree] = tree2.ana[Mu[MetaTree]](MetaTree.coalgebra)

    val df: Mu[Diff[Mu, MetaTree, ?]] = metaTree.paraMerga(metaTree2)(patterns.diff)
    println(s"df:${df}")

    // not yet formatting correctly
    // val drawn = df.cata(toTree).drawTree
    // println(s"$drawn")

  }

}

