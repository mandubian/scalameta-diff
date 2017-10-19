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

    // first tree
    val tree: scala.meta.Tree = q"""
object Test {  
  val a = 2 + 5
}"""

    // build recursive MetaTree from tree using an anamorphism
    val metaTree: Mu[MetaTree] = tree.ana[Mu[MetaTree]](MetaTree.coalgebra)
    println(s"metaTree:${ToShowOps(metaTree).show}")

    // rebuild original tree from MetaTree using catamorphism
    val cataTree: scala.meta.Tree = metaTree.cata(MetaTree.algebra)
    println(s"cataTree:$cataTree")

    // check both are equal
    assert(tree.isEqual[Structurally](cataTree))
    assert(tree.isEqual[Syntactically](cataTree))

    // second tree
    val tree2: scala.meta.Tree = q"""
object Test {  
  val a = 2 + 6
}"""

    // build recursive MetaTree from tree2 using an anamorphism
    val metaTree2: Mu[MetaTree] = tree2.ana[Mu[MetaTree]](MetaTree.coalgebra)

    // build diff tree using Matryoshka Diff structure & funny paramerga function
    val df: Mu[Diff[Mu, MetaTree, ?]] = metaTree.paraMerga(metaTree2)(patterns.diff)
    // here you'll see a big structure with at the end LocallyDifferent(Leaf(5),Leaf(6))
    println(s"df:${df}")

    // displaying diff not yet formatting correctly due to inner fields
    // val drawn = df.cata(toTree).drawTree
    // println(s"$drawn")

  }

}

