package scala.meta
package fix

import matryoshka._
import matryoshka.implicits._
import scalaz.StateT
import scalaz.std.either._

import MetaTree._

import shapeless.TypeCase

// Contains the Matryoshka required Coalgebra Tree => MetaTree[Tree]
// this code is really raw and can be improved
trait MetaTreeCoalgebra {

  val `List[Tree]` = TypeCase[List[Tree]]
  val `Option[Tree]` = TypeCase[Option[Tree]]
  val `List[List[Tree]]` = TypeCase[List[List[Tree]]]

  val coalgebra: Coalgebra[MetaTree, Tree] = {
    case t: Term.Name => Leaf(t)
    case t: Name => Leaf(t)
    case l: Lit  => Leaf(l)  

    case t =>
      Obj(
        t.productPrefix
      , t.productFields.zip(t.productIterator.toList).map {
          case (n, t) => t match {
            case `Option[Tree]`(t) => OptionField(n, t)
            case `List[Tree]`(t) => ListField(n, t)
            case `List[List[Tree]]`(t) => ListListField(n, t)
            case t: Tree => SimpleField(n, t)
          }
        }
      )
  }
  
}