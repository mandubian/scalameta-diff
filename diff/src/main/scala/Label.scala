package scala.meta
package diff

// import scala.meta._
// import scala.meta.parsers._
import scala.meta.inputs._
import scala.meta.contrib.implicits.Equality._
import internal.trees.Origin

sealed trait Label

final case class ObjectType(tpe: String) extends Label
final case class ValueLabel(value: TreeNode) extends Label
final case class PosLabel(origin: internal.trees.Origin) extends Label

// final case class AnnotationLabel(value: TreeNode) extends Label

sealed trait FieldLabel extends Label
final case class SimpleFieldLabel(name: String) extends FieldLabel
final case class TreeListFieldLabel(name: String, nb: Int) extends FieldLabel
final case class TreeListListFieldLabel(name: String, nb: Int) extends FieldLabel
final case class TreeOptionFieldLabel(name: String, isDefined: Boolean) extends FieldLabel


object Label {

  def equals(lbl1: Label, lbl2: Label): Boolean = {
    (lbl1, lbl2) match {
      case (PosLabel(Origin.Parsed(_, _, pos1)), PosLabel(Origin.Parsed(_, _, pos2))) =>
        pos1 == pos2
      case (ValueLabel(tree1), ValueLabel(tree2)) =>
        tree1.tree.isEqual(tree2.tree)
      case _ => lbl1 == lbl2
    }
  }
}