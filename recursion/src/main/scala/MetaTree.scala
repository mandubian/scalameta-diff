package scala.meta
package fix

import matryoshka._
import matryoshka.implicits._
import matryoshka.patterns._
import matryoshka.data._

import scalaz._, Scalaz._
import scala.meta.contrib.implicits.Equality._


sealed trait Label

final case class ObjectType(tpe: String) extends Label
final case class ValueLabel(value: scala.meta.Tree) extends Label
// final case class PosLabel(origin: internal.trees.Origin) extends Label

sealed trait FieldLabel extends Label
final case class SimpleFieldLabel(name: String) extends FieldLabel
final case class ListFieldLabel(name: String, nb: Int) extends FieldLabel
final case class ListListFieldLabel(name: String, nb: Int) extends FieldLabel
final case class OptionFieldLabel(name: String, isDefined: Boolean) extends FieldLabel



sealed trait MetaTree[+A] {
  def label: Label
  // def fieldChildren: List[A]
}

object MetaTree extends MetaTreeCoalgebra with MetaTreeAlgebra {

  final case class Leaf[+A](value: scala.meta.Tree) extends MetaTree[A] {
    val label = ValueLabel(value)
  }

  // final case class Siblings[+A](elts: List[A]) extends MetaTree[A]

  final case class Obj[+A](tpe: String, fields: List[Field[A]]) extends MetaTree[A] {
    val label = ObjectType(tpe)
  }

  sealed trait Field[+A] {
    def label: FieldLabel
  }

  final case class SimpleField[+A](name: String, child: A) extends Field[A] {
    val label = SimpleFieldLabel(name)
  }

  final case class ListField[+A](name: String, children: List[A]) extends Field[A] {
    val label = ListFieldLabel(name, children.length)
  }

  final case class ListListField[+A](name: String, childrens: List[List[A]]) extends Field[A] {
    val label = ListListFieldLabel(name, childrens.length)
  }

  final case class OptionField[+A](name: String, childOpt: Option[A]) extends Field[A] {
    val label = OptionFieldLabel(name, childOpt.isDefined)
  }

  implicit val fieldFunctor: Functor[Field] = new Functor[Field] {
    override def map[A, B](fa: Field[A])(f: A => B) = fa match {
      case SimpleField(label, child) => SimpleField(label, f(child))
      case ListField(label, children) => ListField(label, children.map(f))
      case ListListField(label, childrens) => ListListField(label, childrens.map(_.map(f)))
      case OptionField(label, childOpt) => OptionField(label, childOpt.map(f))
    }
  }

  implicit val functor: Functor[MetaTree] = new Functor[MetaTree] {
    override def map[A, B](fa: MetaTree[A])(f: A => B) = fa match {
      case Leaf(value) => Leaf[B](value)
      // case Siblings(elts) => Siblings(elts.map(f))
      case Obj(label, fields) => Obj(label, fields.map(field => fieldFunctor.map(field)(f)))
    }
  }

  implicit val fieldTraverse: Traverse[Field] = new Traverse[Field] {
    def traverseImpl[G[_], A, B](fa: Field[A])(f: A => G[B])(
      implicit G: Applicative[G]):
        G[Field[B]] = fa match {
      case SimpleField(label, child) => G.map(f(child)) { c => SimpleField(label, c) }
      case ListField(label, children) => G.map(children.traverse(f)) { cs => ListField(label, cs) }
      case ListListField(label, childrens) => G.map(childrens.traverse(_.traverse(f))) { css => ListListField(label, css) }
      case OptionField(label, childOpt) => G.map(childOpt.traverse(f)) { cOpt => OptionField(label, cOpt) }        
    }
  }

  implicit val traverse: Traverse[MetaTree] = new Traverse[MetaTree] {
    def traverseImpl[G[_], A, B](fa: MetaTree[A])(f: A => G[B])(
      implicit G: Applicative[G]):
        G[MetaTree[B]] = fa match {
      case Leaf(value) => G.point(Leaf[B](value))

      case Obj(label, fields) => G.map(fields.traverse(fs => fs.traverse(f))){ fs => Obj(label, fs) }
    }
  }  

  implicit val fieldEqual: Delay[Equal, Field] = new Delay[Equal, Field] {
    def apply[α](eq: Equal[α]) = Equal.equal((a, b) => {
      implicit val ieq = eq
        (a, b) match {
        case (SimpleField(ll, lc), SimpleField(rl, rc)) if (ll == rl) => lc ≟ rc
        case (ListField(ll, lcs), ListField(rl, rcs)) if (ll == rl) => lcs ≟ rcs
        case (ListListField(ll, lcs), ListListField(rl, rcs)) if (ll == rl) => lcs ≟ rcs
        case (OptionField(ll, lc), OptionField(rl, rc)) => lc ≟ rc
        case (_, _) => false
      }
    })
  }

  implicit val equal: Delay[Equal, MetaTree] = new Delay[Equal, MetaTree] {
    def apply[α](eq: Equal[α]) = Equal.equal((a, b) => {
      implicit val ieq = eq
        (a, b) match {
        case (Leaf(l), Leaf(r)) if (l.isEqual(r)) => true
        case (Obj(l, lfs), Obj(r, rfs)) if(l == r) => lfs ≟ rfs
        case (_, _) => false
      }
    })
  }

  implicit val diffable: Diffable[MetaTree] = new Diffable[MetaTree] {
    def diffImpl[T[_[_]]: BirecursiveT](l: T[MetaTree], r: T[MetaTree]):
        Option[DiffT[T, MetaTree]] =
      (l.project, r.project) match {
        case (l @ Leaf(vl),        r @ Leaf(vr)) =>
          localDiff(l, r).some
        case (l @ Obj(l1, lfs1),   r @ Obj(r1, rfs1)) =>
          localDiff(l, r).some
        case (_,                  _) => None
      }
  }

  implicit val fieldShow: Delay[Show, Field] = new Delay[Show, Field] {
    def apply[α](s: Show[α]) = {
      implicit val is = s
      Show.show {
        case SimpleField(label, child) => Cord(label) ++ Cord(": ") ++ ToShowOps(child).show
        case ListField(label, children) => Cord(label) ++ ToShowOps(children).show
        case ListListField(label, childrens) => Cord(label) ++ ToShowOps(childrens).show
        case OptionField(label, childOpt) => Cord(label) ++ ToShowOps(childOpt).show
      }
    }
  }

  implicit val show: Delay[Show, MetaTree] = new Delay[Show, MetaTree] {
    def apply[α](s: Show[α]) = {
      implicit val is = s
      Show.show {
        case Leaf(tree)       => Cord(s"${tree.syntax}")
        case Obj(tpe, fields) => Cord(tpe) ++ ToShowOps(fields).show
      }
    }
  }

  type MetaError[T] = Either[String, T]

  implicit val birec: Birecursive.Aux[scala.meta.Tree, MetaTree] =
    Birecursive.fromAlgebraIso(algebra, coalgebra)

  // def toScalazTree: Algebra[MetaTree, scalaz.Tree[String]] = {
  //   // x => Tree.Node(x.void, x.toStream)
  //   case Leaf(tree) => scalaz.Tree.Leaf(tree.syntax)
  //   case Obj(lbl, fields) => scalaz.Tree.Node(lbl, Stream.Empty)
  // }

  // def toScalazTree2: Algebra[Diff[Mu, MetaTree,?], Tree[String]] = {
  //   case Same(t) => t.cata(toScalazTree)
  //   case Similar(ident) => ident.traverse(f) ∘ (Similar(_))
  //   // case Different(left, right) =>
  //   //   G.point(Different(left, right))
  //   // case LocallyDifferent(left, right) =>
  //   //   left.traverse(f) ∘ (LocallyDifferent(_, right))
  //   // case Inserted(right) => right.traverse(f) ∘ (Inserted(_))
  //   // case Deleted(left) => left.traverse(f) ∘ (Deleted(_))
  //   // case Added(right) => G.point(Added(right))
  //   // case Removed(left) => G.point(Removed(left))
  // }
    

}
