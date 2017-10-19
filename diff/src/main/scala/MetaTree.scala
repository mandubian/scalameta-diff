package scala.meta
package diff

import internal.trees.Origin


sealed trait MetaTree {
  def fieldChildren: List[MetaTree]

  def label: Label
}

final case class TreeNode(tree: Tree) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    MetaTree.fieldChildren(tree)
  }

  val label: Label = {
    tree match {
      case t:Term.Name  => ValueLabel(this)
      case t:Name       => ValueLabel(this)
      case l:Lit        => ValueLabel(this)
      case t            => ObjectType(t.productPrefix)
    }
  }

}

final case class Annotation(node: MetaTree) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    Nil
  }

  val label: Label = node.label
}


final case class PosField(origin: Origin) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    Nil
  }

  val label: Label = {
    PosLabel(origin)
  }
}

final case class TreeField(name: String, tree: Tree) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    List(TreeNode(tree))
  }

  val label: Label = {
    SimpleFieldLabel(name)
  }
}

final case class TreeListField(name: String, trees: List[Tree]) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    trees.map(TreeNode(_))
  }

  val label: Label = {
    TreeListFieldLabel(name, trees.length)
  }
}

final case class TreeOptionField(name: String, opt: Option[Tree]) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    opt.map(t => List(TreeNode(t))).getOrElse(Nil)
  }

  val label: Label = {
    TreeOptionFieldLabel(name, opt.isDefined)
  }
}

final case class TreeListListField(name: String, treess: List[List[Tree]]) extends MetaTree {
  val fieldChildren: List[MetaTree] = {
    treess.map { trees => TreeListField(name, trees) }    
  }

  val label: Label = {
    TreeListListFieldLabel(name, treess.length)
  }
}

trait TreeConverter[T <: Tree] {
  def toMeta(tree: T): List[MetaTree]
  def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], T)]]
}



object MetaTree {

  // Oh a StateMonad
  def getField[T](xs: List[MetaTree]): PatchError[(List[MetaTree], T)] = {
    xs match {
      case Nil =>
        Left(PatchErrorMsg(s"can't get field, empty list $xs"))

      case Annotation(_) :: x :: xs =>
        val TreeField(_, f) = x
        Right((xs, f.asInstanceOf[T]))

      case x :: xs =>
        val TreeField(_, f) = x
        Right((xs, f.asInstanceOf[T]))

    }
  }

  // Oh a StateMonad
  def getPosField(xs: List[MetaTree]): PatchError[(List[MetaTree], Origin)] = {
    xs match {
      case Nil =>
        Left(PatchErrorMsg(s"can't get field, empty list $xs"))

      case Annotation(_) :: x :: xs =>
        val PosField(origin) = x
        Right((xs, origin))

      case x :: xs =>
        val PosField(origin) = x
        Right((xs, origin))

    }
  }

  def getListField[T](xs: List[MetaTree]): PatchError[(List[MetaTree], List[T])] = {
    xs match {
      case Nil =>
        Left(PatchErrorMsg(s"can't get field, empty list $xs"))

      case Annotation(_) :: x :: xs =>
        val TreeListField(_, f) = x
        Right((xs, f.asInstanceOf[List[T]]))

      case x :: xs =>
        val TreeListField(_, f) = x
        Right((xs, f.asInstanceOf[List[T]]))
    }
  }

  def getListListField[T](xs: List[MetaTree]): PatchError[(List[MetaTree], List[List[T]])] = {
    xs match {
      case Nil =>
        Left(PatchErrorMsg(s"can't get field, empty list $xs"))

      case Annotation(_) :: x :: xs =>
        val TreeListListField(_, f) = x
        Right((xs, f.asInstanceOf[List[List[T]]]))

      case x :: xs =>
        val TreeListListField(_, f) = x
        Right((xs, f.asInstanceOf[List[List[T]]]))
    }
  }

  def getOptionField[T](xs: List[MetaTree]): PatchError[(List[MetaTree], Option[T])] = {
    xs match {
      case Nil =>
        Left(PatchErrorMsg(s"can't get field, empty list $xs"))

      case Annotation(_) :: x :: xs =>
        val TreeOptionField(_, f) = x
        Right((xs, f.asInstanceOf[Option[T]]))

      case x :: xs =>
        val TreeOptionField(_, f) = x
        Right((xs, f.asInstanceOf[Option[T]]))
    }
  }

  val termParamConverter = new TreeConverter[Term.Param] {
    def toMeta(tree: Term.Param): List[MetaTree] = {
      //   @ast class Param(mods: List[Mod], name: meta.Name, decltpe: Option[Type], default: Option[Term]) extends Member
      val Term.Param(mods, name, decltpe, default) = tree
      TreeListField("mods", mods) ::  TreeField("name", name) ::
      TreeOptionField("decltpe", decltpe) :: TreeOptionField("default", default) ::
      Nil

    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Term.Param)]] = {
      //   @ast class Param(mods: List[Mod], name: meta.Name, decltpe: Option[Type], default: Option[Term]) extends Member
      case "Term.Param" =>
        getListField[Mod](xs).flatMap { case (xs, mods) =>
          getField[Term.Name](xs).flatMap { case (xs, name) =>
            getOptionField[Type](xs).flatMap { case (xs, decltpe) =>
              getOptionField[Term](xs).map { case (xs, default) =>
                xs -> Term.Param(mods, name, decltpe, default)
              }
            }
          }
        }
    }

  }

  val termConverter = new TreeConverter[Term] {
    def toMeta(tree: Term): List[MetaTree] = tree match {
      // @branch trait Term extends Stat
      // object Term {
      //   @branch trait Ref extends Term with scala.meta.Ref
      //   @ast class This(qual: scala.meta.Name) extends Term.Ref
      case Term.This(qual) =>
        TreeField("qual", qual) ::
        Nil

      //   @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Term.Ref
      case Term.Super(thisp, superp) =>
        TreeField("thisp", thisp) :: TreeField("superp", superp) ::
        Nil
      //   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
      //   @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
      case Term.Select(qual, name) =>
        TreeField("qual", qual) ::  TreeField("name", name) ::
        Nil
      //   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
      //     checkFields(parts.length == args.length + 1)
      //   }
      case Term.Interpolate(prefix, parts, args) =>
        TreeField("prefix", prefix) :: TreeListField("parts", parts) :: TreeListField("args", args) ::  
        Nil
      //   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
      //     checkFields(parts.length == args.length + 1)
      //   }
      case Term.Xml(parts, args) =>
        TreeListField("parts", parts) :: TreeListField("args", args) ::  
        Nil
      //   @ast class Apply(fun: Term, args: List[Term]) extends Term
      case Term.Apply(fun, args) =>
        TreeField("fun", fun) :: TreeListField("args", args) ::  
        Nil
      //   @ast class ApplyType(fun: Term, targs: List[Type] @nonEmpty) extends Term
      case Term.ApplyType(fun, targs) =>
        TreeField("fun", fun) :: TreeListField("targs", targs) ::  
        Nil
      //   @ast class ApplyInfix(lhs: Term, op: Name, targs: List[Type], args: List[Term]) extends Term
      case Term.ApplyInfix(lhs, op, targs, args) =>
        TreeField("lhs", lhs) :: TreeField("op", op) :: TreeListField("targs", targs) :: TreeListField("args", args) ::  
        Nil
      //   @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
      //     checkFields(op.isUnaryOp)
      //   }
      case Term.ApplyUnary(op, arg) =>
        TreeField("op", op) :: TreeField("arg", arg) ::
        Nil
      //   @ast class Assign(lhs: Term, rhs: Term) extends Term {
      //     checkFields(lhs.is[Term.Quasi] || lhs.is[Term.Ref] || lhs.is[Term.Apply])
      //     checkParent(ParentChecks.TermAssign)
      //   }
      case Term.Assign(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) ::
        Nil
      //   @ast class Return(expr: Term) extends Term
      case Term.Return(expr) =>
        TreeField("expr", expr) ::
        Nil
      //   @ast class Throw(expr: Term) extends Term
      case Term.Throw(expr) =>
        TreeField("expr", expr) ::
        Nil
      //   @ast class Ascribe(expr: Term, tpe: Type) extends Term
      case Term.Ascribe(expr, tpe) =>
        TreeField("expr", expr) :: TreeField("tpe", tpe) ::
        Nil
      //   @ast class Annotate(expr: Term, annots: List[Mod.Annot] @nonEmpty) extends Term
      case Term.Annotate(expr, annots) =>
        TreeField("expr", expr) :: TreeListField("annots", annots) ::
        Nil
      //   @ast class Tuple(args: List[Term] @nonEmpty) extends Term {
      //     // tuple must have more than one element
      //     // however, this element may be Quasi with "hidden" list of elements inside
      //     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Term.Quasi]))
      //   }
      case Term.Tuple(args) =>
        TreeListField("args", args) ::
        Nil
      //   @ast class Block(stats: List[Stat]) extends Term {
      //     checkFields(stats.forall(_.isBlockStat))
      //   }
      case Term.Block(stats) =>
        TreeListField("stats", stats) ::
        Nil
      //   @ast class If(cond: Term, thenp: Term, elsep: Term) extends Term
      case Term.If(cond, thenp, elsep) =>
        TreeField("cond", cond) :: TreeField("thenp", thenp) :: TreeField("elsep", elsep) ::
        Nil
      //   @ast class Match(expr: Term, cases: List[Case] @nonEmpty) extends Term
      case Term.Match(expr, cases) =>
        TreeField("expr", expr) :: TreeListField("cases", cases) ::
        Nil
      //   @ast class Try(expr: Term, catchp: List[Case], finallyp: Option[Term]) extends Term
      case Term.Try(expr, catchp, finallyp) =>
        TreeField("expr", expr) :: TreeListField("catchp", catchp) :: TreeOptionField("finallyp", finallyp) ::
        Nil
      //   @ast class TryWithHandler(expr: Term, catchp: Term, finallyp: Option[Term]) extends Term
      case Term.TryWithHandler(expr, catchp, finallyp) =>
        TreeField("expr", expr) :: TreeField("catchp", catchp) :: TreeOptionField("finallyp", finallyp) ::
        Nil
      //   @ast class Function(params: List[Term.Param], body: Term) extends Term {
      //     checkFields(params.forall(param => param.is[Term.Param.Quasi] || (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)))
      //     checkFields(params.exists(_.is[Term.Param.Quasi]) || params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1))
      //   }
      case Term.Function(params, body) =>
        TreeListField("params", params) :: TreeField("body", body) ::
        Nil
      //   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Term
      case Term.PartialFunction(cases) =>
        TreeListField("cases", cases) ::
        Nil
      //   @ast class While(expr: Term, body: Term) extends Term
      case Term.While(expr, body) =>
        TreeField("expr", expr) :: TreeField("body", body) ::
        Nil
      //   @ast class Do(body: Term, expr: Term) extends Term
      case Term.Do(body, expr) =>
        TreeField("body", body) :: TreeField("expr", expr) ::
        Nil
      //   @ast class For(enums: List[Enumerator] @nonEmpty, body: Term) extends Term {
      //     checkFields(enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.Quasi])
      //   }
      case Term.For(enums, body) =>
        TreeListField("enums", enums) :: TreeField("body", body) ::
        Nil
      //   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Term) extends Term
      case Term.ForYield(enums, body) =>
        TreeListField("enums", enums) :: TreeField("body", body) ::
        Nil
      //   @ast class New(init: Init) extends Term
      case Term.New(init) =>
        TreeField("init", init) ::
        Nil
      //   @ast class NewAnonymous(templ: Template) extends Term
      case Term.NewAnonymous(templ) =>
        TreeField("templ", templ) ::
        Nil
      //   @ast class Placeholder() extends Term
      case Term.Placeholder() =>
        Nil
      //   @ast class Eta(expr: Term) extends Term
      case Term.Eta(expr) =>
        TreeField("expr", expr) ::
        Nil
      //   @ast class Repeated(expr: Term) extends Term {
      //     checkParent(ParentChecks.TermRepeated)
      //   }
      case Term.Repeated(expr) =>
        TreeField("expr", expr) ::
        Nil

      //   def fresh(): Term.Name = fresh("fresh")
      //   def fresh(prefix: String): Term.Name = Term.Name(prefix + Fresh.nextId())
      // }
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Term)]] = {
      case s if s.startsWith("Term") => s match {

      // @branch trait Term extends Stat
      // object Term {
      //   @branch trait Ref extends Term with scala.meta.Ref
      //   @ast class This(qual: scala.meta.Name) extends Term.Ref
        case "Term.This" =>
          getField[Name](xs). map { case (xs, qual) =>
            xs -> Term.This(qual)
          }
      //   @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Term.Ref
        case "Term.Super" =>
          getField[Name](xs).flatMap { case (xs, thisp) =>
            getField[Name](xs).map { case (xs, superp) =>
              xs -> Term.Super(thisp, superp)
            }
          }
      //   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
      //   @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
        case "Term.Select" =>
          getField[Term](xs).flatMap { case (xs, qual) =>
            getField[Term.Name](xs).map { case (xs, name) =>
              xs -> Term.Select(qual, name)
            }
          }
      //   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
      //     checkFields(parts.length == args.length + 1)
      //   }
        case "Term.Interpolate" =>
          getField[Term.Name](xs).flatMap { case (xs, prefix) =>
            getListField[Lit](xs).flatMap { case (xs, parts) =>
              getListField[Term](xs).map { case (xs, args) =>
                xs -> Term.Interpolate(prefix, parts, args)
              }
            }
          }
      //   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
      //     checkFields(parts.length == args.length + 1)
      //   }
        case "Term.Xml" =>
          getListField[Lit](xs).flatMap { case (xs, parts) =>
            getListField[Term](xs).map { case (xs, args) =>
              xs -> Term.Xml(parts, args)
            }
          }

      //   @ast class Apply(fun: Term, args: List[Term]) extends Term
        case "Term.Apply" =>
          getField[Term](xs).flatMap { case (xs, fun) =>
            getListField[Term](xs).map { case (xs, args) =>
              xs -> Term.Apply(fun, args)
            }
          }
      //   @ast class ApplyType(fun: Term, targs: List[Type] @nonEmpty) extends Term
        case "Term.ApplyType" =>
          getField[Term](xs).flatMap { case (xs, fun) =>
            getListField[Type](xs).map { case (xs, targs) =>
              xs -> Term.ApplyType(fun, targs)
            }
          }
      //   @ast class ApplyInfix(lhs: Term, op: Name, targs: List[Type], args: List[Term]) extends Term
        case "Term.ApplyInfix" =>
          getField[Term](xs).flatMap { case (xs, lhs) =>
            getField[Term.Name](xs).flatMap { case (xs, op) =>
              getListField[Type](xs).flatMap { case (xs, targs) =>
                getListField[Term](xs).map { case (xs, args) =>
                  xs -> Term.ApplyInfix(lhs, op, targs, args)
                }
              }
            }
          }
      //   @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
      //     checkFields(op.isUnaryOp)
      //   }
        case "Term.ApplyUnary" =>
          getField[Term.Name](xs).flatMap { case (xs, op) =>
            getField[Term](xs).map { case (xs, arg) =>
              xs -> Term.ApplyUnary(op, arg)
            }
          }
      //   @ast class Assign(lhs: Term, rhs: Term) extends Term {
      //     checkFields(lhs.is[Term.Quasi] || lhs.is[Term.Ref] || lhs.is[Term.Apply])
      //     checkParent(ParentChecks.TermAssign)
      //   }
        case "Term.Assign" =>
          getField[Term](xs).flatMap { case (xs, lhs) =>
            getField[Term](xs).map { case (xs, rhs) =>
              xs -> Term.Assign(lhs, rhs)
            }
          }
      //   @ast class Return(expr: Term) extends Term
        case "Term.Return" =>
          getField[Term](xs).map { case (xs, expr) =>
            xs -> Term.Return(expr)
          }
      //   @ast class Throw(expr: Term) extends Term
        case "Term.Throw" =>
          getField[Term](xs).map { case (xs, expr) =>
            xs -> Term.Throw(expr)
          }
      //   @ast class Ascribe(expr: Term, tpe: Type) extends Term
        case "Term.Ascribe" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getField[Type](xs).map { case (xs, tpe) =>
              xs -> Term.Ascribe(expr, tpe)
            }
          }
      //   @ast class Annotate(expr: Term, annots: List[Mod.Annot] @nonEmpty) extends Term
        case "Term.Annotate" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getListField[Mod.Annot](xs).map { case (xs, annots) =>
              xs -> Term.Annotate(expr, annots)
            }
          }
      //   @ast class Tuple(args: List[Term] @nonEmpty) extends Term {
      //     // tuple must have more than one element
      //     // however, this element may be Quasi with "hidden" list of elements inside
      //     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Term.Quasi]))
      //   }
        case "Term.Tuple" =>
          getListField[Term](xs).map { case (xs, args) =>
            xs -> Term.Tuple(args)
          }
      //   @ast class Block(stats: List[Stat]) extends Term {
      //     checkFields(stats.forall(_.isBlockStat))
      //   }
        case "Term.Block" =>
          getListField[Stat](xs).map { case (xs, stats) =>
            xs -> Term.Block(stats)
          }
      //   @ast class If(cond: Term, thenp: Term, elsep: Term) extends Term
        case "Term.If" =>
          getField[Term](xs).flatMap { case (xs, cond) =>
            getField[Term](xs).flatMap { case (xs, thenp) =>
              getField[Term](xs).map { case (xs, elsep) =>
                xs -> Term.If(cond, thenp, elsep)
              }
            }
          }
      //   @ast class Match(expr: Term, cases: List[Case] @nonEmpty) extends Term
        case "Term.Match" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getListField[Case](xs).map { case (xs, cases) =>
              xs -> Term.Match(expr, cases)
            }
          }
      //   @ast class Try(expr: Term, catchp: List[Case], finallyp: Option[Term]) extends Term
        case "Term.Try" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getListField[Case](xs).flatMap { case (xs, catchp) =>
              getOptionField[Term](xs).map { case (xs, finallyp) =>
                xs -> Term.Try(expr, catchp, finallyp)
              }
            }
          }
      //   @ast class TryWithHandler(expr: Term, catchp: Term, finallyp: Option[Term]) extends Term
        case "Term.TryWithHandler" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getField[Term](xs).flatMap { case (xs, catchp) =>
              getOptionField[Term](xs).map { case (xs, finallyp) =>
                xs -> Term.TryWithHandler(expr, catchp, finallyp)
              }
            }
          }
      //   @ast class Function(params: List[Term.Param], body: Term) extends Term {
      //     checkFields(params.forall(param => param.is[Term.Param.Quasi] || (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)))
      //     checkFields(params.exists(_.is[Term.Param.Quasi]) || params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1))
      //   }
        case "Term.Function" =>
          getListField[Term.Param](xs).flatMap { case (xs, params) =>
            getField[Term](xs).map { case (xs, body) =>
              xs -> Term.Function(params, body)
            }
          }
      //   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Term
        case "Term.PartialFunction" =>
          getListField[Case](xs).map { case (xs, cases) =>
            xs -> Term.PartialFunction(cases)
          }
      //   @ast class While(expr: Term, body: Term) extends Term
        case "Term.While" =>
          getField[Term](xs).flatMap { case (xs, expr) =>
            getField[Term](xs).map { case (xs, body) =>
              xs -> Term.While(expr, body)
            }
          }
      //   @ast class Do(body: Term, expr: Term) extends Term
        case "Term.Do" =>
          getField[Term](xs).flatMap { case (xs, body) =>
            getField[Term](xs).map { case (xs, expr) =>
              xs -> Term.Do(body, expr)
            }
          }
      //   @ast class For(enums: List[Enumerator] @nonEmpty, body: Term) extends Term {
      //     checkFields(enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.Quasi])
      //   }
        case "Term.For" =>
          getListField[Enumerator](xs).flatMap { case (xs, enums) =>
            getField[Term](xs).map { case (xs, body) =>
              xs -> Term.For(enums, body)
            }
          }
      //   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Term) extends Term
        case "Term.ForYield" =>
          getListField[Enumerator](xs).flatMap { case (xs, enums) =>
            getField[Term](xs).map { case (xs, body) =>
              xs -> Term.ForYield(enums, body)
            }
          }
      //   @ast class New(init: Init) extends Term
        case "Term.New" =>
          getField[Init](xs).map { case (xs, init) =>
            xs -> Term.New(init)
          }
      //   @ast class NewAnonymous(templ: Template) extends Term
        case "Term.NewAnonymous" =>
          getField[Template](xs).map { case (xs, templ) =>
            xs -> Term.NewAnonymous(templ)
          }
      //   @ast class Placeholder() extends Term
        case "Term.Placeholder" =>
          Right(xs -> Term.Placeholder())

      //   @ast class Eta(expr: Term) extends Term
        case "Term.Eta" =>
          getField[Term](xs).map { case (xs, expr) =>
            xs -> Term.Eta(expr)
          }
      //   @ast class Repeated(expr: Term) extends Term {
      //     checkParent(ParentChecks.TermRepeated)
      //   }
        case "Term.Repeated" =>
          getField[Term](xs).map { case (xs, expr) =>
            xs -> Term.Repeated(expr)
          }

      //   def fresh(): Term.Name = fresh("fresh")
      //   def fresh(prefix: String): Term.Name = Term.Name(prefix + Fresh.nextId())
      }
    }
  }

  val typeParamConverter = new TreeConverter[Type.Param] {
    // @ast class Param(mods: List[Mod],
    //                  name: meta.Name,
    //                  tparams: List[Type.Param],
    //                  tbounds: Type.Bounds,
    //                  vbounds: List[Type],
    //                  cbounds: List[Type]) extends Member
    def toMeta(tree: Type.Param): List[MetaTree] = {
      TreeListField("mods", tree.mods) ::  TreeField("name", tree.name) :: TreeListField("tparams", tree.tparams) ::
      TreeField("tbounds", tree.tbounds) :: TreeListField("vbounds", tree.vbounds) :: TreeListField("cbounds", tree.cbounds) :: 
      Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Type.Param)]] = {
      //   @ast class Param(mods: List[Mod], name: meta.Name, decltpe: Option[Type], default: Option[Term]) extends Member
      case "Type.Param" =>
        getListField[Mod](xs).flatMap { case (xs, mods) =>
          getField[Term.Name](xs).flatMap { case (xs, name) =>
            getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
              getField[Type.Bounds](xs).flatMap { case (xs, tbounds) =>
                getListField[Type](xs).flatMap { case (xs, vbounds) =>
                  getListField[Type](xs).map { case (xs, cbounds) =>
                    xs -> Type.Param(mods, name, tparams, tbounds, vbounds, cbounds)
                  }
                }
              }
            }
          }
        }
    }

  }


  val typeConverter = new TreeConverter[Type] {
    def toMeta(tree: Type): List[MetaTree] = tree match {
      // @branch trait Ref extends Type with scala.meta.Ref
      // @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
      // @ast class Select(qual: Term.Ref, name: Type.Name) extends Type.Ref {
      //   checkFields(qual.isPath || qual.is[Term.Super] || qual.is[Term.Ref.Quasi])
      // }
      case Type.Select(qual, name) =>
        TreeField("qual", qual) :: TreeField("name", name) :: 
        Nil
      // @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
      case Type.Project(qual, name) =>
        TreeField("qual", qual) :: TreeField("name", name) :: 
        Nil
      // @ast class Singleton(ref: Term.Ref) extends Type.Ref {
      //   checkFields(ref.isPath || ref.is[Term.Super])
      // }
      case Type.Singleton(ref) =>
        TreeField("ref", ref) :: 
        Nil
      // @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
      case Type.Apply(tpe, args) =>
        TreeField("tpe", tpe) :: TreeListField("args", args) :: 
        Nil
      // @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
      case Type.ApplyInfix(lhs, op, rhs) =>
        TreeField("lhs", lhs) :: TreeField("op", op) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class Function(params: List[Type], res: Type) extends Type
      case Type.Function(params, res) =>
        TreeListField("params", params) :: TreeField("res", res) :: 
        Nil
      // @ast class ImplicitFunction(params: List[Type], res: Type) extends Type
      case Type.ImplicitFunction(params, res) =>
        TreeListField("params", params) :: TreeField("res", res) :: 
        Nil
      // @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
      //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
      // }
      case Type.Tuple(args) =>
        TreeListField("args", args) :: 
        Nil
      // @ast class With(lhs: Type, rhs: Type) extends Type
      case Type.With(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class And(lhs: Type, rhs: Type) extends Type
      case Type.And(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class Or(lhs: Type, rhs: Type) extends Type
      case Type.Or(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
      //   checkFields(stats.forall(_.isRefineStat))
      // }
      case Type.Refine(tpe, stats) =>
        TreeOptionField("tpe", tpe) :: TreeListField("stats", stats) :: 
        Nil
      // @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
      //   checkFields(stats.forall(_.isExistentialStat))
      // }
      case Type.Existential(tpe, stats) =>
        TreeField("tpe", tpe) :: TreeListField("stats", stats) :: 
        Nil
      // @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
      case Type.Existential(tpe, stats) =>
        TreeField("tpe", tpe) :: TreeListField("stats", stats) :: 
        Nil
      // @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeLambda)
      // }
      case Type.Lambda(tparams, tpe) =>
        TreeListField("tparams", tparams) :: TreeField("tpe", tpe) :: 
        Nil
      // @ast class Method(paramss: List[List[Term.Param]], tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeMethod)
      // }
      case Type.Method(paramss, tpe) =>
        TreeListListField("paramss", paramss) :: TreeField("tpe", tpe) :: 
        Nil
      // @ast class Placeholder(bounds: Bounds) extends Type
      case Type.Placeholder(bounds) =>
        TreeField("bounds", bounds) :: 
        Nil

      // @ast class ByName(tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeByName)
      // }
      case Type.ByName(tpe) =>
        TreeField("tpe", tpe) :: 
        Nil
      // @ast class Repeated(tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeRepeated)
      // }
      case Type.Repeated(tpe) =>
        TreeField("tpe", tpe) :: 
        Nil
      // @ast class Var(name: Name) extends Type with Member.Type {
      //   checkFields(name.value(0).isLower)
      //   checkParent(ParentChecks.TypeVar)
      // }
      case Type.Var(name) =>
        TreeField("name", name) :: 
        Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Type)]] = {
      case s if s.startsWith("Type") => s match {
        // @branch trait Ref extends Type with scala.meta.Ref
        // @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
        // @ast class Select(qual: Term.Ref, name: Type.Name) extends Type.Ref {
        case "Type.Select" =>
          getField[Term.Ref](xs).flatMap { case (xs, qual) =>
            getField[Type.Name](xs).map { case (xs, name) =>
              xs -> Type.Select(qual, name)
            }
          }
        //   checkFields(qual.isPath || qual.is[Term.Super] || qual.is[Term.Ref.Quasi])
        // }
        // @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
        case "Type.Project" =>
          getField[Type](xs).flatMap { case (xs, qual) =>
            getField[Type.Name](xs).map { case (xs, name) =>
              xs -> Type.Project(qual, name)
            }
          }
        // @ast class Singleton(ref: Term.Ref) extends Type.Ref {
        //   checkFields(ref.isPath || ref.is[Term.Super])
        // }
        case "Type.Singleton" =>
          getField[Term.Ref](xs).map { case (xs, ref) =>
            xs -> Type.Singleton(ref)
          }
        // @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
        case "Type.Apply" =>
          getField[Type](xs).flatMap { case (xs, tpe) =>
            getListField[Type](xs).map { case (xs, args) =>
              xs -> Type.Apply(tpe, args)
            }
          }
        // @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
        case "Type.ApplyInfix" =>
          getField[Type](xs).flatMap { case (xs, lhs) =>
            getField[Type.Name](xs).flatMap { case (xs, op) =>
              getField[Type](xs).map { case (xs, rhs) =>
                xs -> Type.ApplyInfix(lhs, op, rhs)
              }
            }
          }
        // @ast class Function(params: List[Type], res: Type) extends Type
        case "Type.Function" =>
          getListField[Type](xs).flatMap { case (xs, params) =>
            getField[Type](xs).map { case (xs, res) =>
              xs -> Type.Function(params, res)
            }
          }
        // @ast class ImplicitFunction(params: List[Type], res: Type) extends Type
        case "Type.ImplicitFunction" =>
          getListField[Type](xs).flatMap { case (xs, params) =>
            getField[Type](xs).map { case (xs, res) =>
              xs -> Type.ImplicitFunction(params, res)
            }
          }
        // @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
        //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
        // }
        case "Type.Tuple" =>
          getListField[Type](xs).map { case (xs, args) =>
            xs -> Type.Tuple(args)
          }
        // @ast class With(lhs: Type, rhs: Type) extends Type
        case "Type.With" =>
          getField[Type](xs).flatMap { case (xs, lhs) =>
            getField[Type](xs).map { case (xs, rhs) =>
              xs -> Type.With(lhs, rhs)
            }
          }
        // @ast class And(lhs: Type, rhs: Type) extends Type
        case "Type.And" =>
          getField[Type](xs).flatMap { case (xs, lhs) =>
            getField[Type](xs).map { case (xs, rhs) =>
              xs -> Type.And(lhs, rhs)
            }
          }
        // @ast class Or(lhs: Type, rhs: Type) extends Type
        case "Type.Or" =>
          getField[Type](xs).flatMap { case (xs, lhs) =>
            getField[Type](xs).map { case (xs, rhs) =>
              xs -> Type.Or(lhs, rhs)
            }
          }
        // @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
        //   checkFields(stats.forall(_.isRefineStat))
        // }
        case "Type.Refine" =>
          getOptionField[Type](xs).flatMap { case (xs, tpe) =>
            getListField[Stat](xs).map { case (xs, stats) =>
              xs -> Type.Refine(tpe, stats)
            }
          }
        // @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
        //   checkFields(stats.forall(_.isExistentialStat))
        // }
        case "Type.Existential" =>
          getField[Type](xs).flatMap { case (xs, tpe) =>
            getListField[Stat](xs).map { case (xs, stats) =>
              xs -> Type.Existential(tpe, stats)
            }
          }
        // @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
        case "Type.Annotate" =>
          getField[Type](xs).flatMap { case (xs, tpe) =>
            getListField[Mod.Annot](xs).map { case (xs, annots) =>
              xs -> Type.Annotate(tpe, annots)
            }
          }
        // @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeLambda)
        // }
        case "Type.Lambda" =>
          getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
            getField[Type](xs).map { case (xs, tpe) =>
              xs -> Type.Lambda(tparams, tpe)
            }
          }
        // @ast class Method(paramss: List[List[Term.Param]], tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeMethod)
        // }
        case "Type.Method" =>
          getListListField[Term.Param](xs).flatMap { case (xs, paramss) =>
            getField[Type](xs).map { case (xs, tpe) =>
              xs -> Type.Method(paramss, tpe)
            }
          }
        // @ast class Placeholder(bounds: Bounds) extends Type
        case "Type.Placeholder" =>
          getField[Type.Bounds](xs).map { case (xs, bounds) =>
            xs -> Type.Placeholder(bounds)
          }

        // @ast class ByName(tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeByName)
        // }
        case "Type.ByName" =>
          getField[Type](xs).map { case (xs, tpe) =>
            xs -> Type.ByName(tpe)
          }
        // @ast class Repeated(tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeRepeated)
        // }
        case "Type.Repeated" =>
          getField[Type](xs).map { case (xs, tpe) =>
            xs -> Type.Repeated(tpe)
          }
        // @ast class Var(name: Name) extends Type with Member.Type {
        //   checkFields(name.value(0).isLower)
        //   checkParent(ParentChecks.TypeVar)
        // }
        case "Type.Var" =>
          getField[Type.Name](xs).map { case (xs, name) =>
            xs -> Type.Var(name)
          }
      }
    }
  }

  val typeBoundsConverter = new TreeConverter[Type.Bounds] {
    // @ast class Bounds(lo: Option[Type], hi: Option[Type]) extends Tree
    def toMeta(tree: Type.Bounds): List[MetaTree] = {
      TreeOptionField("lo", tree.lo) ::  TreeOptionField("hi", tree.hi) :: 
      Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Type.Bounds)]] = {
      case "Type.Bounds" =>
        getOptionField[Type](xs).flatMap { case (xs, lo) =>
          getOptionField[Type](xs).map { case (xs, hi) =>
            xs -> Type.Bounds(lo, hi)
          }
        }
    }

  }


  val patConverter = new TreeConverter[Pat] {
    def toMeta(tree: Pat): List[MetaTree] = tree match {
      // @ast class Var(name: scala.meta.Term.Name) extends Pat with Member.Term {
      //   // NOTE: can't do this check here because of things like `val X = 2`
      //   // checkFields(name.value(0).isLower)
      //   checkParent(ParentChecks.PatVar)
      // }
      case Pat.Var(name) =>
        TreeField("name", name) :: 
        Nil
      // @ast class Wildcard() extends Pat
      case Pat.Wildcard() => Nil
      // @ast class SeqWildcard() extends Pat {
      //   checkParent(ParentChecks.PatSeqWildcard)
      // }
      case Pat.SeqWildcard() => Nil
      // @ast class Bind(lhs: Pat, rhs: Pat) extends Pat {
      //   checkFields(lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
      // }
      case Pat.Bind(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
      case Pat.Alternative(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
      // @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
      //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
      // }
      case Pat.Tuple(args) =>
        TreeListField("args", args) :: 
        Nil
      // @ast class Extract(fun: Term, args: List[Pat]) extends Pat {
      //   checkFields(fun.isExtractor)
      // }
      case Pat.Extract(fun, args) =>
        TreeField("fun", fun) :: TreeListField("args", args) :: 
        Nil
      // @ast class ExtractInfix(lhs: Pat, op: Term.Name, rhs: List[Pat]) extends Pat
      case Pat.ExtractInfix(lhs, op, rhs) =>
        TreeField("lhs", lhs) :: TreeField("op", op) :: TreeListField("rhs", rhs) :: 
        Nil
      // @ast class Interpolate(prefix: Term.Name, parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
      //   checkFields(parts.length == args.length + 1)
      // }
      case Pat.Interpolate(prefix, parts, args) =>
        TreeField("prefix", prefix) :: TreeListField("parts", parts) :: TreeListField("args", args) :: 
        Nil
      // @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
      //   checkFields(parts.length == args.length + 1)
      // }
      case Pat.Xml(parts, args) =>
        TreeListField("parts", parts) :: TreeListField("args", args) :: 
        Nil
      // @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
      //   checkFields(lhs.is[Pat.Wildcard] || lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
      //   checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
      // }
      case Pat.Typed(lhs, rhs) =>
        TreeField("lhs", lhs) :: TreeField("rhs", rhs) :: 
        Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Pat)]] = {
      case s if s.startsWith("Pat") => s match {
        // @ast class Var(name: scala.meta.Term.Name) extends Pat with Member.Term {
        //   // NOTE: can't do this check here because of things like `val X = 2`
        //   // checkFields(name.value(0).isLower)
        //   checkParent(ParentChecks.PatVar)
        // }
        case "Pat.Var" =>
          getField[Term.Name](xs).map { case (xs, name) =>
            xs -> Pat.Var(name)
          }
        // @ast class Wildcard() extends Pat
        case "Pat.Wildcard" => Right(xs -> Pat.Wildcard())
        // @ast class SeqWildcard() extends Pat {
        //   checkParent(ParentChecks.PatSeqWildcard)
        // }
        case "Pat.SeqWildcard" => Right(xs -> Pat.SeqWildcard())
        // @ast class Bind(lhs: Pat, rhs: Pat) extends Pat {
        //   checkFields(lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
        // }
        case "Pat.Bind" =>
          getField[Pat](xs).flatMap { case (xs, lhs) =>
            getField[Pat](xs).map { case (xs, rhs) =>
              xs -> Pat.Bind(lhs, rhs)
            }
          }
        // @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
        case "Pat.Alternative" =>
          getField[Pat](xs).flatMap { case (xs, lhs) =>
            getField[Pat](xs).map { case (xs, rhs) =>
              xs -> Pat.Alternative(lhs, rhs)
            }
          }
        // @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
        //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
        // }
        case "Pat.Tuple" =>
          getListField[Pat](xs).map { case (xs, args) =>
            xs -> Pat.Tuple(args)
          }
        // @ast class Extract(fun: Term, args: List[Pat]) extends Pat {
        //   checkFields(fun.isExtractor)
        // }
        case "Pat.Extract" =>
          getField[Term](xs).flatMap { case (xs, fun) =>
            getListField[Pat](xs).map { case (xs, args) =>
              xs -> Pat.Extract(fun, args)
            }
          }
        // @ast class ExtractInfix(lhs: Pat, op: Term.Name, rhs: List[Pat]) extends Pat
        case "Pat.ExtractInfix" =>
          getField[Pat](xs).flatMap { case (xs, lhs) =>
            getField[Term.Name](xs).flatMap { case (xs, op) =>
              getListField[Pat](xs).map { case (xs, rhs) =>
                xs -> Pat.ExtractInfix(lhs, op, rhs)
              }
            }
          }
        // @ast class Interpolate(prefix: Term.Name, parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
        //   checkFields(parts.length == args.length + 1)
        // }
        case "Type.Interpolate" =>
          getField[Term.Name](xs).flatMap { case (xs, prefix) =>
            getListField[Lit](xs).flatMap { case (xs, parts) =>
              getListField[Pat](xs).map { case (xs, args) =>
                xs -> Pat.Interpolate(prefix, parts, args)
              }
            }
          }
        // @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
        //   checkFields(parts.length == args.length + 1)
        // }
        case "Pat.Xml" =>
          getListField[Lit](xs).flatMap { case (xs, parts) =>
            getListField[Pat](xs).map { case (xs, args) =>
              xs -> Pat.Xml(parts, args)
            }
          }
        // @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
        //   checkFields(lhs.is[Pat.Wildcard] || lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
        //   checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
        // }
        case "Pat.Typed" =>
          getField[Pat](xs).flatMap { case (xs, lhs) =>
            getField[Type](xs).map { case (xs, rhs) =>
              xs -> Pat.Typed(lhs, rhs)
            }
          }
      }
    }

  }

  val declConverter = new TreeConverter[Decl] {
    def toMeta(tree: Decl): List[MetaTree] = tree match {
      // @branch trait Decl extends Stat
      // object Decl {
      //   @ast class Val(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: scala.meta.Type) extends Decl
      case Decl.Val(mods, pats, decltpe) =>
        TreeListField("mods", mods) :: TreeListField("pats", pats) :: TreeField("decltpe", decltpe) :: 
        Nil
      //   @ast class Var(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: scala.meta.Type) extends Decl
      case Decl.Var(mods, pats, decltpe) =>
        TreeListField("mods", mods) :: TreeListField("pats", pats) :: TreeField("decltpe", decltpe) :: 
        Nil
      //   @ast class Def(mods: List[Mod],
      //                  name: Term.Name,
      //                  tparams: List[scala.meta.Type.Param],
      //                  paramss: List[List[Term.Param]],
      //                  decltpe: scala.meta.Type) extends Decl with Member.Term
      case Decl.Def(mods, name, tparams, paramss, decltpe) =>
        TreeListField("mods", mods) :: TreeField("name", name) ::
        TreeListField("tparams", tparams) :: TreeListListField("paramss", paramss) :: TreeField("decltpe", decltpe) :: 
        Nil
      //   @ast class Type(mods: List[Mod],
      //                   name: scala.meta.Type.Name,
      //                   tparams: List[scala.meta.Type.Param],
      //                   bounds: scala.meta.Type.Bounds) extends Decl with Member.Type
      // }
      case Decl.Type(mods, name, tparams, bounds) =>
        TreeListField("mods", mods) :: TreeField("name", name) ::
        TreeListField("tparams", tparams) :: TreeField("bounds", bounds) :: 
        Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Decl)]] = {
      case s if s.startsWith("Decl") => s match {
        // @branch trait Decl extends Stat
        // object Decl {
        //   @ast class Val(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: scala.meta.Type) extends Decl
        case "Decl.Val" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getListField[Pat](xs).flatMap { case (xs, pats) =>
              getField[Type](xs).map { case (xs, decltpe) =>
                xs -> Decl.Val(mods, pats, decltpe)
              }
            }
          }
        //   @ast class Var(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: scala.meta.Type) extends Decl
        case "Decl.Var" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getListField[Pat](xs).flatMap { case (xs, pats) =>
              getField[Type](xs).map { case (xs, decltpe) =>
                xs -> Decl.Var(mods, pats, decltpe)
              }
            }
          }

        case "Decl.Def" =>
        //   @ast class Def(mods: List[Mod],
        //                  name: Term.Name,
        //                  tparams: List[scala.meta.Type.Param],
        //                  paramss: List[List[Term.Param]],
        //                  decltpe: scala.meta.Type) extends Decl with Member.Term
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Term.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getListListField[Term.Param](xs).flatMap { case (xs, paramss) =>
                  getField[Type](xs).map { case (xs, decltpe) =>
                    xs -> Decl.Def(mods, name, tparams, paramss, decltpe)
                  }
                }
              }
            }
          }
        //   @ast class Type(mods: List[Mod],
        //                   name: scala.meta.Type.Name,
        //                   tparams: List[scala.meta.Type.Param],
        //                   bounds: scala.meta.Type.Bounds) extends Decl with Member.Type
        // }
        case "Decl.Type" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Type.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getField[Type.Bounds](xs).map { case (xs, bounds) =>
                  xs -> Decl.Type(mods, name, tparams, bounds)
                }
              }
            }
          }
      }
    }
  }

  val defnConverter = new TreeConverter[Defn] {
    def toMeta(tree: Defn): List[MetaTree] = tree match {
      // @branch trait Defn extends Stat
      // object Defn {
      //   @ast class Val(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: Option[scala.meta.Type],
      //                  rhs: Term) extends Defn {
      //     checkFields(pats.forall(!_.is[Term.Name]))
      //   }
      case Defn.Val(mods, pats, decltpe, rhs) =>
        TreeListField("mods", mods) :: TreeListField("pats", pats) :: 
        TreeOptionField("decltpe", decltpe) :: TreeField("rhs", rhs) ::
        Nil
      //   @ast class Var(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: Option[scala.meta.Type],
      //                  rhs: Option[Term]) extends Defn {
      //     checkFields(pats.forall(!_.is[Term.Name]))
      //     checkFields(decltpe.nonEmpty || rhs.nonEmpty)
      //     checkFields(rhs.isEmpty ==> pats.forall(_.is[Pat.Var]))
      //   }
      case Defn.Var(mods, pats, decltpe, rhs) =>
        TreeListField("mods", mods) :: TreeListField("pats", pats) :: 
        TreeOptionField("decltpe", decltpe) :: TreeOptionField("rhs", rhs) ::
        Nil
      //   @ast class Def(mods: List[Mod],
      //                  name: Term.Name,
      //                  tparams: List[scala.meta.Type.Param],
      //                  paramss: List[List[Term.Param]],
      //                  decltpe: Option[scala.meta.Type],
      //                  body: Term) extends Defn with Member.Term
      case Defn.Def(mods, name, tparams, paramss, decltpe, body) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeListField("tparams", tparams) :: TreeListListField("paramss", paramss) :: 
        TreeOptionField("decltpe", decltpe) :: TreeField("body", body) ::
        Nil
      //   @ast class Macro(mods: List[Mod],
      //                    name: Term.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    paramss: List[List[Term.Param]],
      //                    decltpe: Option[scala.meta.Type],
      //                    body: Term) extends Defn with Member.Term
      case Defn.Macro(mods, name, tparams, paramss, decltpe, body) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeListField("tparams", tparams) :: TreeListListField("paramss", paramss) :: 
        TreeOptionField("decltpe", decltpe) :: TreeField("body", body) ::
        Nil
      //   @ast class Type(mods: List[Mod],
      //                   name: scala.meta.Type.Name,
      //                   tparams: List[scala.meta.Type.Param],
      //                   body: scala.meta.Type) extends Defn with Member.Type
      case Defn.Type(mods, name, tparams, body) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeListField("tparams", tparams) :: TreeField("body", body) ::
        Nil
      //   @ast class Class(mods: List[Mod],
      //                    name: scala.meta.Type.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    ctor: Ctor.Primary,
      //                    templ: Template) extends Defn with Member.Type
      case Defn.Class(mods, name, tparams, ctor, templ) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeListField("tparams", tparams) :: TreeField("ctor", ctor) :: TreeField("templ", templ) ::
        Nil
      //   @ast class Trait(mods: List[Mod],
      //                    name: scala.meta.Type.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    ctor: Ctor.Primary,
      //                    templ: Template) extends Defn with Member.Type {
      //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
      //   }
      case Defn.Trait(mods, name, tparams, ctor, templ) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeListField("tparams", tparams) :: TreeField("ctor", ctor) :: TreeField("templ", templ) ::
        Nil
      //   @ast class Object(mods: List[Mod],
      //                     name: Term.Name,
      //                     templ: Template) extends Defn with Member.Term {
      //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
      //   }
      case Defn.Object(mods, name, templ) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: 
        TreeField("templ", templ) ::
        Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Defn)]] = {
      case s if s.startsWith("Defn") => s match {
        // @branch trait Defn extends Stat
        // object Defn {
        //   @ast class Val(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: Option[scala.meta.Type],
        //                  rhs: Term) extends Defn {
        //     checkFields(pats.forall(!_.is[Term.Name]))
        //   }
        case "Defn.Val" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getListField[Pat](xs).flatMap { case (xs, pats) =>
              getOptionField[Type](xs).flatMap { case (xs, decltpe) =>
                getField[Term](xs).map { case (xs, rhs) =>
                  xs -> Defn.Val(mods, pats, decltpe, rhs)
                }
              }
            }
          }
        //   @ast class Var(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: Option[scala.meta.Type],
        //                  rhs: Option[Term]) extends Defn {
        //     checkFields(pats.forall(!_.is[Term.Name]))
        //     checkFields(decltpe.nonEmpty || rhs.nonEmpty)
        //     checkFields(rhs.isEmpty ==> pats.forall(_.is[Pat.Var]))
        //   }
        case "Defn.Var" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getListField[Pat](xs).flatMap { case (xs, pats) =>
              getOptionField[Type](xs).flatMap { case (xs, decltpe) =>
                getOptionField[Term](xs).map { case (xs, rhs) =>
                  xs -> Defn.Var(mods, pats, decltpe, rhs)
                }
              }
            }
          }
        //   @ast class Def(mods: List[Mod],
        //                  name: Term.Name,
        //                  tparams: List[scala.meta.Type.Param],
        //                  paramss: List[List[Term.Param]],
        //                  decltpe: Option[scala.meta.Type],
        //                  body: Term) extends Defn with Member.Term
        case "Defn.Def" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Term.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getListListField[Term.Param](xs).flatMap { case (xs, paramss) =>
                  getOptionField[Type](xs).flatMap { case (xs, decltpe) =>
                    getField[Term](xs).map { case (xs, body) =>
                      xs -> Defn.Def(mods, name, tparams, paramss, decltpe, body)
                    }
                  }
                }
              }
            }
          }
        //   @ast class Macro(mods: List[Mod],
        //                    name: Term.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    paramss: List[List[Term.Param]],
        //                    decltpe: Option[scala.meta.Type],
        //                    body: Term) extends Defn with Member.Term
        case "Defn.Macro" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Term.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getListListField[Term.Param](xs).flatMap { case (xs, paramss) =>
                  getOptionField[Type](xs).flatMap { case (xs, decltpe) =>
                    getField[Term](xs).map { case (xs, body) =>
                      xs -> Defn.Macro(mods, name, tparams, paramss, decltpe, body)
                    }
                  }
                }
              }
            }
          }
        //   @ast class Type(mods: List[Mod],
        //                   name: scala.meta.Type.Name,
        //                   tparams: List[scala.meta.Type.Param],
        //                   body: scala.meta.Type) extends Defn with Member.Type
        case "Defn.Type" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Type.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getField[Type](xs).map { case (xs, body) =>
                  xs -> Defn.Type(mods, name, tparams, body)
                }
              }
            }
          }
        //   @ast class Class(mods: List[Mod],
        //                    name: scala.meta.Type.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    ctor: Ctor.Primary,
        //                    templ: Template) extends Defn with Member.Type
        case "Defn.Class" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Type.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getField[Ctor.Primary](xs).flatMap { case (xs, ctor) =>
                  getField[Template](xs).map { case (xs, templ) =>
                    xs -> Defn.Class(mods, name, tparams, ctor, templ)
                  }
                }
              }
            }
          }
        //   @ast class Trait(mods: List[Mod],
        //                    name: scala.meta.Type.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    ctor: Ctor.Primary,
        //                    templ: Template) extends Defn with Member.Type {
        //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
        //   }
        case "Defn.Trait" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Type.Name](xs).flatMap { case (xs, name) =>
              getListField[Type.Param](xs).flatMap { case (xs, tparams) =>
                getField[Ctor.Primary](xs).flatMap { case (xs, ctor) =>
                  getField[Template](xs).map { case (xs, templ) =>
                    xs -> Defn.Trait(mods, name, tparams, ctor, templ)
                  }
                }
              }
            }
          }
        //   @ast class Object(mods: List[Mod],
        //                     name: Term.Name,
        //                     templ: Template) extends Defn with Member.Term {
        //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
        //   }
        case "Defn.Object" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Term.Name](xs).flatMap { case (xs, name) =>
              getField[Template](xs).map { case (xs, templ) =>
                xs -> Defn.Object(mods, name, templ)
              }
            }
          }
      }
    }

  }



  val pkgConverter = new TreeConverter[Pkg] {
    // class Pkg(ref: Term.Ref, stats: List[Stat])
    def toMeta(tree: Pkg): List[MetaTree] = {
      TreeField("ref", tree.ref) :: TreeListField("stats", tree.stats) :: Nil
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Pkg)]] = {
      case "Pkg" =>
        getField[Term.Ref](xs).flatMap { case (xs, ref) =>
          getListField[Stat](xs).map { case (xs, stats) =>
            xs -> Pkg(ref, stats)
          }
        }
    }

  }
  
  val ctorConverter = new TreeConverter[Ctor] {
    def toMeta(tree: Ctor): List[MetaTree] = tree match {
      // @branch trait m extends Tree with Member
      // object Ctor {
      //   @ast class Primary(mods: List[Mod],
      //                      name: Name,
      //                      paramss: List[List[Term.Param]]) extends Ctor
      case Ctor.Primary(mods, name, paramss) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: TreeListListField("paramss", paramss) :: Nil
      //   @ast class Secondary(mods: List[Mod],
      //                        name: Name,
      //                        paramss: List[List[Term.Param]] @nonEmpty,
      //                        init: Init,
      //                        stats: List[Stat]) extends Ctor with Stat {
      //     checkFields(stats.forall(_.isBlockStat))
      //   }
      case Ctor.Secondary(mods, name, paramss, init, stats) =>
        TreeListField("mods", mods) :: TreeField("name", name) :: TreeListListField("paramss", paramss) :: 
        TreeField("init", init) :: TreeListField("stats", stats) :: 
        Nil
      // }

    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Ctor)]] = {
      case s if s.startsWith("Ctor") => s match {
      // @branch trait m extends Tree with Member
      // object Ctor {
      //   @ast class Primary(mods: List[Mod],
      //                      name: Name,
      //                      paramss: List[List[Term.Param]]) extends Ctor
        case "Ctor.Primary" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Name](xs).flatMap { case (xs, name) =>
              getListListField[Term.Param](xs).map { case (xs, paramss) =>
                xs -> Ctor.Primary(mods, name, paramss)
              }
            }
          }
      //   @ast class Secondary(mods: List[Mod],
      //                        name: Name,
      //                        paramss: List[List[Term.Param]] @nonEmpty,
      //                        init: Init,
      //                        stats: List[Stat]) extends Ctor with Stat {
      //     checkFields(stats.forall(_.isBlockStat))
      //   }
      // }
        case "Ctor.Secondary" =>
          getListField[Mod](xs).flatMap { case (xs, mods) =>
            getField[Name](xs).flatMap { case (xs, name) =>
              getListListField[Term.Param](xs).flatMap { case (xs, paramss) =>
                getField[Init](xs).flatMap { case (xs, init) =>
                  getListField[Stat](xs).map { case (xs, stats) =>
                    xs -> Ctor.Secondary(mods, name, paramss, init, stats)
                  }
                }
              }
            }
          }
      }
    }

  }

  val modConverter = new TreeConverter[Mod] {
    def toMeta(tree: Mod): List[MetaTree] = tree match {
      // @branch trait Mod extends Tree
      // object Mod {
      //   @ast class Annot(init: Init) extends Mod {
      //     @deprecated("Use init instead", "1.9.0")
      //     def body = init
      //   }
      case Mod.Annot(init) =>
        TreeField("init", init) :: Nil

      //   @ast class Private(within: Ref) extends Mod {
      //     checkFields(within.isWithin)
      //   }
      case Mod.Private(within) =>
        TreeField("within", within) :: Nil

      //   @ast class Protected(within: Ref) extends Mod {
      //     checkFields(within.isWithin)
      //   }
      case Mod.Protected(within) =>
        TreeField("within", within) :: Nil

      //   @ast class Implicit() extends Mod
      case Mod.Implicit() =>
        Nil
      //   @ast class Final() extends Mod
      case Mod.Final() =>
        Nil
      //   @ast class Sealed() extends Mod
      case Mod.Sealed() =>
        Nil
      //   @ast class Override() extends Mod
      case Mod.Override() =>
        Nil
      //   @ast class Case() extends Mod
      case Mod.Case() =>
        Nil
      //   @ast class Abstract() extends Mod
      case Mod.Abstract() =>
        Nil
      //   @ast class Covariant() extends Mod
      case Mod.Covariant() =>
        Nil
      //   @ast class Contravariant() extends Mod
      case Mod.Contravariant() =>
        Nil
      //   @ast class Lazy() extends Mod
      case Mod.Lazy() =>
        Nil
      //   @ast class ValParam() extends Mod
      case Mod.ValParam() =>
        Nil
      //   @ast class VarParam() extends Mod
      case Mod.VarParam() =>
        Nil
      //   @ast class Inline() extends Mod
      case Mod.Inline() =>
        Nil
      // }

    }


    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Mod)]] = {
      case s if s.startsWith("Mod") => s match {
      // @branch trait Mod extends Tree
      // object Mod {
      //   @ast class Annot(init: Init) extends Mod {
      //     @deprecated("Use init instead", "1.9.0")
      //     def body = init
      //   }
        case "Mod.Annot" =>
          getField[Init](xs).map { case (xs, init) =>
            xs -> Mod.Annot(init)
          }
      //   @ast class Private(within: Ref) extends Mod {
      //     checkFields(within.isWithin)
      //   }
        case "Mod.Private" =>
          getField[Ref](xs).map { case (xs, within) =>
            xs -> Mod.Private(within)
          }
      //   @ast class Protected(within: Ref) extends Mod {
      //     checkFields(within.isWithin)
      //   }
        case "Mod.Protected" =>
          getField[Ref](xs).map { case (xs, within) =>
            xs -> Mod.Protected(within)
          }
      //   @ast class Implicit() extends Mod
        case "Mod.Implicit" =>
          Right(xs -> Mod.Implicit())
      //   @ast class Final() extends Mod
        case "Mod.Final" =>
          Right(xs -> Mod.Final())
      //   @ast class Sealed() extends Mod
        case "Mod.Sealed" =>
          Right(xs -> Mod.Sealed())
      //   @ast class Override() extends Mod
        case "Mod.Override" =>
          Right(xs -> Mod.Override())
      //   @ast class Case() extends Mod
        case "Mod.Case" =>
          Right(xs -> Mod.Case())
      //   @ast class Abstract() extends Mod
        case "Mod.Abstract" =>
          Right(xs -> Mod.Abstract())
      //   @ast class Covariant() extends Mod
        case "Mod.Covariant" =>
          Right(xs -> Mod.Covariant())
      //   @ast class Contravariant() extends Mod
        case "Mod.Contravariant" =>
          Right(xs -> Mod.Contravariant())
      //   @ast class Lazy() extends Mod
        case "Mod.Lazy" =>
          Right(xs -> Mod.Lazy())
      //   @ast class ValParam() extends Mod
        case "Mod.ValParam" =>
          Right(xs -> Mod.ValParam())
      //   @ast class VarParam() extends Mod
        case "Mod.VarParam" =>
          Right(xs -> Mod.VarParam())
      //   @ast class Inline() extends Mod
        case "Mod.Inline" =>
          Right(xs -> Mod.Inline())
      // }

      }
    }
  }


  val enumeratorConverter = new TreeConverter[Enumerator] {
    def toMeta(tree: Enumerator): List[MetaTree] = tree match {
      // @branch trait Enumerator extends Tree
      // object Enumerator {
      //   @ast class Generator(pat: Pat, rhs: Term) extends Enumerator
      case Enumerator.Generator(pat, rhs) =>
        TreeField("pat", pat) :: TreeField("rhs", rhs) :: Nil
      //   @ast class Val(pat: Pat, rhs: Term) extends Enumerator
      case Enumerator.Val(pat, rhs) =>
        TreeField("pat", pat) :: TreeField("rhs", rhs) :: Nil
      //   @ast class Guard(cond: Term) extends Enumerator
      case Enumerator.Guard(cond) =>
        TreeField("cond", cond) :: Nil
      // }
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Enumerator)]] = {
      case s if s.startsWith("Enumerator") => s match {
      // @branch trait Enumerator extends Tree
      // object Enumerator {
      //   @ast class Generator(pat: Pat, rhs: Term) extends Enumerator
        case "Enumerator.Generator" =>
          getField[Pat](xs).flatMap { case (xs, pat) =>
            getField[Term](xs).map { case (xs, rhs) =>
              xs -> Enumerator.Generator(pat, rhs)
            }
          }
      //   @ast class Val(pat: Pat, rhs: Term) extends Enumerator
        case "Enumerator.Val" =>
          getField[Pat](xs).flatMap { case (xs, pat) =>
            getField[Term](xs).map { case (xs, rhs) =>
              xs -> Enumerator.Val(pat, rhs)
            }
          }
      //   @ast class Guard(cond: Term) extends Enumerator
        case "Enumerator.Guard" =>
          getField[Term](xs).map { case (xs, cond) =>
            xs -> Enumerator.Guard(cond)
          }
      // }
      }
    }
  }

  val importeeConverter = new TreeConverter[Importee] {
    def toMeta(tree: Importee): List[MetaTree] = tree match {
    // @branch trait Importee extends Tree with Ref
    // object Importee {
    //   @ast class Wildcard() extends Importee
      case Importee.Wildcard() =>
        Nil
    //   @ast class Name(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
      case Importee.Name(name) =>
        TreeField("name", name) :: Nil
    //   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
    //   }
      case Importee.Rename(name, rename) =>
        TreeField("name", name) :: TreeField("rename", rename) :: Nil
    //   @ast class Unimport(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
      case Importee.Unimport(name) =>
        TreeField("name", name) :: Nil
    // }
    }

    def fromMeta(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Importee)]] = {
      case s if s.startsWith("Importee") => s match {
    // @branch trait Importee extends Tree with Ref
    // object Importee {
    //   @ast class Wildcard() extends Importee
        case "Importee.Wildcard" => Right(xs -> Importee.Wildcard())

    //   @ast class Name(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
        case "Importee.Name" =>
          getField[Name](xs).map { case (xs, name) =>
            xs -> Importee.Name(name)
          }
    //   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
    //   }
        case "Importee.Rename" =>
          getField[Name](xs).flatMap { case (xs, name) =>
            getField[Name](xs).map { case (xs, rename) =>
              xs -> Importee.Rename(name, rename)
            }
          }
    //   @ast class Unimport(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
    // }
        case "Importee.Unimport" =>
          getField[Name](xs).map { case (xs, name) =>
            xs -> Importee.Unimport(name)
          }
      }
    }
  }


  def fieldChildren(tree: Tree): List[MetaTree] = {
    val ls = tree match {
      case x:Name => Nil

      case x:Lit => Nil

      case x:Term => termConverter.toMeta(x)

      case x:Term.Param => termParamConverter.toMeta(x)

      case x:Type => typeConverter.toMeta(x)

      case x:Pat => patConverter.toMeta(x)

      case x:Decl => declConverter.toMeta(x)

      case x:Defn => defnConverter.toMeta(x)

      case x:Pkg => pkgConverter.toMeta(x)

      case x:Ctor => ctorConverter.toMeta(x)

      case x:Mod => modConverter.toMeta(x)

      case x:Enumerator => enumeratorConverter.toMeta(x)

      case x:Importee => importeeConverter.toMeta(x)

      // @ast class Self(name: Name, decltpe: Option[Type]) extends Member
      case Self(name, decltpe) =>
        TreeField("name", name) :: TreeOptionField("decltpe", decltpe) :: Nil

      // @ast class Template(early: List[Stat],
      //                     inits: List[Init],
      //                     self: Self,
      //                     stats: List[Stat]) extends Tree {
      //   checkFields(early.forall(_.isEarlyStat && inits.nonEmpty))
      //   checkFields(stats.forall(_.isTemplateStat))
      // }
      case Template(early, inits, self, stats) =>
        TreeListField("early", early) :: TreeListField("inits", inits) :: TreeField("self", self) ::
        TreeListField("stats", stats) :: Nil

      // @ast class Init(tpe: Type, name: Name, argss: List[List[Term]]) extends Ref {
      //   checkFields(tpe.isConstructable)
      //   checkParent(ParentChecks.Init)
      // }
      case Init(tpe, name, argss) =>
        TreeField("tpe", tpe) :: TreeField("name", name) :: TreeListListField("argss", argss) :: Nil

      // @ast class Import(importers: List[Importer] @nonEmpty) extends Stat
      case Import(importers) =>
        TreeListField("importers", importers) :: Nil

      // @ast class Importer(ref: Term.Ref, importees: List[Importee] @nonEmpty) extends Tree {
      //   checkFields(ref.isStableId)
      // }
      case Importer(ref, importees) =>
        TreeField("ref", ref) :: TreeListField("importees", importees) :: Nil

      // @ast class Case(pat: Pat, cond: Option[Term], body: Term) extends Tree
      case Case(pat, cond, body) =>
        TreeField("pat", pat) :: TreeOptionField("cond", cond) :: TreeField("body", body) :: Nil

      // @ast class Source(stats: List[Stat]) extends Tree {
      case Source(stats) =>
        TreeListField("stats", stats) :: Nil

    }

    // ls :+ PosField(tree.origin)
    ls
  }


  def rebuildTree(xs: List[MetaTree]): PartialFunction[String, PatchError[(List[MetaTree], Tree)]] = {
    val f: PartialFunction[String, PatchError[(List[MetaTree], Tree)]] = termParamConverter.fromMeta(xs) orElse termConverter.fromMeta(xs) orElse
    typeParamConverter.fromMeta(xs) orElse typeBoundsConverter.fromMeta(xs) orElse typeConverter.fromMeta(xs) orElse
    patConverter.fromMeta(xs) orElse declConverter.fromMeta(xs) orElse defnConverter.fromMeta(xs) orElse
    pkgConverter.fromMeta(xs) orElse ctorConverter.fromMeta(xs) orElse modConverter.fromMeta(xs) orElse
    enumeratorConverter.fromMeta(xs) orElse importeeConverter.fromMeta(xs) orElse
    {
      // @ast class Self(name: Name, decltpe: Option[Type]) extends Member
      case "Self" =>
        getField[Name](xs).flatMap { case (xs, name) =>
          getOptionField[Type](xs).map { case (xs, decltpe) =>
            xs -> Self(name, decltpe)
          }
        }

      // @ast class Template(early: List[Stat],
      //                     inits: List[Init],
      //                     self: Self,
      //                     stats: List[Stat]) extends Tree {
      //   checkFields(early.forall(_.isEarlyStat && inits.nonEmpty))
      //   checkFields(stats.forall(_.isTemplateStat))
      // }
      case "Template" =>
        getListField[Stat](xs).flatMap { case (xs, early) =>
          getListField[Init](xs).flatMap { case (xs, inits) =>
            getField[Self](xs).flatMap { case (xs, self) =>
              getListField[Stat](xs).map { case (xs, stats) =>
                xs -> Template(early, inits, self, stats)
              }
            }
          }
        }
      // @ast class Init(tpe: Type, name: Name, argss: List[List[Term]]) extends Ref {
      //   checkFields(tpe.isConstructable)
      //   checkParent(ParentChecks.Init)
      // }
      case "Init" =>
        getField[Type](xs).flatMap { case (xs, tpe) =>
          getField[Name](xs).flatMap { case (xs, name) =>
            getListListField[Term](xs).map { case (xs, argss) =>
              xs -> Init(tpe, name, argss)
            }
          }
        }

      // @ast class Import(importers: List[Importer] @nonEmpty) extends Stat
      case "Import" =>
        getListField[Importer](xs).map { case (xs, importers) =>
          xs -> Import(importers)
        }
      // @ast class Importer(ref: Term.Ref, importees: List[Importee] @nonEmpty) extends Tree {
      //   checkFields(ref.isStableId)
      // }
      case "Importer" =>
        getField[Term.Ref](xs).flatMap { case (xs, ref) =>
          getListField[Importee](xs).map { case (xs, importees) =>
            xs -> Importer(ref, importees)
          }
        }

      // @ast class Case(pat: Pat, cond: Option[Term], body: Term) extends Tree
      case "Case" =>
        getField[Pat](xs).flatMap { case (xs, pat) =>
          getOptionField[Term](xs).flatMap { case (xs, cond) =>
            getField[Term](xs).map { case (xs, body) =>
              xs -> Case(pat, cond, body)
            }
          }
        }
      // @ast class Source(stats: List[Stat]) extends Tree {
      case "Source" =>
        getListField[Stat](xs).map { case (xs, stats) =>
          xs -> Source(stats)
        }

    }
    f
    // f andThen { s =>
    //   s.flatMap { case (xs, tree) => 
    //     getPosField(xs).map { case (xs, origin) =>
    //       xs -> tree.withOrigin(origin)
    //     }
    //   }
    // }
  }
}
