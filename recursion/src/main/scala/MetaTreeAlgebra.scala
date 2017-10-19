package scala.meta
package fix

import matryoshka._
import matryoshka.implicits._
import scalaz.StateT
import scalaz.std.either._

import MetaTree._

trait MetaTreeAlgebra {

  def getField[A <: Tree](name: String) = StateT[MetaError, List[Field[Tree]], A] {
    case Nil =>
      Left(s"can't get field $name, empty list of fields")

    case SimpleField(`name`, f) :: xs =>
      Right((xs, f.asInstanceOf[A]))

    case f :: xs =>
      Left(s"can't get field $name, found field $f")
  }

  def getListField[A <: Tree](name: String) = StateT[MetaError, List[Field[Tree]], List[A]] {
    case Nil =>
      Left(s"can't get listfield $name, empty list of fields")

    case ListField(`name`, fs) :: xs =>
      Right((xs, fs.asInstanceOf[List[A]]))

    case f :: xs =>
      Left(s"can't get listfield $name, found field $f")
  }

  def getOptionField[A <: Tree](name: String) = StateT[MetaError, List[Field[Tree]], Option[A]] {
    case Nil =>
      Left(s"can't get optionfield $name, empty list of fields")

    case OptionField(`name`, f) :: xs =>
      Right((xs, f.asInstanceOf[Option[A]]))

    case f :: xs =>
      Left(s"can't get optionfield $name, found field $f")
  }


  def getListListField[A <: Tree](name: String) = StateT[MetaError, List[Field[Tree]], List[List[A]]] {
    case Nil =>
      Left(s"can't get listlistfield $name, empty list of fields")

    case ListListField(`name`, fss) :: xs =>
      Right((xs, fss.asInstanceOf[List[List[A]]]))

    case f :: xs =>
      Left(s"can't get listlistfield $name, found field $f")
  }

  val termParamState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Term.Param]] = {
    case "Term.Param" => for { 
      mods <- getListField[Mod]("mods")
      name <- getField[Term.Name]("name")
      decltpe <- getOptionField[Type]("decltpe")
      default <- getOptionField[Term]("default")
    } yield {
      Term.Param(mods, name, decltpe, default)
    }
  }

  val termState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Term]] = {
    case tpe if tpe.startsWith("Term") => tpe match {
      case "Term.This" => for {
        qual <- getField[Name]("qual")
      } yield {
        Term.This(qual)
      }

      case "Term.Super" => for {
        thisp <- getField[Name]("thisp")
        superp <- getField[Name]("superp")
      } yield {
        Term.Super(thisp, superp)
      }
    //   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
    //   @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
      case "Term.Select" => for {
        qual <- getField[Term]("qual")
        name <- getField[Term.Name]("name")
      } yield {
        Term.Select(qual, name)
      }
    //   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
    //     checkFields(parts.length == args.length + 1)
    //   }
      case "Term.Interpolate" => for {
        prefix <- getField[Term.Name]("prefix")
        parts <- getListField[Lit]("parts")
        args <- getListField[Term]("args")
      } yield {
        Term.Interpolate(prefix, parts, args)
      }
    //   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
    //     checkFields(parts.length == args.length + 1)
    //   }
      case "Term.Xml" => for {
        parts <- getListField[Lit]("parts")
        args <- getListField[Term]("args")
      } yield {
        Term.Xml(parts, args)
      }

    //   @ast class Apply(fun: Term, args: List[Term]) extends Term
      case "Term.Apply" => for {
        fun <- getField[Term]("fun")
        args <- getListField[Term]("args")
      } yield {
        Term.Apply(fun, args)
      }
    //   @ast class ApplyType(fun: Term, targs: List[Type] @nonEmpty) extends Term
      case "Term.ApplyType" => for {
        fun <- getField[Term]("fun")
        targs <- getListField[Type]("targs")
      } yield {
        Term.ApplyType(fun, targs)
      }
    //   @ast class ApplyInfix(lhs: Term, op: Name, targs: List[Type], args: List[Term]) extends Term
      case "Term.ApplyInfix" => for {
        lhs <- getField[Term]("lhs")
        op <- getField[Term.Name]("op")
        targs <- getListField[Type]("targs")
        args <- getListField[Term]("args")
      } yield {
        Term.ApplyInfix(lhs, op, targs, args)
      }
    //   @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
    //     checkFields(op.isUnaryOp)
    //   }
      case "Term.ApplyUnary" => for {
        op <- getField[Term.Name]("op")
        arg <- getField[Term]("arg")
      } yield {
        Term.ApplyUnary(op, arg)
      }
    //   @ast class Assign(lhs: Term, rhs: Term) extends Term {
    //     checkFields(lhs.is[Term.Quasi] || lhs.is[Term.Ref] || lhs.is[Term.Apply])
    //     checkParent(ParentChecks.TermAssign)
    //   }
      case "Term.Assign" => for {
        lhs <- getField[Term]("lhs")
        rhs <- getField[Term]("rhs")
      } yield {
        Term.Assign(lhs, rhs)
      }
    //   @ast class Return(expr: Term) extends Term
      case "Term.Return" => for {
        expr <- getField[Term]("expr")
      } yield {
        Term.Return(expr)
      }
    //   @ast class Throw(expr: Term) extends Term
      case "Term.Throw" => for {
        expr <- getField[Term]("expr")
      } yield {
        Term.Throw(expr)
      }
    //   @ast class Ascribe(expr: Term, tpe: Type) extends Term
      case "Term.Ascribe" => for {
        expr <- getField[Term]("expr")
        tpe <- getField[Type]("tpe")
      } yield {
        Term.Ascribe(expr, tpe)
      }
    //   @ast class Annotate(expr: Term, annots: List[Mod.Annot] @nonEmpty) extends Term
      case "Term.Annotate" => for {
        expr <- getField[Term]("expr")
        annots <- getListField[Mod.Annot]("annots")
      } yield {
        Term.Annotate(expr, annots)
      }
    //   @ast class Tuple(args: List[Term] @nonEmpty) extends Term {
    //     // tuple must have more than one element
    //     // however, this element may be Quasi with "hidden" list of elements inside
    //     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Term.Quasi]))
    //   }
      case "Term.Tuple" => for {
        args <- getListField[Term]("args")
      } yield {
        Term.Tuple(args)
      }
    //   @ast class Block(stats: List[Stat]) extends Term {
    //     checkFields(stats.forall(_.isBlockStat))
    //   }
      case "Term.Block" => for {
        stats <- getListField[Stat]("stats")
      } yield { 
        Term.Block(stats)
      }
    //   @ast class If(cond: Term, thenp: Term, elsep: Term) extends Term
      case "Term.If" => for {
        cond <- getField[Term]("cond")
        thenp <- getField[Term]("thenp")
        elsep <- getField[Term]("elsep")
      } yield {
        Term.If(cond, thenp, elsep)
      }
    //   @ast class Match(expr: Term, cases: List[Case] @nonEmpty) extends Term
      case "Term.Match" => for {
        expr <- getField[Term]("expr")
        cases <- getListField[Case]("cases")
      } yield {
        Term.Match(expr, cases)
      }
    //   @ast class Try(expr: Term, catchp: List[Case], finallyp: Option[Term]) extends Term
      case "Term.Try" => for {
        expr <- getField[Term]("expr")
        catchp <- getListField[Case]("catchp")
        finallyp <- getOptionField[Term]("finallyp")
      } yield {
        Term.Try(expr, catchp, finallyp)
      }
    //   @ast class TryWithHandler(expr: Term, catchp: Term, finallyp: Option[Term]) extends Term
      case "Term.TryWithHandler" => for { 
        expr <- getField[Term]("expr")
        catchp <- getField[Term]("catchp")
        finallyp <- getOptionField[Term]("finallyp")
      } yield {
        Term.TryWithHandler(expr, catchp, finallyp)
      }
    //   @ast class Function(params: List[Term.Param], body: Term) extends Term {
    //     checkFields(params.forall(param => param.is[Term.Param.Quasi] || (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)))
    //     checkFields(params.exists(_.is[Term.Param.Quasi]) || params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1))
    //   }
      case "Term.Function" => for {
        params <- getListField[Term.Param]("params")
        body <- getField[Term]("body")
      } yield {
        Term.Function(params, body)
      }
    //   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Term
      case "Term.PartialFunction" => for {
        cases <- getListField[Case]("cases")
      } yield {
        Term.PartialFunction(cases)
      }
    //   @ast class While(expr: Term, body: Term) extends Term
      case "Term.While" => for {
        expr <- getField[Term]("expr")
        body <- getField[Term]("body")
      } yield {
        Term.While(expr, body)
      }
    //   @ast class Do(body: Term, expr: Term) extends Term
      case "Term.Do" => for { 
        body <- getField[Term]("body")
        expr <- getField[Term]("expr")
      } yield {
        Term.Do(body, expr)
      }
    //   @ast class For(enums: List[Enumerator] @nonEmpty, body: Term) extends Term {
    //     checkFields(enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.Quasi])
    //   }
      case "Term.For" => for {
        enums <- getListField[Enumerator]("enums")
        body <- getField[Term]("body")
      } yield {
        Term.For(enums, body)
      }
    //   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Term) extends Term
      case "Term.ForYield" => for {
        enums <- getListField[Enumerator]("enums")
        body <- getField[Term]("body")
      } yield {
        Term.ForYield(enums, body)
      }
    //   @ast class New(init: Init) extends Term
      case "Term.New" => for { 
        init <- getField[Init]("init")
      } yield {
        Term.New(init)
      }
    //   @ast class NewAnonymous(templ: Template) extends Term
      case "Term.NewAnonymous" => for {
        templ <- getField[Template]("templ")
      } yield { 
        Term.NewAnonymous(templ)
      }
    //   @ast class Placeholder() extends Term
      case "Term.Placeholder" =>
        StateT[MetaError, List[Field[Tree]], Term] { xs => Right((xs, Term.Placeholder())) }

    //   @ast class Eta(expr: Term) extends Term
      case "Term.Eta" => for {
        expr <- getField[Term]("expr")
      } yield { 
        Term.Eta(expr)
      }
    //   @ast class Repeated(expr: Term) extends Term {
    //     checkParent(ParentChecks.TermRepeated)
    //   }
      case "Term.Repeated" => for { 
        expr <- getField[Term]("expr")
      } yield {
        Term.Repeated(expr)
      }
    }
  }

  val typeParamState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Type.Param]] = {
    case "Type.Param" => for {
      mods <- getListField[Mod]("mods")
      name <- getField[Term.Name]("name")
      tparams <- getListField[Type.Param]("tparams")
      tbounds <- getField[Type.Bounds]("tbounds")
      vbounds <- getListField[Type]("vbounds")
      cbounds <- getListField[Type]("cbounds")
    } yield {
      Type.Param(mods, name, tparams, tbounds, vbounds, cbounds)
    }
  }


  val typeState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Type]] = {
    case s if s.startsWith("Type") => s match {
      // @branch trait Ref extends Type with scala.meta.Ref
      // @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
      // @ast class Select(qual: Term.Ref, name: Type.Name) extends Type.Ref {
      case "Type.Select" => for {
        qual <- getField[Term.Ref]("qual")
        name <- getField[Type.Name]("name")
      } yield {
        Type.Select(qual, name)
      }
      //   checkFields(qual.isPath || qual.is[Term.Super] || qual.is[Term.Ref.Quasi])
      // }
      // @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
      case "Type.Project" => for {
        qual <- getField[Type]("qual")
        name <- getField[Type.Name]("name")
      } yield { 
        Type.Project(qual, name)
      }
      // @ast class Singleton(ref: Term.Ref) extends Type.Ref {
      //   checkFields(ref.isPath || ref.is[Term.Super])
      // }
      case "Type.Singleton" => for { 
        ref <- getField[Term.Ref]("ref")
      } yield {
        Type.Singleton(ref)
      }
      // @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
      case "Type.Apply" => for { 
        tpe <- getField[Type]("tpe")
        args <- getListField[Type]("args")
      } yield {
        Type.Apply(tpe, args)
      }
      // @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
      case "Type.ApplyInfix" => for {
        lhs <- getField[Type]("lhs")
        op <- getField[Type.Name]("op")
        rhs <- getField[Type]("rhs")
      } yield { 
        Type.ApplyInfix(lhs, op, rhs)
      }
      // @ast class Function(params: List[Type], res: Type) extends Type
      case "Type.Function" => for { 
        params <- getListField[Type]("params")
        res <- getField[Type]("res")
      } yield {
        Type.Function(params, res)
      }
      // @ast class ImplicitFunction(params: List[Type], res: Type) extends Type
      case "Type.ImplicitFunction" => for { 
        params <- getListField[Type]("params")
        res <- getField[Type]("res")
      } yield { 
        Type.ImplicitFunction(params, res)
      }
      // @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
      //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
      // }
      case "Type.Tuple" => for { 
        args <- getListField[Type]("args")
      } yield { 
        Type.Tuple(args)
      }
      // @ast class With(lhs: Type, rhs: Type) extends Type
      case "Type.With" => for { 
        lhs <- getField[Type]("lhs")
        rhs <- getField[Type]("rhs")
      } yield {
        Type.With(lhs, rhs)
      }
      // @ast class And(lhs: Type, rhs: Type) extends Type
      case "Type.And" => for { 
        lhs <- getField[Type]("lhs")
        rhs <- getField[Type]("rhs")
      } yield {
        Type.And(lhs, rhs)
      }
      // @ast class Or(lhs: Type, rhs: Type) extends Type
      case "Type.Or" => for { 
        lhs <- getField[Type]("lhs")
        rhs <- getField[Type]("rhs")
      } yield {
        Type.Or(lhs, rhs)
      }
      // @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
      //   checkFields(stats.forall(_.isRefineStat))
      // }
      case "Type.Refine" => for { 
        tpe <- getOptionField[Type]("tpe")
        stats <- getListField[Stat]("stats")
      } yield {
        Type.Refine(tpe, stats)
      }
      // @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
      //   checkFields(stats.forall(_.isExistentialStat))
      // }
      case "Type.Existential" => for { 
        tpe <- getField[Type]("tpe")
        stats <- getListField[Stat]("stats")
      } yield {
        Type.Existential(tpe, stats)
      }
      // @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
      case "Type.Annotate" => for { 
        tpe <- getField[Type]("tpe")
        annots <- getListField[Mod.Annot]("annots")
      } yield {
        Type.Annotate(tpe, annots)
      }
      // @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeLambda)
      // }
      case "Type.Lambda" => for { 
        tparams <- getListField[Type.Param]("tparams")
        tpe <- getField[Type]("tpe")
      } yield {  
        Type.Lambda(tparams, tpe)
      }
      // @ast class Method(paramss: List[List[Term.Param]], tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeMethod)
      // }
      case "Type.Method" => for { 
        paramss <- getListListField[Term.Param]("paramss")
        tpe <- getField[Type]("tpe")
      } yield { 
        Type.Method(paramss, tpe)
      }
      // @ast class Placeholder(bounds: Bounds) extends Type
      case "Type.Placeholder" => for {
        bounds <- getField[Type.Bounds]("bounds")
      } yield {
        Type.Placeholder(bounds)
      }

      // @ast class ByName(tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeByName)
      // }
      case "Type.ByName" => for {
        tpe <- getField[Type]("tpe")
      } yield { 
        Type.ByName(tpe)
      }
      // @ast class Repeated(tpe: Type) extends Type {
      //   checkParent(ParentChecks.TypeRepeated)
      // }
      case "Type.Repeated" => for {
        tpe <- getField[Type]("tpe")
      } yield { 
        Type.Repeated(tpe)
      }
      // @ast class Var(name: Name) extends Type with Member.Type {
      //   checkFields(name.value(0).isLower)
      //   checkParent(ParentChecks.TypeVar)
      // }
      case "Type.Var" => for {
        name <- getField[Type.Name]("name")
      } yield { 
        Type.Var(name)
      }
    }
  }

  val typeBoundsState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Type.Bounds]] = {
    case "Type.Bounds" => for {
      lo <- getOptionField[Type]("lo")
      hi <- getOptionField[Type]("hi")
    } yield {
      Type.Bounds(lo, hi)
    }
  }

  val patState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Pat]] = {
    case s if s.startsWith("Pat") => s match {
      // @ast class Var(name: scala.meta.Term.Name) extends Pat with Member.Term {
      //   // NOTE: can't do this check here because of things like `val X = 2`
      //   // checkFields(name.value(0).isLower)
      //   checkParent(ParentChecks.PatVar)
      // }
      case "Pat.Var" => for {
        name <- getField[Term.Name]("name")
      } yield {
        Pat.Var(name)
      }
      // @ast class Wildcard() extends Pat
      case "Pat.Wildcard" => StateT[MetaError, List[Field[Tree]], Pat](xs => Right(xs -> Pat.Wildcard()))
      // @ast class SeqWildcard() extends Pat {
      //   checkParent(ParentChecks.PatSeqWildcard)
      // }
      case "Pat.SeqWildcard" => StateT[MetaError, List[Field[Tree]], Pat](xs => Right(xs -> Pat.SeqWildcard()))
      // @ast class Bind(lhs: Pat, rhs: Pat) extends Pat {
      //   checkFields(lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
      // }
      case "Pat.Bind" => for { 
        lhs <- getField[Pat]("lhs")
        rhs <- getField[Pat]("rhs")
      } yield { 
        Pat.Bind(lhs, rhs)
      }
      // @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
      case "Pat.Alternative" => for {
        lhs <- getField[Pat]("lhs")
        rhs <- getField[Pat]("rhs")
      } yield {
        Pat.Alternative(lhs, rhs)
      }
      // @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
      //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
      // }
      case "Pat.Tuple" => for {
        args <- getListField[Pat]("args")
      } yield {
        Pat.Tuple(args)
      }
      // @ast class Extract(fun: Term, args: List[Pat]) extends Pat {
      //   checkFields(fun.isExtractor)
      // }
      case "Pat.Extract" => for { 
        fun <- getField[Term]("fun")
        args <- getListField[Pat]("args")
      } yield {
        Pat.Extract(fun, args)
      }
      // @ast class ExtractInfix(lhs: Pat, op: Term.Name, rhs: List[Pat]) extends Pat
      case "Pat.ExtractInfix" => for {
        lhs <- getField[Pat]("lhs")
        op <- getField[Term.Name]("op")
        rhs <- getListField[Pat]("rhs")
      } yield { 
        Pat.ExtractInfix(lhs, op, rhs)
      }
      // @ast class Interpolate(prefix: Term.Name, parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
      //   checkFields(parts.length == args.length + 1)
      // }
      case "Type.Interpolate" => for {
        prefix <- getField[Term.Name]("prefix")
        parts <- getListField[Lit]("parts")
        args <- getListField[Pat]("args")
      } yield {
        Pat.Interpolate(prefix, parts, args)
      }
      // @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
      //   checkFields(parts.length == args.length + 1)
      // }
      case "Pat.Xml" => for {
        parts <- getListField[Lit]("parts")
        args <- getListField[Pat]("args")
      } yield { 
        Pat.Xml(parts, args)
      }
      // @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
      //   checkFields(lhs.is[Pat.Wildcard] || lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
      //   checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
      // }
      case "Pat.Typed" => for { 
        lhs <- getField[Pat]("lhs")
        rhs <- getField[Type]("rhs")
      } yield {
        Pat.Typed(lhs, rhs)
      }
    }
  }

  val declState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Decl]] = {
    case s if s.startsWith("Decl") => s match {
      // @branch trait Decl extends Stat
      // object Decl {
      //   @ast class Val(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: scala.meta.Type) extends Decl
      case "Decl.Val" => for {
        mods <- getListField[Mod]("mods")
        pats <- getListField[Pat]("pats")
        decltpe <- getField[Type]("decltpe")
      } yield {
        Decl.Val(mods, pats, decltpe)
      }
      //   @ast class Var(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: scala.meta.Type) extends Decl
      case "Decl.Var" => for {
        mods <- getListField[Mod]("mods")
        pats <- getListField[Pat]("pats")
        decltpe <- getField[Type]("decltpe")
      } yield {
        Decl.Var(mods, pats, decltpe)
      }

      case "Decl.Def" => for { 
      //   @ast class Def(mods: List[Mod],
      //                  name: Term.Name,
      //                  tparams: List[scala.meta.Type.Param],
      //                  paramss: List[List[Term.Param]],
      //                  decltpe: scala.meta.Type) extends Decl with Member.Term
        mods <- getListField[Mod]("mods")
        name <- getField[Term.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        paramss <- getListListField[Term.Param]("paramss")
        decltpe <- getField[Type]("decltpe")
      } yield {
        Decl.Def(mods, name, tparams, paramss, decltpe)
      }
      //   @ast class Type(mods: List[Mod],
      //                   name: scala.meta.Type.Name,
      //                   tparams: List[scala.meta.Type.Param],
      //                   bounds: scala.meta.Type.Bounds) extends Decl with Member.Type
      // }
      case "Decl.Type" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Type.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        bounds <- getField[Type.Bounds]("bounds")
      } yield {
        Decl.Type(mods, name, tparams, bounds)
      }
    }
  }

  val defnState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Defn]] = {
    case s if s.startsWith("Defn") => s match {
      // @branch trait Defn extends Stat
      // object Defn {
      //   @ast class Val(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: Option[scala.meta.Type],
      //                  rhs: Term) extends Defn {
      //     checkFields(pats.forall(!_.is[Term.Name]))
      //   }
      case "Defn.Val" => for { 
        mods <- getListField[Mod]("mods")
        pats <- getListField[Pat]("pats")
        decltpe <- getOptionField[Type]("decltpe")
        rhs <- getField[Term]("rhs")
      } yield {
        Defn.Val(mods, pats, decltpe, rhs)
      }
      //   @ast class Var(mods: List[Mod],
      //                  pats: List[Pat] @nonEmpty,
      //                  decltpe: Option[scala.meta.Type],
      //                  rhs: Option[Term]) extends Defn {
      //     checkFields(pats.forall(!_.is[Term.Name]))
      //     checkFields(decltpe.nonEmpty || rhs.nonEmpty)
      //     checkFields(rhs.isEmpty ==> pats.forall(_.is[Pat.Var]))
      //   }
      case "Defn.Var" => for {
        mods <- getListField[Mod]("mods")
        pats <- getListField[Pat]("pats")
        decltpe <- getOptionField[Type]("decltpe")
        rhs <- getOptionField[Term]("rhs")
      } yield {
        Defn.Var(mods, pats, decltpe, rhs)
      }
      //   @ast class Def(mods: List[Mod],
      //                  name: Term.Name,
      //                  tparams: List[scala.meta.Type.Param],
      //                  paramss: List[List[Term.Param]],
      //                  decltpe: Option[scala.meta.Type],
      //                  body: Term) extends Defn with Member.Term
      case "Defn.Def" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Term.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        paramss <- getListListField[Term.Param]("paramss")
        decltpe <- getOptionField[Type]("decltpe")
        body <- getField[Term]("body")
      } yield {
        Defn.Def(mods, name, tparams, paramss, decltpe, body)
      }
      //   @ast class Macro(mods: List[Mod],
      //                    name: Term.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    paramss: List[List[Term.Param]],
      //                    decltpe: Option[scala.meta.Type],
      //                    body: Term) extends Defn with Member.Term
      case "Defn.Macro" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Term.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        paramss <- getListListField[Term.Param]("paramss")
        decltpe <- getOptionField[Type]("decltpe")
        body <- getField[Term]("body")
      } yield {
        Defn.Macro(mods, name, tparams, paramss, decltpe, body)
      }
      //   @ast class Type(mods: List[Mod],
      //                   name: scala.meta.Type.Name,
      //                   tparams: List[scala.meta.Type.Param],
      //                   body: scala.meta.Type) extends Defn with Member.Type
      case "Defn.Type" => for { 
        mods <- getListField[Mod]("mods")
        name <- getField[Type.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        body <- getField[Type]("body")
      } yield {
        Defn.Type(mods, name, tparams, body)
      }
      //   @ast class Class(mods: List[Mod],
      //                    name: scala.meta.Type.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    ctor: Ctor.Primary,
      //                    templ: Template) extends Defn with Member.Type
      case "Defn.Class" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Type.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        ctor <- getField[Ctor.Primary]("ctor")
        templ <- getField[Template]("templ")
      } yield {
        Defn.Class(mods, name, tparams, ctor, templ)
      }
      //   @ast class Trait(mods: List[Mod],
      //                    name: scala.meta.Type.Name,
      //                    tparams: List[scala.meta.Type.Param],
      //                    ctor: Ctor.Primary,
      //                    templ: Template) extends Defn with Member.Type {
      //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
      //   }
      case "Defn.Trait" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Type.Name]("name")
        tparams <- getListField[Type.Param]("tparams")
        ctor <- getField[Ctor.Primary]("ctor")
        templ <- getField[Template]("templ")
      } yield {
        Defn.Trait(mods, name, tparams, ctor, templ)
      }
      //   @ast class Object(mods: List[Mod],
      //                     name: Term.Name,
      //                     templ: Template) extends Defn with Member.Term {
      //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
      //   }
      case "Defn.Object" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Term.Name]("name")
        templ <- getField[Template]("templ")
      } yield {
        Defn.Object(mods, name, templ)
      }
    }
  }

  val pkgState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Pkg]] = {
    case "Pkg" => for {
      ref <- getField[Term.Ref]("ref")
      stats <- getListField[Stat]("stats")
    } yield {
      Pkg(ref, stats)
    }
  }

  val ctorState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Ctor]] = {
    case s if s.startsWith("Ctor") => s match {
      // @branch trait m extends Tree with Member
      // object Ctor {
      //   @ast class Primary(mods: List[Mod],
      //                      name: Name,
      //                      paramss: List[List[Term.Param]]) extends Ctor
      case "Ctor.Primary" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Name]("name")
        paramss <- getListListField[Term.Param]("paramss")
      } yield {
        Ctor.Primary(mods, name, paramss)
      }
      //   @ast class Secondary(mods: List[Mod],
      //                        name: Name,
      //                        paramss: List[List[Term.Param]] @nonEmpty,
      //                        init: Init,
      //                        stats: List[Stat]) extends Ctor with Stat {
      //     checkFields(stats.forall(_.isBlockStat))
      //   }
      // }
      case "Ctor.Secondary" => for {
        mods <- getListField[Mod]("mods")
        name <- getField[Name]("name")
        paramss <- getListListField[Term.Param]("paramss")
        init <- getField[Init]("init")
        stats <- getListField[Stat]("stats")
      } yield {
        Ctor.Secondary(mods, name, paramss, init, stats)
      }
    }
  }


  val modState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Mod]] = {
    case s if s.startsWith("Mod") => s match {
    // @branch trait Mod extends Tree
    // object Mod {
    //   @ast class Annot(init: Init) extends Mod {
    //     @deprecated("Use init instead", "1.9.0")
    //     def body = init
    //   }
      case "Mod.Annot" => for {
        init <- getField[Init]("init")
      } yield {
        Mod.Annot(init)
      }
    //   @ast class Private(within: Ref) extends Mod {
    //     checkFields(within.isWithin)
    //   }
      case "Mod.Private" => for {
        within <- getField[Ref]("within")
      } yield {
        Mod.Private(within)
      }
    //   @ast class Protected(within: Ref) extends Mod {
    //     checkFields(within.isWithin)
    //   }
      case "Mod.Protected" => for {
        within <- getField[Ref]("within")
      } yield {
        Mod.Protected(within)
      }
    //   @ast class Implicit() extends Mod
      case "Mod.Implicit" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Implicit())
      }
    //   @ast class Final() extends Mod
      case "Mod.Final" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Final())
      }
    //   @ast class Sealed() extends Mod
      case "Mod.Sealed" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Sealed())
      }
    //   @ast class Override() extends Mod
      case "Mod.Override" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Override())
      }
    //   @ast class Case() extends Mod
      case "Mod.Case" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Case())
      }
    //   @ast class Abstract() extends Mod
      case "Mod.Abstract" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Abstract())
      }
    //   @ast class Covariant() extends Mod
      case "Mod.Covariant" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Covariant())
      }
    //   @ast class Contravariant() extends Mod
      case "Mod.Contravariant" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Contravariant())
      }
    //   @ast class Lazy() extends Mod
      case "Mod.Lazy" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Lazy())
      }
    //   @ast class ValParam() extends Mod
      case "Mod.ValParam" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.ValParam())
      }
    //   @ast class VarParam() extends Mod
      case "Mod.VarParam" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.VarParam())
      }
    //   @ast class Inline() extends Mod
      case "Mod.Inline" => StateT[MetaError, List[Field[Tree]], Mod]{ xs =>
        Right(xs -> Mod.Inline())
      }
    // }

    }
  }

  val enumeratorState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Enumerator]] = {
    case s if s.startsWith("Enumerator") => s match {
    // @branch trait Enumerator extends Tree
    // object Enumerator {
    //   @ast class Generator(pat: Pat, rhs: Term) extends Enumerator
      case "Enumerator.Generator" => for {
        pat <- getField[Pat]("pat")
        rhs <- getField[Term]("rhs")
      } yield {
        Enumerator.Generator(pat, rhs)
      }
    //   @ast class Val(pat: Pat, rhs: Term) extends Enumerator
      case "Enumerator.Val" => for {
        pat <- getField[Pat]("pat")          
        rhs <- getField[Term]("rhs")
      } yield {
        Enumerator.Val(pat, rhs)
      }
    //   @ast class Guard(cond: Term) extends Enumerator
      case "Enumerator.Guard" => for {
        cond <- getField[Term]("cond")
      } yield {
        Enumerator.Guard(cond)
      }
    // }
    }
  }

  val importeeState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Importee]] = {
    case s if s.startsWith("Importee") => s match {
    // @branch trait Importee extends Tree with Ref
    // object Importee {
    //   @ast class Wildcard() extends Importee
      case "Importee.Wildcard" => StateT[MetaError, List[Field[Tree]], Importee] { xs =>
        Right(xs -> Importee.Wildcard())
      }

    //   @ast class Name(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
      case "Importee.Name" => for {
        name <- getField[Name]("name")
      } yield {
        Importee.Name(name)
      }
    //   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
    //   }
      case "Importee.Rename" => for {
        name <- getField[Name]("name")
        rename <- getField[Name]("rename")
      } yield {
        Importee.Rename(name, rename)
      }
    //   @ast class Unimport(name: scala.meta.Name) extends Importee {
    //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
    //   }
    // }
      case "Importee.Unimport" => for {
        name <- getField[Name]("name")
      } yield {
        Importee.Unimport(name)
      }
    }
  }


  val algebra: Algebra[MetaTree, Tree] = {
    case Leaf(t) => t
    case Obj(tpe, fields) => 
      val othersState: PartialFunction[String, StateT[MetaError, List[Field[Tree]], Tree]] = {

        // @ast class Self(name: Name, decltpe: Option[Type]) extends Member
        case "Self" => for {
          name <- getField[Name]("name")
          decltpe <- getOptionField[Type]("decltpe")
        } yield {
          Self(name, decltpe)
        }

        // @ast class Template(early: List[Stat],
        //                     inits: List[Init],
        //                     self: Self,
        //                     stats: List[Stat]) extends Tree {
        //   checkFields(early.forall(_.isEarlyStat && inits.nonEmpty))
        //   checkFields(stats.forall(_.isTemplateStat))
        // }
        case "Template" => for {
          early <- getListField[Stat]("early")
          inits <- getListField[Init]("inits")
          self <- getField[Self]("self")
          stats <- getListField[Stat]("stats")
        } yield {
          Template(early, inits, self, stats)
        }
        // @ast class Init(tpe: Type, name: Name, argss: List[List[Term]]) extends Ref {
        //   checkFields(tpe.isConstructable)
        //   checkParent(ParentChecks.Init)
        // }
        case "Init" => for {
          tpe <- getField[Type]("tpe")
          name <- getField[Name]("name")
          argss <- getListListField[Term]("argss")
        } yield {
          Init(tpe, name, argss)
        }

        // @ast class Import(importers: List[Importer] @nonEmpty) extends Stat
        case "Import" => for {
          importers <- getListField[Importer]("importers")
        } yield {
          Import(importers)
        }
        // @ast class Importer(ref: Term.Ref, importees: List[Importee] @nonEmpty) extends Tree {
        //   checkFields(ref.isStableId)
        // }
        case "Importer" => for {
          ref <- getField[Term.Ref]("ref")
          importees <- getListField[Importee]("importees")
        } yield {
          Importer(ref, importees)
        }

        // @ast class Case(pat: Pat, cond: Option[Term], body: Term) extends Tree
        case "Case" => for {
          pat <- getField[Pat]("pat")
          cond <- getOptionField[Term]("cond")
          body <- getField[Term]("body")
        } yield {
          Case(pat, cond, body)
        }
        // @ast class Source(stats: List[Stat]) extends Tree {
        case "Source" => for {
          stats <- getListField[Stat]("stats")
        } yield {
          Source(stats)
        }
      }

      val st = (
        termParamState orElse
        termState orElse
        typeParamState orElse
        typeState orElse
        typeBoundsState orElse
        patState orElse
        declState orElse
        defnState orElse
        pkgState orElse
        ctorState orElse
        modState orElse
        enumeratorState orElse
        importeeState orElse
        othersState
      )(tpe)

      st.eval(fields) match {
        case Left(err) => throw new RuntimeException(err)
        case Right(x)  => x
      }

  }


}