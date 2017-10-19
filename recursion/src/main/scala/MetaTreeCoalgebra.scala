package scala.meta
package fix

import matryoshka._
import matryoshka.implicits._
import scalaz.StateT
import scalaz.std.either._

import MetaTree._

trait MetaTreeCoalgebra {

  val termParamCoalgebra: Term.Param => MetaTree[Tree] = { 
    case Term.Param(mods, name, decltpe, default) =>
      Obj(
        "Term.Param"
      , ListField("mods", mods) ::  SimpleField("name", name) ::
        OptionField("decltpe", decltpe) :: OptionField("default", default) ::
        Nil
      )
  }

  val termCoalgebra: Term => MetaTree[Tree] = { t: Term =>
    Obj(
      t.productPrefix
    , t match {
        // @branch trait Term extends Stat
        // object Term {
        //   @branch trait Ref extends Term with scala.meta.Ref
        //   @ast class This(qual: scala.meta.Name) extends Term.Ref
        case Term.This(qual) =>
          SimpleField("qual", qual) ::
          Nil

        //   @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Term.Ref
        case Term.Super(thisp, superp) =>
          SimpleField("thisp", thisp) :: SimpleField("superp", superp) ::
          Nil
        //   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
        //   @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
        case Term.Select(qual, name) =>
          SimpleField("qual", qual) ::  SimpleField("name", name) ::
          Nil
        //   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
        //     checkFields(parts.length == args.length + 1)
        //   }
        case Term.Interpolate(prefix, parts, args) =>
          SimpleField("prefix", prefix) :: ListField("parts", parts) :: ListField("args", args) ::  
          Nil
        //   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
        //     checkFields(parts.length == args.length + 1)
        //   }
        case Term.Xml(parts, args) =>
          ListField("parts", parts) :: ListField("args", args) ::  
          Nil
        //   @ast class Apply(fun: Term, args: List[Term]) extends Term
        case Term.Apply(fun, args) =>
          SimpleField("fun", fun) :: ListField("args", args) ::  
          Nil
        //   @ast class ApplyType(fun: Term, targs: List[Type] @nonEmpty) extends Term
        case Term.ApplyType(fun, targs) =>
          SimpleField("fun", fun) :: ListField("targs", targs) ::  
          Nil
        //   @ast class ApplyInfix(lhs: Term, op: Name, targs: List[Type], args: List[Term]) extends Term
        case Term.ApplyInfix(lhs, op, targs, args) =>
          SimpleField("lhs", lhs) :: SimpleField("op", op) :: ListField("targs", targs) :: ListField("args", args) ::  
          Nil
        //   @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
        //     checkFields(op.isUnaryOp)
        //   }
        case Term.ApplyUnary(op, arg) =>
          SimpleField("op", op) :: SimpleField("arg", arg) ::
          Nil
        //   @ast class Assign(lhs: Term, rhs: Term) extends Term {
        //     checkFields(lhs.is[Term.Quasi] || lhs.is[Term.Ref] || lhs.is[Term.Apply])
        //     checkParent(ParentChecks.TermAssign)
        //   }
        case Term.Assign(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) ::
          Nil
        //   @ast class Return(expr: Term) extends Term
        case Term.Return(expr) =>
          SimpleField("expr", expr) ::
          Nil
        //   @ast class Throw(expr: Term) extends Term
        case Term.Throw(expr) =>
          SimpleField("expr", expr) ::
          Nil
        //   @ast class Ascribe(expr: Term, tpe: Type) extends Term
        case Term.Ascribe(expr, tpe) =>
          SimpleField("expr", expr) :: SimpleField("tpe", tpe) ::
          Nil
        //   @ast class Annotate(expr: Term, annots: List[Mod.Annot] @nonEmpty) extends Term
        case Term.Annotate(expr, annots) =>
          SimpleField("expr", expr) :: ListField("annots", annots) ::
          Nil
        //   @ast class Tuple(args: List[Term] @nonEmpty) extends Term {
        //     // tuple must have more than one element
        //     // however, this element may be Quasi with "hidden" list of elements inside
        //     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Term.Quasi]))
        //   }
        case Term.Tuple(args) =>
          ListField("args", args) ::
          Nil
        //   @ast class Block(stats: List[Stat]) extends Term {
        //     checkFields(stats.forall(_.isBlockStat))
        //   }
        case Term.Block(stats) =>
          ListField("stats", stats) ::
          Nil
        //   @ast class If(cond: Term, thenp: Term, elsep: Term) extends Term
        case Term.If(cond, thenp, elsep) =>
          SimpleField("cond", cond) :: SimpleField("thenp", thenp) :: SimpleField("elsep", elsep) ::
          Nil
        //   @ast class Match(expr: Term, cases: List[Case] @nonEmpty) extends Term
        case Term.Match(expr, cases) =>
          SimpleField("expr", expr) :: ListField("cases", cases) ::
          Nil
        //   @ast class Try(expr: Term, catchp: List[Case], finallyp: Option[Term]) extends Term
        case Term.Try(expr, catchp, finallyp) =>
          SimpleField("expr", expr) :: ListField("catchp", catchp) :: OptionField("finallyp", finallyp) ::
          Nil
        //   @ast class TryWithHandler(expr: Term, catchp: Term, finallyp: Option[Term]) extends Term
        case Term.TryWithHandler(expr, catchp, finallyp) =>
          SimpleField("expr", expr) :: SimpleField("catchp", catchp) :: OptionField("finallyp", finallyp) ::
          Nil
        //   @ast class Function(params: List[Term.Param], body: Term) extends Term {
        //     checkFields(params.forall(param => param.is[Term.Param.Quasi] || (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)))
        //     checkFields(params.exists(_.is[Term.Param.Quasi]) || params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1))
        //   }
        case Term.Function(params, body) =>
          ListField("params", params) :: SimpleField("body", body) ::
          Nil
        //   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Term
        case Term.PartialFunction(cases) =>
          ListField("cases", cases) ::
          Nil
        //   @ast class While(expr: Term, body: Term) extends Term
        case Term.While(expr, body) =>
          SimpleField("expr", expr) :: SimpleField("body", body) ::
          Nil
        //   @ast class Do(body: Term, expr: Term) extends Term
        case Term.Do(body, expr) =>
          SimpleField("body", body) :: SimpleField("expr", expr) ::
          Nil
        //   @ast class For(enums: List[Enumerator] @nonEmpty, body: Term) extends Term {
        //     checkFields(enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.Quasi])
        //   }
        case Term.For(enums, body) =>
          ListField("enums", enums) :: SimpleField("body", body) ::
          Nil
        //   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Term) extends Term
        case Term.ForYield(enums, body) =>
          ListField("enums", enums) :: SimpleField("body", body) ::
          Nil
        //   @ast class New(init: Init) extends Term
        case Term.New(init) =>
          SimpleField("init", init) ::
          Nil
        //   @ast class NewAnonymous(templ: Template) extends Term
        case Term.NewAnonymous(templ) =>
          SimpleField("templ", templ) ::
          Nil
        //   @ast class Placeholder() extends Term
        case Term.Placeholder() =>
          Nil
        //   @ast class Eta(expr: Term) extends Term
        case Term.Eta(expr) =>
          SimpleField("expr", expr) ::
          Nil
        //   @ast class Repeated(expr: Term) extends Term {
        //     checkParent(ParentChecks.TermRepeated)
        //   }
        case Term.Repeated(expr) =>
          SimpleField("expr", expr) ::
          Nil

        //   def fresh(): Term.Name = fresh("fresh")
        //   def fresh(prefix: String): Term.Name = Term.Name(prefix + Fresh.nextId())
        // }
      }
    )
  }

  val typeParamCoalgebra: Type.Param => MetaTree[Tree] = {
    case Type.Param(mods, name, tparams, tbounds, vbounds, cbounds) =>
      Obj(
        "Type.Param"
      , ListField("mods", mods) ::  SimpleField("name", name) :: ListField("tparams", tparams) ::
        SimpleField("tbounds", tbounds) :: ListField("vbounds", vbounds) :: ListField("cbounds", cbounds) :: 
        Nil
      )
  }

  val typeCoalgebra: Type => MetaTree[Tree] = { t: Type =>
    Obj(
      t.productPrefix
    , t match {
        // @branch trait Ref extends Type with scala.meta.Ref
        // @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
        // @ast class Select(qual: Term.Ref, name: Type.Name) extends Type.Ref {
        //   checkFields(qual.isPath || qual.is[Term.Super] || qual.is[Term.Ref.Quasi])
        // }
        case Type.Select(qual, name) =>
          SimpleField("qual", qual) :: SimpleField("name", name) :: 
          Nil
        // @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
        case Type.Project(qual, name) =>
          SimpleField("qual", qual) :: SimpleField("name", name) :: 
          Nil
        // @ast class Singleton(ref: Term.Ref) extends Type.Ref {
        //   checkFields(ref.isPath || ref.is[Term.Super])
        // }
        case Type.Singleton(ref) =>
          SimpleField("ref", ref) :: 
          Nil
        // @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
        case Type.Apply(tpe, args) =>
          SimpleField("tpe", tpe) :: ListField("args", args) :: 
          Nil
        // @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
        case Type.ApplyInfix(lhs, op, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("op", op) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class Function(params: List[Type], res: Type) extends Type
        case Type.Function(params, res) =>
          ListField("params", params) :: SimpleField("res", res) :: 
          Nil
        // @ast class ImplicitFunction(params: List[Type], res: Type) extends Type
        case Type.ImplicitFunction(params, res) =>
          ListField("params", params) :: SimpleField("res", res) :: 
          Nil
        // @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
        //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
        // }
        case Type.Tuple(args) =>
          ListField("args", args) :: 
          Nil
        // @ast class With(lhs: Type, rhs: Type) extends Type
        case Type.With(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class And(lhs: Type, rhs: Type) extends Type
        case Type.And(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class Or(lhs: Type, rhs: Type) extends Type
        case Type.Or(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
        //   checkFields(stats.forall(_.isRefineStat))
        // }
        case Type.Refine(tpe, stats) =>
          OptionField("tpe", tpe) :: ListField("stats", stats) :: 
          Nil
        // @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
        //   checkFields(stats.forall(_.isExistentialStat))
        // }
        case Type.Existential(tpe, stats) =>
          SimpleField("tpe", tpe) :: ListField("stats", stats) :: 
          Nil
        // @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
        case Type.Existential(tpe, stats) =>
          SimpleField("tpe", tpe) :: ListField("stats", stats) :: 
          Nil
        // @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeLambda)
        // }
        case Type.Lambda(tparams, tpe) =>
          ListField("tparams", tparams) :: SimpleField("tpe", tpe) :: 
          Nil
        // @ast class Method(paramss: List[List[Term.Param]], tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeMethod)
        // }
        case Type.Method(paramss, tpe) =>
          ListListField("paramss", paramss) :: SimpleField("tpe", tpe) :: 
          Nil
        // @ast class Placeholder(bounds: Bounds) extends Type
        case Type.Placeholder(bounds) =>
          SimpleField("bounds", bounds) :: 
          Nil

        // @ast class ByName(tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeByName)
        // }
        case Type.ByName(tpe) =>
          SimpleField("tpe", tpe) :: 
          Nil
        // @ast class Repeated(tpe: Type) extends Type {
        //   checkParent(ParentChecks.TypeRepeated)
        // }
        case Type.Repeated(tpe) =>
          SimpleField("tpe", tpe) :: 
          Nil
        // @ast class Var(name: Name) extends Type with Member.Type {
        //   checkFields(name.value(0).isLower)
        //   checkParent(ParentChecks.TypeVar)
        // }
        case Type.Var(name) =>
          SimpleField("name", name) :: 
          Nil
      }
    )
  }

  val typeBoundsCoalgebra: Type.Bounds => MetaTree[Tree] = { t: Type.Bounds =>
    Obj(
      t.productPrefix
    , OptionField("lo", t.lo) ::  OptionField("hi", t.hi) :: 
      Nil
    )
  }

  val patCoalgebra: Pat => MetaTree[Tree] = { t: Pat =>
    Obj(
      t.productPrefix
    , t match {
        // @ast class Var(name: scala.meta.Term.Name) extends Pat with Member.Term {
        //   // NOTE: can't do this check here because of things like `val X = 2`
        //   // checkFields(name.value(0).isLower)
        //   checkParent(ParentChecks.PatVar)
        // }
        case Pat.Var(name) =>
          SimpleField("name", name) :: 
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
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
        case Pat.Alternative(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
        // @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
        //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
        // }
        case Pat.Tuple(args) =>
          ListField("args", args) :: 
          Nil
        // @ast class Extract(fun: Term, args: List[Pat]) extends Pat {
        //   checkFields(fun.isExtractor)
        // }
        case Pat.Extract(fun, args) =>
          SimpleField("fun", fun) :: ListField("args", args) :: 
          Nil
        // @ast class ExtractInfix(lhs: Pat, op: Term.Name, rhs: List[Pat]) extends Pat
        case Pat.ExtractInfix(lhs, op, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("op", op) :: ListField("rhs", rhs) :: 
          Nil
        // @ast class Interpolate(prefix: Term.Name, parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
        //   checkFields(parts.length == args.length + 1)
        // }
        case Pat.Interpolate(prefix, parts, args) =>
          SimpleField("prefix", prefix) :: ListField("parts", parts) :: ListField("args", args) :: 
          Nil
        // @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
        //   checkFields(parts.length == args.length + 1)
        // }
        case Pat.Xml(parts, args) =>
          ListField("parts", parts) :: ListField("args", args) :: 
          Nil
        // @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
        //   checkFields(lhs.is[Pat.Wildcard] || lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
        //   checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
        // }
        case Pat.Typed(lhs, rhs) =>
          SimpleField("lhs", lhs) :: SimpleField("rhs", rhs) :: 
          Nil
      }
    )
  }

  val declCoalgebra: Decl => MetaTree[Tree] = { t: Decl =>
    Obj(
      t.productPrefix
    , t match {
        // @branch trait Decl extends Stat
        // object Decl {
        //   @ast class Val(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: scala.meta.Type) extends Decl
        case Decl.Val(mods, pats, decltpe) =>
          ListField("mods", mods) :: ListField("pats", pats) :: SimpleField("decltpe", decltpe) :: 
          Nil
        //   @ast class Var(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: scala.meta.Type) extends Decl
        case Decl.Var(mods, pats, decltpe) =>
          ListField("mods", mods) :: ListField("pats", pats) :: SimpleField("decltpe", decltpe) :: 
          Nil
        //   @ast class Def(mods: List[Mod],
        //                  name: Term.Name,
        //                  tparams: List[scala.meta.Type.Param],
        //                  paramss: List[List[Term.Param]],
        //                  decltpe: scala.meta.Type) extends Decl with Member.Term
        case Decl.Def(mods, name, tparams, paramss, decltpe) =>
          ListField("mods", mods) :: SimpleField("name", name) ::
          ListField("tparams", tparams) :: ListListField("paramss", paramss) :: SimpleField("decltpe", decltpe) :: 
          Nil
        //   @ast class Type(mods: List[Mod],
        //                   name: scala.meta.Type.Name,
        //                   tparams: List[scala.meta.Type.Param],
        //                   bounds: scala.meta.Type.Bounds) extends Decl with Member.Type
        // }
        case Decl.Type(mods, name, tparams, bounds) =>
          ListField("mods", mods) :: SimpleField("name", name) ::
          ListField("tparams", tparams) :: SimpleField("bounds", bounds) :: 
          Nil
      }
    )
  }

  val defnCoalgebra: Defn => MetaTree[Tree] = { t: Defn =>
    Obj(
      t.productPrefix
    , t match {
        // @branch trait Defn extends Stat
        // object Defn {
        //   @ast class Val(mods: List[Mod],
        //                  pats: List[Pat] @nonEmpty,
        //                  decltpe: Option[scala.meta.Type],
        //                  rhs: Term) extends Defn {
        //     checkFields(pats.forall(!_.is[Term.Name]))
        //   }
        case Defn.Val(mods, pats, decltpe, rhs) =>
          ListField("mods", mods) :: ListField("pats", pats) :: 
          OptionField("decltpe", decltpe) :: SimpleField("rhs", rhs) ::
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
          ListField("mods", mods) :: ListField("pats", pats) :: 
          OptionField("decltpe", decltpe) :: OptionField("rhs", rhs) ::
          Nil
        //   @ast class Def(mods: List[Mod],
        //                  name: Term.Name,
        //                  tparams: List[scala.meta.Type.Param],
        //                  paramss: List[List[Term.Param]],
        //                  decltpe: Option[scala.meta.Type],
        //                  body: Term) extends Defn with Member.Term
        case Defn.Def(mods, name, tparams, paramss, decltpe, body) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          ListField("tparams", tparams) :: ListListField("paramss", paramss) :: 
          OptionField("decltpe", decltpe) :: SimpleField("body", body) ::
          Nil
        //   @ast class Macro(mods: List[Mod],
        //                    name: Term.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    paramss: List[List[Term.Param]],
        //                    decltpe: Option[scala.meta.Type],
        //                    body: Term) extends Defn with Member.Term
        case Defn.Macro(mods, name, tparams, paramss, decltpe, body) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          ListField("tparams", tparams) :: ListListField("paramss", paramss) :: 
          OptionField("decltpe", decltpe) :: SimpleField("body", body) ::
          Nil
        //   @ast class Type(mods: List[Mod],
        //                   name: scala.meta.Type.Name,
        //                   tparams: List[scala.meta.Type.Param],
        //                   body: scala.meta.Type) extends Defn with Member.Type
        case Defn.Type(mods, name, tparams, body) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          ListField("tparams", tparams) :: SimpleField("body", body) ::
          Nil
        //   @ast class Class(mods: List[Mod],
        //                    name: scala.meta.Type.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    ctor: Ctor.Primary,
        //                    templ: Template) extends Defn with Member.Type
        case Defn.Class(mods, name, tparams, ctor, templ) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          ListField("tparams", tparams) :: SimpleField("ctor", ctor) :: SimpleField("templ", templ) ::
          Nil
        //   @ast class Trait(mods: List[Mod],
        //                    name: scala.meta.Type.Name,
        //                    tparams: List[scala.meta.Type.Param],
        //                    ctor: Ctor.Primary,
        //                    templ: Template) extends Defn with Member.Type {
        //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
        //   }
        case Defn.Trait(mods, name, tparams, ctor, templ) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          ListField("tparams", tparams) :: SimpleField("ctor", ctor) :: SimpleField("templ", templ) ::
          Nil
        //   @ast class Object(mods: List[Mod],
        //                     name: Term.Name,
        //                     templ: Template) extends Defn with Member.Term {
        //     checkFields(templ.is[Template.Quasi] || templ.stats.forall(!_.is[Ctor]))
        //   }
        case Defn.Object(mods, name, templ) =>
          ListField("mods", mods) :: SimpleField("name", name) :: 
          SimpleField("templ", templ) ::
          Nil
      }
    )
  }  

  val pkgCoalgebra: Pkg => MetaTree[Tree] = { t: Pkg =>
    Obj(
      t.productPrefix
    , SimpleField("ref", t.ref) :: ListField("stats", t.stats) :: Nil
    )
  }

  val ctorCoalgebra: Ctor => MetaTree[Tree] = { t: Ctor =>
    Obj(
      t.productPrefix
      , t match {
          // @branch trait m extends Tree with Member
          // object Ctor {
          //   @ast class Primary(mods: List[Mod],
          //                      name: Name,
          //                      paramss: List[List[Term.Param]]) extends Ctor
          case Ctor.Primary(mods, name, paramss) =>
            ListField("mods", mods) :: SimpleField("name", name) :: ListListField("paramss", paramss) :: Nil
          //   @ast class Secondary(mods: List[Mod],
          //                        name: Name,
          //                        paramss: List[List[Term.Param]] @nonEmpty,
          //                        init: Init,
          //                        stats: List[Stat]) extends Ctor with Stat {
          //     checkFields(stats.forall(_.isBlockStat))
          //   }
          case Ctor.Secondary(mods, name, paramss, init, stats) =>
            ListField("mods", mods) :: SimpleField("name", name) :: ListListField("paramss", paramss) :: 
            SimpleField("init", init) :: ListField("stats", stats) :: 
            Nil
        }
    )
  }

  val modCoalgebra: Mod => MetaTree[Tree] = { t: Mod =>
    Obj(
      t.productPrefix
      , t match {
          // @branch trait Mod extends Tree
          // object Mod {
          //   @ast class Annot(init: Init) extends Mod {
          //     @deprecated("Use init instead", "1.9.0")
          //     def body = init
          //   }
          case Mod.Annot(init) =>
            SimpleField("init", init) :: Nil

          //   @ast class Private(within: Ref) extends Mod {
          //     checkFields(within.isWithin)
          //   }
          case Mod.Private(within) =>
            SimpleField("within", within) :: Nil

          //   @ast class Protected(within: Ref) extends Mod {
          //     checkFields(within.isWithin)
          //   }
          case Mod.Protected(within) =>
            SimpleField("within", within) :: Nil

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
    )
  }

  val enumCoalgebra: Enumerator => MetaTree[Tree] = { t: Enumerator =>
    Obj(
      t.productPrefix
      , t match {
          // @branch trait Enumerator extends Tree
          // object Enumerator {
          //   @ast class Generator(pat: Pat, rhs: Term) extends Enumerator
          case Enumerator.Generator(pat, rhs) =>
            SimpleField("pat", pat) :: SimpleField("rhs", rhs) :: Nil
          //   @ast class Val(pat: Pat, rhs: Term) extends Enumerator
          case Enumerator.Val(pat, rhs) =>
            SimpleField("pat", pat) :: SimpleField("rhs", rhs) :: Nil
          //   @ast class Guard(cond: Term) extends Enumerator
          case Enumerator.Guard(cond) =>
            SimpleField("cond", cond) :: Nil
          // }
        }
    )
  }

  val importeeCoalgebra: Importee => MetaTree[Tree] = { t: Importee =>
    Obj(
      t.productPrefix
      , t match {
          // @branch trait Importee extends Tree with Ref
          // object Importee {
          //   @ast class Wildcard() extends Importee
            case Importee.Wildcard() =>
              Nil
          //   @ast class Name(name: scala.meta.Name) extends Importee {
          //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
          //   }
            case Importee.Name(name) =>
              SimpleField("name", name) :: Nil
          //   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
          //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
          //     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
          //   }
            case Importee.Rename(name, rename) =>
              SimpleField("name", name) :: SimpleField("rename", rename) :: Nil
          //   @ast class Unimport(name: scala.meta.Name) extends Importee {
          //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
          //   }
            case Importee.Unimport(name) =>
              SimpleField("name", name) :: Nil
          // }
        }
    )
  }

  val coalgebra: Coalgebra[MetaTree, Tree] = {
    case t: Term.Name => Leaf(t)
    case t: Name => Leaf(t)

    case l: Lit  => Leaf(l)  

    case t: Term => termCoalgebra(t)

    case t: Term.Param => termParamCoalgebra(t)

    case t: Type.Param => typeParamCoalgebra(t)

    case t: Type.Bounds => typeBoundsCoalgebra(t)

    case t: Type => typeCoalgebra(t)

    case t: Pat => patCoalgebra(t)

    case t: Decl => declCoalgebra(t)

    case t: Defn => defnCoalgebra(t)

    case t: Pkg => pkgCoalgebra(t)

    case t: Ctor => ctorCoalgebra(t)

    case t: Mod => modCoalgebra(t)

    case t: Enumerator => enumCoalgebra(t)

    case t: Importee => importeeCoalgebra(t)

    // @ast class Self(name: Name, decltpe: Option[Type]) extends Member
    case t@Self(name, decltpe) =>
      Obj(
        t.productPrefix
      , SimpleField("name", name) :: OptionField("decltpe", decltpe) :: Nil
      )

    // @ast class Template(early: List[Stat],
    //                     inits: List[Init],
    //                     self: Self,
    //                     stats: List[Stat]) extends Tree {
    //   checkFields(early.forall(_.isEarlyStat && inits.nonEmpty))
    //   checkFields(stats.forall(_.isTemplateStat))
    // }
    case t@Template(early, inits, self, stats) =>
      Obj(
        t.productPrefix
      , ListField("early", early) :: ListField("inits", inits) :: SimpleField("self", self) ::
        ListField("stats", stats) :: Nil
      )

    // @ast class Init(tpe: Type, name: Name, argss: List[List[Term]]) extends Ref {
    //   checkFields(tpe.isConstructable)
    //   checkParent(ParentChecks.Init)
    // }
    case t@Init(tpe, name, argss) =>
      Obj(
        t.productPrefix
      , SimpleField("tpe", tpe) :: SimpleField("name", name) :: ListListField("argss", argss) :: Nil
      )

    // @ast class Import(importers: List[Importer] @nonEmpty) extends Stat
    case t@Import(importers) =>
      Obj(
        t.productPrefix
      , ListField("importers", importers) :: Nil
      ) 

    // @ast class Importer(ref: Term.Ref, importees: List[Importee] @nonEmpty) extends Tree {
    //   checkFields(ref.isStableId)
    // }
    case t@Importer(ref, importees) =>
      Obj(
        t.productPrefix
      , SimpleField("ref", ref) :: ListField("importees", importees) :: Nil
      )

    // @ast class Case(pat: Pat, cond: Option[Term], body: Term) extends Tree
    case t@Case(pat, cond, body) =>
      Obj(
        t.productPrefix
      , SimpleField("pat", pat) :: OptionField("cond", cond) :: SimpleField("body", body) :: Nil
      )

    // @ast class Source(stats: List[Stat]) extends Tree {
    case t@Source(stats) =>
      Obj(
        t.productPrefix
      , ListField("stats", stats) :: Nil
      )

  }
}