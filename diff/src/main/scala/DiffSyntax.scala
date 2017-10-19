package scala.meta
package diff

import scala.meta.classifiers._
import scala.meta.internal.prettyprinters._
import scala.meta.prettyprinters.Show
import Show.{ sequence => s, repeat => r, indent => i, newline => n, meta => m, wrap => w, function => fn }
import scala.meta.internal.trees.{root => _, branch => _, _}
import scala.meta.internal.tokenizers.Chars._
import scala.meta.internal.tokenizers.keywords
import org.scalameta.adt._
import org.scalameta.invariants._
import org.scalameta.unreachable
import scala.compat.Platform.EOL


object DiffSyntax {
  def apply[T <: Diff](dialect: Dialect): scala.meta.prettyprinters.Syntax[T] = {
    object syntaxInstances {
      // NOTE: these groups closely follow non-terminals in the grammar spec from SLS, except for:
      // 1) we don't care about tracking non-terminals (with m() and/or p()) when that doesn't affect parenthesization
      // 2) `InfixType ::= CompoundType {id [nl] CompoundType}` is incorrect. Should be `CompoundType | InfixType {id [nl] InfixType}`
      // 3) `Pattern2 ::= varid ['@' Pattern3]` has become `Pattern2 ::= varid ['@' AnyPattern3]` due to implementational reasons
      // 4) `Type ::= ... | InfixType [ExistentialClause]` has become `Type ::= ... | AnyInfixType [ExistentialClause]` due to implementational reasons
      // 5) `FunctionArgTypes ::= InfixType | ...` has become `Type ::= AnyInfixType | ...` due to implementational reasons
      @root trait SyntacticGroup {
        def categories: List[String]
        def precedence: Double
      }
      object SyntacticGroup {
        @branch trait Type extends SyntacticGroup { def categories = List("Type") }
        object Type {
          @leaf object ParamTyp extends Type { def precedence = 0 }
          @leaf object Typ extends Type { def precedence = 1 }
          @leaf object AnyInfixTyp extends Type { def precedence = 1.5 }
          @leaf class InfixTyp(op: String) extends Type { def precedence = 2 }
          @leaf object RefineTyp extends Type { def precedence = 3 }
          @leaf object WithTyp extends Type { def precedence = 3.5 }
          @leaf object AnnotTyp extends Type { def precedence = 4 }
          @leaf object SimpleTyp extends Type { def precedence = 6 }
        }
        @branch trait Term extends SyntacticGroup { def categories = List("Term") }
        object Term {
          @leaf object Expr extends Term { def precedence = 0 }
          @leaf object Expr1 extends Term { def precedence = 1 }
          @leaf object PostfixExpr extends Term { def precedence = 2 }
          @leaf class InfixExpr(op: String) extends Term { def precedence = 3 }
          @leaf object PrefixExpr extends Term { def precedence = 4 }
          @leaf object SimpleExpr extends Term { def precedence = 5 }
          @leaf object SimpleExpr1 extends Term { def precedence = 6 }
        }
        @branch trait Pat extends SyntacticGroup { def categories = List("Pat") }
        object Pat {
          @leaf object Pattern extends Pat { def precedence = 0 }
          @leaf object Pattern1 extends Pat { def precedence = 1 }
          @leaf object Pattern2 extends Pat { def precedence = 2 }
          @leaf object AnyPattern3 extends Pat { def precedence = 2.5 }
          @leaf class Pattern3(op: String) extends Pat { def precedence = 3 }
          @leaf object SimplePattern extends Pat { def precedence = 6 }
        }
        @leaf object Literal extends Term with Pat { override def categories = List("Term", "Pat"); def precedence = 6 }
        require(Literal.precedence == Term.SimpleExpr1.precedence && Literal.precedence == Pat.SimplePattern.precedence)
        @leaf object Path extends Type with Term with Pat { override def categories = List("Type", "Term", "Pat"); def precedence = 6 }
        require(Path.precedence == Type.SimpleTyp.precedence && Path.precedence == Term.SimpleExpr1.precedence && Path.precedence == Pat.SimplePattern.precedence)
      }
      import SyntacticGroup.Type._, SyntacticGroup.Term._, SyntacticGroup.Pat._, SyntacticGroup.Literal, SyntacticGroup.Path

      def p(og: SyntacticGroup, t: Tree, left: Boolean = false, right: Boolean = false) = {
        def opNeedsParens(oo: String, io: String, customAssoc: Boolean, customPrecedence: Boolean): Boolean = {
          implicit class XtensionMySyntacticInfo(name: String) {
            def isleftassoc: Boolean = if (customAssoc) name.last != ':' else true
            def isrightassoc: Boolean = !isleftassoc
            def precedence: Int = if (customPrecedence) Term.Name(name).precedence else 0
          }
          require(left != right)
          val (ol, il) = (oo.isleftassoc, io.isleftassoc)
          if (ol ^ il) true
          else {
            val (l, r) = (ol, !ol)
            val (op, ip) = (oo.precedence, io.precedence)
            if (op < ip) r
            else if (op > ip) l
            else l ^ left
          }
        }
        def groupNeedsParens(og: SyntacticGroup, ig: SyntacticGroup): Boolean = {
          val result = {
            require(og.categories.intersect(ig.categories).nonEmpty)
            (og, ig) match {
              case (InfixExpr(oo), InfixExpr(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = true)
              case (InfixTyp(oo), InfixTyp(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = false)
              case (Pattern3(oo), Pattern3(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = true)
              case _ => og.precedence > ig.precedence
            }
          }
          // println((og, ig, left, right) + " => " + result)
          result
        }
        s(t) match {
          case Show.Meta(ig: SyntacticGroup, res) if groupNeedsParens(og, ig) => s("(", res, ")")
          case res => res
        }
      }

      def p2(og: SyntacticGroup, res: Show.Result, left: Boolean = false, right: Boolean = false) = {
        def opNeedsParens(oo: String, io: String, customAssoc: Boolean, customPrecedence: Boolean): Boolean = {
          implicit class XtensionMySyntacticInfo(name: String) {
            def isleftassoc: Boolean = if (customAssoc) name.last != ':' else true
            def isrightassoc: Boolean = !isleftassoc
            def precedence: Int = if (customPrecedence) Term.Name(name).precedence else 0
          }
          require(left != right)
          val (ol, il) = (oo.isleftassoc, io.isleftassoc)
          if (ol ^ il) true
          else {
            val (l, r) = (ol, !ol)
            val (op, ip) = (oo.precedence, io.precedence)
            if (op < ip) r
            else if (op > ip) l
            else l ^ left
          }
        }
        def groupNeedsParens(og: SyntacticGroup, ig: SyntacticGroup): Boolean = {
          val result = {
            require(og.categories.intersect(ig.categories).nonEmpty)
            (og, ig) match {
              case (InfixExpr(oo), InfixExpr(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = true)
              case (InfixTyp(oo), InfixTyp(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = false)
              case (Pattern3(oo), Pattern3(io)) => opNeedsParens(oo, io, customAssoc = true, customPrecedence = true)
              case _ => og.precedence > ig.precedence
            }
          }
          // println((og, ig, left, right) + " => " + result)
          result
        }
        res match {
          case Show.Meta(ig: SyntacticGroup, res) if groupNeedsParens(og, ig) => s("(", res, ")")
          case res => res
        }
      }


      def kw(keyword: String) = fn(sb => {
        val prelast = if (sb.length > 1) sb.charAt(sb.length - 2) else ' '
        val last = if (sb.length > 0) sb.charAt(sb.length - 1) else ' '
        val next = if (keyword.length > 0) keyword(0) else ' '
        val danger = {
          val opThenOp = isOperatorPart(last) && isOperatorPart(next)
          val underscoreThenOp = isIdentifierPart(prelast) && last == '_' && isOperatorPart(next)
          opThenOp || underscoreThenOp
        }
        if (danger) s(" " +keyword) else s(keyword)
      })

      def templ(templ: Template) =
        // TODO: consider XXX.isEmpty
        if (templ.early.isEmpty && templ.inits.isEmpty && templ.self.name.is[Name.Anonymous] && templ.self.decltpe.isEmpty && templ.stats.isEmpty) s()
        else if (templ.inits.nonEmpty || templ.early.nonEmpty) s(" extends ", templ)
        else s(" ", templ)

      def guessIsBackquoted(t: Name): Boolean = {
        def cantBeWrittenWithoutBackquotes(t: Name): Boolean = {
          // TODO: this requires a more thorough implementation
          // TODO: the `this` check is actually here to correctly prettyprint primary ctor calls in secondary ctors
          // this is purely an implementation artifact and will be fixed once we have tokens
          t.value != "this" && (keywords.contains(t.value) || t.value.contains(" "))
        }
        def isAmbiguousWithPatVarTerm(t: Term.Name, p: Tree): Boolean = {
          // TODO: the `eq` trick is very unreliable, but I can't come up with anything better at the moment
          // since the whole guessXXX business is going to be obsoleted by tokens very soon, I'm leaving this as is
          val looksLikePatVar = t.value.head.isLower && t.value.head.isLetter
          val thisLocationAlsoAcceptsPatVars = p match {
            case p: Term.Name => unreachable
            case p: Term.Select => false
            case p: Pat.Wildcard => unreachable
            case p: Pat.Var => false
            case p: Pat.Bind => unreachable
            case p: Pat.Alternative => true
            case p: Pat.Tuple => true
            case p: Pat.Extract => p.args.exists(_ eq t)
            case p: Pat.ExtractInfix => (p.lhs eq t) || p.rhs.exists(_ eq t)
            case p: Pat.Interpolate => p.args.exists(_ eq t)
            case p: Pat.Typed => unreachable
            case p: Pat => unreachable
            case p: Case => p.pat eq t
            case p: Defn.Val => p.pats.exists(_ eq t)
            case p: Defn.Var => p.pats.exists(_ eq t)
            case p: Enumerator.Generator => p.pat eq t
            case p: Enumerator.Val => p.pat eq t
            case _ => false
          }
          looksLikePatVar && thisLocationAlsoAcceptsPatVars
        }
        def isAmbiguousWithPatVarType(t: Type.Name, p: Tree): Boolean = {
          // TODO: figure this out with Martin
          // `x match { case _: t => }` produces a Type.Name
          // `x match { case _: List[t] => }` produces a Type.Var
          // `x match { case _: List[`t`] => }` produces a Type.Var as well
          // the rules look really inconsistent and probably that's just an oversight
          false
        }
        (t, t.parent) match {
          case (t: Term.Name, Some(p: Tree)) => isAmbiguousWithPatVarTerm(t, p) || cantBeWrittenWithoutBackquotes(t)
          case (t: Type.Name, Some(p: Tree)) => isAmbiguousWithPatVarType(t, p) || cantBeWrittenWithoutBackquotes(t)
          case _ => cantBeWrittenWithoutBackquotes(t)
        }
      }
      def guessIsPostfix(t: Term.Select): Boolean = false
      def guessHasExpr(t: Term.Return): Boolean = t.expr match { case Lit.Unit() => false; case _ => true }
      def guessHasElsep(t: Term.If): Boolean = t.elsep match { case Lit.Unit() => false; case e => true }
      def guessHasStats(t: Template): Boolean = t.stats.nonEmpty
      def guessHasBraces(t: Pkg): Boolean = {
        def isOnlyChildOfOnlyChild(t: Pkg): Boolean = t.parent match {
          case Some(pkg: Pkg) => isOnlyChildOfOnlyChild(pkg) && pkg.stats.length == 1
          case Some(source: Source) => source.stats.length == 1
          case None => true
          case _ => unreachable
        }
        !isOnlyChildOfOnlyChild(t)
      }

      // Branches
      // TODO: this match is not exhaustive: if I remove Mod.Package, then I get no warning
      implicit def syntaxTree[T <: Tree]: scala.meta.prettyprinters.Syntax[T] = scala.meta.prettyprinters.Syntax {
        // Bottom
        case t: Quasi =>
          if (!dialect.allowUnquotes) throw new UnsupportedOperationException(s"$dialect doesn't support unquoting")
          if (t.rank > 0) {
            s("." * (t.rank + 1), w("{", t.tree, "}", !t.tree.is[Quasi]))
          } else {
            val allowBraceless = t.tree.is[Term.Name] || t.tree.is[Pat.Var] || t.tree.is[Term.This] || t.tree.is[Pat.Wildcard]
            implicit val syntaxDialect = dialect.copy(allowTermUnquotes = false, allowPatUnquotes = false, allowMultilinePrograms = true)
            s("$", w("{", t.tree.syntax, "}", !allowBraceless))
          }

        // Name
        case t: Name.Anonymous       => s("_")
        case t: Name.Indeterminate   => if (guessIsBackquoted(t)) s("`", t.value, "`") else s(t.value)

        // Term
        case t: Term.This            =>
          val qual = if (t.qual.is[Name.Anonymous]) s() else s(t.qual, ".")
          m(Path, qual, kw("this"))
        case t: Term.Super           =>
          val thisqual = if (t.thisp.is[Name.Anonymous]) s() else s(t.thisp, ".")
          val superqual = if (t.superp.is[Name.Anonymous]) s() else s("[", t.superp, "]")
          m(Path, s(thisqual, kw("super"), superqual))
        case t: Term.Name            => m(Path, if (guessIsBackquoted(t)) s("`", t.value, "`") else s(t.value))
        case t: Term.Select          => m(Path, s(p(SimpleExpr, t.qual), if (guessIsPostfix(t)) " " else ".", t.name))
        case t: Term.Interpolate     =>
          val parts = t.parts.map{ case Lit(part: String) => part }
          val zipped = parts.zip(t.args).map {
            case (part, id: Name) if !guessIsBackquoted(id) => s(part, "$", id.value)
            case (part, arg) => s(part, "${", p(Expr, arg), "}")
          }
          val quote = if (parts.exists(s => s.contains("\n") || s.contains("\""))) "\"\"\"" else "\""
          m(SimpleExpr1, s(t.prefix, quote, r(zipped), parts.last, quote))
        case t: Term.Xml             =>
          if (!dialect.allowXmlLiterals) throw new UnsupportedOperationException(s"$dialect doesn't support xml literals")
          val parts = t.parts.map{ case Lit(part: String) => part }
          val zipped = parts.zip(t.args).map{ case (part, arg) => s(part, "{", p(Expr, arg), "}") }
          m(SimpleExpr1, s(r(zipped), parts.last))
        case t: Term.Apply           => m(SimpleExpr1, s(p(SimpleExpr1, t.fun), t.args))
        case t: Term.ApplyType       => m(SimpleExpr1, s(p(SimpleExpr, t.fun), t.targs))
        case t: Term.ApplyInfix      =>
          val args = t.args match {
            case (Lit.Unit()) :: Nil =>
              s("(())")
            case (arg: Term) :: Nil =>
              s(p(InfixExpr(t.op.value), arg, right = true))
            case args => s(args)
          }

          m(InfixExpr(t.op.value), s(p(InfixExpr(t.op.value), t.lhs, left = true), " ", t.op, t.targs, " ", args))
        case t: Term.ApplyUnary      => m(PrefixExpr, s(t.op, p(SimpleExpr, t.arg)))
        case t: Term.Assign          => m(Expr1, s(p(SimpleExpr1, t.lhs), " ", kw("="), " ", p(Expr, t.rhs)))
        case t: Term.Return          => m(Expr1, s(kw("return"), if (guessHasExpr(t)) s(" ", p(Expr, t.expr)) else s()))
        case t: Term.Throw           => m(Expr1, s(kw("throw"), " ", p(Expr, t.expr)))
        case t: Term.Ascribe         => m(Expr1, s(p(PostfixExpr, t.expr), kw(":"), " ", t.tpe))
        case t: Term.Annotate        => m(Expr1, s(p(PostfixExpr, t.expr), kw(":"), " ", t.annots))
        case t: Term.Tuple           => m(SimpleExpr1, s("(", r(t.args, ", "), ")"))
        case t: Term.Block           =>
          import Term.{Block, Function}
          def pstats(s: List[Stat]) = r(s.map(i(_)), "")
          t match {
            case Block(Function(Term.Param(mods, name: Term.Name, tptopt, _) :: Nil, Block(stats)) :: Nil) if mods.exists(_.is[Mod.Implicit]) =>
              m(SimpleExpr, s("{ ", kw("implicit"), " ", name, tptopt.map(s(kw(":"), " ", _)).getOrElse(s()), " ", kw("=>"), " ", pstats(stats), n("}")))
            case Block(Function(Term.Param(mods, name: Term.Name, None, _) :: Nil, Block(stats)) :: Nil) =>
              m(SimpleExpr, s("{ ", name, " ", kw("=>"), " ", pstats(stats), n("}")))
            case Block(Function(Term.Param(_, _: Name.Anonymous, _, _) :: Nil, Block(stats)) :: Nil) =>
              m(SimpleExpr, s("{ ", kw("_"), " ", kw("=>"), " ", pstats(stats), n("}")))
            case Block(Function(params, Block(stats)) :: Nil) =>
              m(SimpleExpr, s("{ (", r(params, ", "), ") => ", pstats(stats), n("}")))
            case _ =>
              m(SimpleExpr, if (t.stats.isEmpty) s("{}") else s("{", pstats(t.stats), n("}")))
          }
        case t: Term.If              => m(Expr1, s(kw("if"), " (", t.cond, ") ", p(Expr, t.thenp), if (guessHasElsep(t)) s(" ", kw("else"), " ", p(Expr, t.elsep)) else s()))
        case t: Term.Match           => m(Expr1, s(p(PostfixExpr, t.expr), " ", kw("match"), " {", r(t.cases.map(i(_)), ""), n("}")))
        case t: Term.Try             =>
          m(Expr1, s(kw("try"), " ", p(Expr, t.expr),
            if (t.catchp.nonEmpty) s(" ", kw("catch"), " {", r(t.catchp.map(i(_)), ""), n("}")) else s(""),
            t.finallyp.map { finallyp => s(" ", kw("finally"), " ", finallyp) }.getOrElse(s())))
        case t: Term.TryWithHandler  =>
          m(Expr1, s(kw("try"), " ", p(Expr, t.expr), " ", kw("catch"), " ", t.catchp,
            t.finallyp.map { finallyp => s(" ", kw("finally"), " ", finallyp) }.getOrElse(s())))
        case t: Term.Function        =>
          t match {
            case Term.Function(Term.Param(mods, name: Term.Name, tptopt, _) :: Nil, body) if mods.exists(_.is[Mod.Implicit]) =>
              m(Expr, s(kw("implicit"), " ", name, tptopt.map(s(kw(":"), " ", _)).getOrElse(s()), " ", kw("=>"), " ", p(Expr, body)))
            case Term.Function(Term.Param(mods, name: Term.Name, None, _) :: Nil, body) =>
              m(Expr, s(name, " ", kw("=>"), " ", p(Expr, body)))
            case Term.Function(Term.Param(_, _: Name.Anonymous, decltpeOpt, _) :: Nil, body) =>
              val param = decltpeOpt match {
                case Some(decltpe) => s(kw("("), kw("_"), kw(":"), decltpe, kw(")"))
                case None => s(kw("_"))
              }
              m(Expr, param, " ", kw("=>"), " ", p(Expr, body))
            case Term.Function(params, body) =>
              m(Expr, s("(", r(params, ", "), ") ", kw("=>"), " ", p(Expr, body)))
          }
        case t: Term.PartialFunction => m(SimpleExpr, s("{", r(t.cases.map(i(_)), ""), n("}")))
        case t: Term.While           => m(Expr1, s(kw("while"), " (", t.expr, ") ", p(Expr, t.body)))
        case t: Term.Do              => m(Expr1, s(kw("do"), " ", p(Expr, t.body), " ", kw("while"), " (", t.expr, ")"))
        case t: Term.For             => m(Expr1, s(kw("for"), " (", r(t.enums, "; "), ") ", t.body))
        case t: Term.ForYield        => m(Expr1, s(kw("for"), " (", r(t.enums, "; "), ") ", kw("yield"), " ", t.body))
        case t: Term.New             => m(SimpleExpr, s(kw("new"), " ", t.init))
        case t: Term.NewAnonymous    =>
          val needsExplicitBraces = {
            val selfIsEmpty = t.templ.self.name.is[Name.Anonymous] && t.templ.self.decltpe.isEmpty
            t.templ.early.isEmpty && t.templ.inits.length < 2 && selfIsEmpty && t.templ.stats.isEmpty
          }
          m(SimpleExpr, s(kw("new"), " ", t.templ), w(" {", "", "}", needsExplicitBraces))
        case _: Term.Placeholder     => m(SimpleExpr1, kw("_"))
        case t: Term.Eta             => m(SimpleExpr, s(p(SimpleExpr1, t.expr), " ", kw("_")))
        case t: Term.Repeated        => s(p(PostfixExpr, t.expr), kw(":"), " ", kw("_*"))
        case t: Term.Param           =>
          val mods = t.mods.filter(!_.is[Mod.Implicit]) // NOTE: `implicit` in parameters is skipped in favor of `implicit` in the enclosing parameter list
          s(w(mods, " "), t.name, t.decltpe, t.default.map(s(" ", kw("="), " ", _)).getOrElse(s()))

        // Type
        case t: Type.Name         => m(Path, if (guessIsBackquoted(t)) s("`", t.value, "`") else s(t.value))
        case t: Type.Select       => m(SimpleTyp, s(t.qual, kw("."), t.name))
        case t: Type.Project      => m(SimpleTyp, s(p(SimpleTyp, t.qual), kw("#"), t.name))
        case t: Type.Singleton    => m(SimpleTyp, s(p(SimpleExpr1, t.ref), ".", kw("type")))
        case t: Type.Apply        => m(SimpleTyp, s(p(SimpleTyp, t.tpe), kw("["), r(t.args.map(arg => p(Typ, arg)), ", "), kw("]")))
        case t: Type.ApplyInfix   => m(InfixTyp(t.op.value), s(p(InfixTyp(t.op.value), t.lhs, left = true), " ", t.op, " ", p(InfixTyp(t.op.value), t.rhs, right = true)))
        case t @ (_: Type.Function | _: Type.ImplicitFunction) =>
          val (prefix, tParams, tRes) = t match {
            case Type.Function(params, res) => (s(), params, res)
            case Type.ImplicitFunction(params, res) => (s(kw("implicit"), " "), params, res)
          }
          val params = tParams match {
            case param +: Nil if !param.is[Type.Tuple] => s(p(AnyInfixTyp, param))
            case params => s("(", r(params.map(param => p(ParamTyp, param)), ", "), ")")
          }
          m(Typ, s(prefix, params, " ", kw("=>"), " ", p(Typ, tRes)))
        case t: Type.Tuple        => m(SimpleTyp, s("(", r(t.args, ", "), ")"))
        case t: Type.With         =>
          if (!dialect.allowWithTypes) throw new UnsupportedOperationException(s"$dialect doesn't support with types")
          m(WithTyp, s(p(WithTyp, t.lhs), " with ", p(WithTyp, t.rhs)))
        case t: Type.And          =>
          if (!dialect.allowAndTypes) throw new UnsupportedOperationException(s"$dialect doesn't support and types")
          m(InfixTyp("&"), s(p(InfixTyp("&"), t.lhs, left = true), " ", "&", " ", p(InfixTyp("&"), t.rhs, right = true)))
        case t: Type.Or           =>
          if (!dialect.allowOrTypes) throw new UnsupportedOperationException(s"$dialect doesn't support or types")
          m(InfixTyp("|"), s(p(InfixTyp("|"), t.lhs, left = true), " ", "|", " ", p(InfixTyp("|"), t.rhs, right = true)))
        case t: Type.Refine       => m(RefineTyp, t.tpe.map(tpe => s(p(WithTyp, tpe), " ")).getOrElse(s("")), "{", w(" ", r(t.stats, "; "), " ", t.stats.nonEmpty), "}")
        case t: Type.Existential  => m(Typ, s(p(AnyInfixTyp, t.tpe), " ", kw("forSome"), " { ", r(t.stats, "; "), " }"))
        case t: Type.Annotate     => m(AnnotTyp, s(p(SimpleTyp, t.tpe), " ", t.annots))
        case t: Type.Lambda       => m(Typ, t.tparams, " ", kw("=>"), " ", p(Typ, t.tpe))
        case t: Type.Method       => m(Typ, t.paramss, kw(":"), " ", p(Typ, t.tpe))
        case t: Type.Placeholder  => m(SimpleTyp, s(kw("_"), t.bounds))
        case t: Type.Bounds =>
          s(t.lo.map(lo => s(" ", kw(">:"), " ", p(Typ, lo))).getOrElse(s()), t.hi.map(hi => s(" ", kw("<:"), " ", p(Typ, hi))).getOrElse(s()))
        case t: Type.Repeated     => m(ParamTyp, s(p(Typ, t.tpe), kw("*")))
        case t: Type.ByName       => m(ParamTyp, s(kw("=>"), " ", p(Typ, t.tpe)))
        case t: Type.Var          => m(SimpleTyp, s(t.name.value))
        case t: Type.Param        =>
          val mods = t.mods.filter(m => !m.is[Mod.Covariant] && !m.is[Mod.Contravariant])
          require(t.mods.length - mods.length <= 1)
          val variance = t.mods.foldLeft("")((curr, m) => if (m.is[Mod.Covariant]) "+" else if (m.is[Mod.Contravariant]) "-" else curr)
          val tbounds = s(t.tbounds)
          val vbounds = {
            if (t.vbounds.nonEmpty && !dialect.allowViewBounds) throw new UnsupportedOperationException(s"$dialect doesn't support view bounds")
            r(t.vbounds.map { s(" ", kw("<%"), " ", _) })
          }
          val cbounds = r(t.cbounds.map { s(kw(":"), " ", _) })
          s(w(mods, " "), variance, t.name, t.tparams, tbounds, vbounds, cbounds)

        // Pat
        case t: Pat.Var              => m(SimplePattern, s(if (guessIsBackquoted(t.name)) s"`${t.name.value}`" else t.name.value))
        case _: Pat.Wildcard         => m(SimplePattern, kw("_"))
        case _: Pat.SeqWildcard      => m(SimplePattern, kw("_*"))
        case t: Pat.Bind             =>
          val separator = t.rhs match {
            case Pat.SeqWildcard() =>
              if (dialect.allowAtForExtractorVarargs) s(" ", kw("@"))
              else if (dialect.allowColonForExtractorVarargs) s(kw(":"))
              else throw new UnsupportedOperationException(s"$dialect doesn't support extractor varargs")
            case _ =>
              s(" ", kw("@"))
          }
          m(Pattern2, s(p(SimplePattern, t.lhs), separator, " ", p(AnyPattern3, t.rhs)))
        case t: Pat.Alternative      => m(Pattern, s(p(Pattern, t.lhs), " ", kw("|"), " ", p(Pattern, t.rhs)))
        case t: Pat.Tuple            => m(SimplePattern, s("(", r(t.args, ", "), ")"))
        case t: Pat.Extract          => m(SimplePattern, s(t.fun, t.args))
        case t: Pat.ExtractInfix     =>
          m(Pattern3(t.op.value), s(p(Pattern3(t.op.value), t.lhs, left = true), " ", t.op, " ", t.rhs match {
            case pat :: Nil => s(p(Pattern3(t.op.value), pat, right = true))
            case pats       => s(pats)
          }))
        case t: Pat.Interpolate      =>
          val parts = t.parts.map{ case Lit(part: String) => part }
          val zipped = parts.zip(t.args).map {
            case (part, id: Name) if !guessIsBackquoted(id) => s(part, "$", id.value)
            case (part, arg)                                =>
              s(part, "${", arg, "}")
          }
          m(SimplePattern, s(t.prefix, "\"", r(zipped), parts.last, "\""))
        case t: Pat.Xml              =>
          if (!dialect.allowXmlLiterals) throw new UnsupportedOperationException(s"$dialect doesn't support xml literals")
          val parts = t.parts.map{ case Lit(part: String) => part }
          val zipped = parts.zip(t.args).map{ case (part, arg) => s(part, "{", arg, "}") }
          m(SimplePattern, s(r(zipped), parts.last))
        case Pat.Typed(lhs, rhs : Lit) =>
          if (dialect.allowLiteralTypes) m(Pattern1, s(p(SimplePattern, lhs), kw(":"), " ", p(Literal, rhs)))
          else throw new UnsupportedOperationException(s"$dialect doesn't support literal types")
        case t: Pat.Typed            => m(Pattern1, s(p(SimplePattern, t.lhs), kw(":"), " ", p(RefineTyp, t.rhs)))

        // Lit
        case Lit.Boolean(value) => m(Literal, s(value.toString))
        case Lit.Byte(value)    => m(Literal, s("ByteLiterals.", if (value == 0) "Zero" else if (value > 0) "Plus" + value else "Minus" + value))
        case Lit.Short(value)   => m(Literal, s("ShortLiterals.", if (value == 0) "Zero" else if (value > 0) "Plus" + value else "Minus" + value))
        case Lit.Int(value)     => m(Literal, s(value.toString))
        case Lit.Long(value)    => m(Literal, s(value.toString + "L"))
        case t @ Lit.Float(value)  =>
          val n = value.toFloat
          if (java.lang.Float.isNaN(n)) s("Float.NaN")
          else {
            n match {
              case Float.PositiveInfinity => s("Float.PositiveInfinity")
              case Float.NegativeInfinity => s("Float.NegativeInfinity")
              case _ =>
                s(value, "f")
            }
          }
        case t @ Lit.Double(value) =>
          val n = value.toDouble
          if (java.lang.Double.isNaN(n)) s("Double.NaN")
          else {
            n match {
              case Double.PositiveInfinity => s("Double.PositiveInfinity")
              case Double.NegativeInfinity => s("Double.NegativeInfinity")
              case _ =>
                s(value, "d")
            }
          }
        case Lit.Char(value)    => m(Literal, s(enquote(value.toString, SingleQuotes)))
        // Strings should be triple-quoted regardless of what newline style is used.
        case Lit.String(value)  => m(Literal, s(enquote(value.toString, if (value.contains("\n")) TripleQuotes else DoubleQuotes)))
        case Lit.Symbol(value)  => m(Literal, s("'", value.name))
        case Lit.Null()         => m(Literal, s(kw("null")))
        case Lit.Unit()         => m(Literal, s("()"))

        // Member
        case t: Decl.Val       => s(w(t.mods, " "), kw("val"), " ", r(t.pats, ", "), kw(":"), " ", t.decltpe)
        case t: Decl.Var       => s(w(t.mods, " "), kw("var"), " ", r(t.pats, ", "), kw(":"), " ", t.decltpe)
        case t: Decl.Type      => s(w(t.mods, " "), kw("type"), " ", t.name, t.tparams, t.bounds)
        case t: Decl.Def       => s(w(t.mods, " "), kw("def"), " ", t.name, t.tparams, t.paramss, kw(":"), " ", t.decltpe)
        case t: Defn.Val       => s(w(t.mods, " "), kw("val"), " ", r(t.pats, ", "), t.decltpe, " ", kw("="), " ", t.rhs)
        case t: Defn.Var       => s(w(t.mods, " "), kw("var"), " ", r(t.pats, ", "), t.decltpe, " ", kw("="), " ", t.rhs.map(s(_)).getOrElse(s(kw("_"))))
        case t: Defn.Type      => s(w(t.mods, " "), kw("type"), " ", t.name, t.tparams, " ", kw("="), " ", t.body)
        case t: Defn.Class     => s(w(t.mods, " "), kw("class"), " ", t.name, t.tparams, w(" ", t.ctor, t.ctor.mods.nonEmpty), templ(t.templ))
        case t: Defn.Trait     =>
          if (dialect.allowTraitParameters || t.ctor.mods.isEmpty) {
            s(w(t.mods, " "), kw("trait"), " ", t.name, t.tparams, w(" ", t.ctor, t.ctor.mods.nonEmpty), templ(t.templ))
          } else {
            throw new UnsupportedOperationException(s"$dialect doesn't support trait parameters")
          }
        case t: Defn.Object    => s(w(t.mods, " "), kw("object"), " ", t.name, templ(t.templ))
        case t: Defn.Def       => s(w(t.mods, " "), kw("def"), " ", t.name, t.tparams, t.paramss, t.decltpe, " = ", t.body)
        case t: Defn.Macro     => s(w(t.mods, " "), kw("def"), " ", t.name, t.tparams, t.paramss, t.decltpe, " ", kw("="), " ", kw("macro"), " ", t.body)
        case t: Pkg            =>
          if (guessHasBraces(t)) s(kw("package"), " ", t.ref, " {", r(t.stats.map(i(_)), ""), n("}"))
          else s(kw("package"), " ", t.ref, r(t.stats.map(n(_))))
        case t: Pkg.Object     => s(kw("package"), " ", w(t.mods, " "), kw("object"), " ", t.name, templ(t.templ))
        case t: Ctor.Primary   => s(w(t.mods, " ", t.mods.nonEmpty && t.paramss.nonEmpty), t.paramss)
        case t: Ctor.Secondary =>
          if (t.stats.isEmpty) s(w(t.mods, " "), kw("def"), " ", kw("this"), t.paramss, " = ", t.init)
          else s(w(t.mods, " "), kw("def"), " ", kw("this"), t.paramss, " {", i(t.init), "", r(t.stats.map(i(_)), ""), n("}"))

        // Init
        case t: Init => s(if (t.tpe.is[Type.Singleton]) kw("this") else p(AnnotTyp, t.tpe), t.argss)

        // Self
        case t: Self => s(t.name, t.decltpe)

        // Template
        case t: Template =>
          val isSelfEmpty = t.self.name.is[Name.Anonymous] && t.self.decltpe.isEmpty
          val isSelfNonEmpty = !isSelfEmpty
          val isBodyEmpty = isSelfEmpty && t.stats.isEmpty
          val isTemplateEmpty = t.early.isEmpty && t.inits.isEmpty && isBodyEmpty
          if (isTemplateEmpty) s()
          else {
            val pearly = if (!t.early.isEmpty) s("{ ", r(t.early, "; "), " } with ") else s()
            val pparents = w(r(t.inits, " with "), " ", !t.inits.isEmpty && !isBodyEmpty)
            val pbody = {
              val isOneLiner = t.stats.length == 0 || (t.stats.length == 1 && !s(t.stats.head).toString.contains(EOL))
              (isSelfNonEmpty, t.stats) match {
                case (false, Nil) => s()
                case (false, List(stat)) if isOneLiner => s("{ ", stat, " }")
                case (false, stats) => s("{", r(stats.map(i(_)), ""), n("}"))
                case (true, Nil) => s("{ ", t.self, " => }")
                case (true, List(stat)) if isOneLiner => s("{ ", t.self, " => ", stat, " }")
                case (true, stats) => s("{ ", t.self, " =>", r(stats.map(i(_)), ""), n("}"))
              }
            }
            s(pearly, pparents, pbody)
          }

        // Mod
        case Mod.Annot(init)                 => s(kw("@"), p(SimpleTyp, init.tpe), init.argss)
        case Mod.Private(Name.Anonymous())   => s(kw("private"))
        case Mod.Private(within)             => s(kw("private"), kw("["), within, kw("]"))
        case Mod.Protected(Name.Anonymous()) => s(kw("protected"))
        case Mod.Protected(within)           => s(kw("protected"), kw("["), within, kw("]"))
        case _: Mod.Implicit                 => kw("implicit")
        case _: Mod.Final                    => kw("final")
        case _: Mod.Sealed                   => kw("sealed")
        case _: Mod.Override                 => kw("override")
        case _: Mod.Case                     => kw("case")
        case _: Mod.Abstract                 => kw("abstract")
        case _: Mod.Covariant                => kw("+")
        case _: Mod.Contravariant            => kw("-")
        case _: Mod.Lazy                     => kw("lazy")
        case _: Mod.ValParam                 => kw("val")
        case _: Mod.VarParam                 => kw("var")
        case _: Mod.Inline                   =>
          if (!dialect.allowInlineMods) throw new UnsupportedOperationException(s"$dialect doesn't support inline modifiers")
          kw("inline")

        // Enumerator
        case t: Enumerator.Val           => s(p(Pattern1, t.pat), " = ", p(Expr, t.rhs))
        case t: Enumerator.Generator     => s(p(Pattern1, t.pat), " <- ", p(Expr, t.rhs))
        case t: Enumerator.Guard         => s(kw("if"), " ", p(PostfixExpr, t.cond))

        // Import
        case t: Importee.Name     => s(t.name)
        case t: Importee.Rename   => s(t.name, " ", kw("=>"), " ", t.rename)
        case t: Importee.Unimport => s(t.name, " ", kw("=>"), " ", kw("_"))
        case _: Importee.Wildcard => kw("_")
        case t: Importer          => s(t.ref, ".", t.importees)
        case t: Import            => s(kw("import"), " ", r(t.importers, ", "))

        // Case
        case t: Case  =>
          val ppat = p(Pattern, t.pat)
          val pcond = t.cond.map(cond => s(" ", kw("if"), " ", p(PostfixExpr, cond))).getOrElse(s())
          val isOneLiner = {
            def isOneLiner(t: Case) = t.stats match {
              case Nil => true
              case head :: Nil => head.is[Lit] || head.is[Term.Name]
              case _ => false
            }
            t.parent match {
              case Some(Term.Match(_, cases)) => cases.forall(isOneLiner)
              case Some(Term.PartialFunction(cases)) => cases.forall(isOneLiner)
              case _ => isOneLiner(t)
            }
          }
          val pbody = (t.stats, isOneLiner) match {
            case (Nil, true) => s("")
            case (List(stat), true) => s(" ", stat)
            case (stats, _) => r(stats.map(i(_)), "")
          }
          s("case ", ppat, pcond, " ", kw("=>"), pbody)

        // Source
        case t: Source                   => r(t.stats, EOL)
      }

      // Multiples and optionals
      implicit def syntaxArgs: scala.meta.prettyprinters.Syntax[List[Term]] = scala.meta.prettyprinters.Syntax {
        case (b: Term.Block) :: Nil                                                     => s(" ", b)
        case (f @ Term.Function(params, _)) :: Nil if !params.exists(_.decltpe.isEmpty) => s(" { ", f, " }")
        case args                                                                       => s("(", r(args, ", "), ")")
      }
      implicit def syntaxArgss: scala.meta.prettyprinters.Syntax[List[List[Term]]] = scala.meta.prettyprinters.Syntax {
        r(_)
      }
      implicit def syntaxTargs: scala.meta.prettyprinters.Syntax[List[Type]] = scala.meta.prettyprinters.Syntax { targs =>
        if (targs.isEmpty) s()
        else s("[", r(targs, ", "), "]")
      }
      implicit def syntaxPats: scala.meta.prettyprinters.Syntax[List[Pat]] = scala.meta.prettyprinters.Syntax { pats =>
        s("(", r(pats, ", "), ")")
      }
      implicit def syntaxMods: scala.meta.prettyprinters.Syntax[List[Mod]] = scala.meta.prettyprinters.Syntax { mods =>
        if (mods.nonEmpty) r(mods, " ") else s()
      }
      implicit def syntaxAnnots: scala.meta.prettyprinters.Syntax[List[Mod.Annot]] = scala.meta.prettyprinters.Syntax { annots =>
        if (annots.nonEmpty) r(annots, " ") else s()
      }
      implicit def syntaxParams: scala.meta.prettyprinters.Syntax[List[Term.Param]] = scala.meta.prettyprinters.Syntax { params =>
        s("(", r(params, ", "), ")")
      }
      implicit def syntaxParamss: scala.meta.prettyprinters.Syntax[List[List[Term.Param]]] = scala.meta.prettyprinters.Syntax { paramss =>
        r(paramss.map(params => {
          s("(", w("implicit ", r(params, ", "), params.exists(_.mods.exists(_.is[Mod.Implicit]))), ")")
        }), "")
      }
      implicit def syntaxTparams: scala.meta.prettyprinters.Syntax[List[Type.Param]] = scala.meta.prettyprinters.Syntax { tparams =>
        if (tparams.nonEmpty) s("[", r(tparams, ", "), "]") else s()
      }
      implicit def syntaxTypeOpt: scala.meta.prettyprinters.Syntax[Option[Type]] = scala.meta.prettyprinters.Syntax {
        _.map { t => s(kw(":"), " ", t) }.getOrElse(s())
      }
      implicit def syntaxImportee: scala.meta.prettyprinters.Syntax[List[Importee]] = scala.meta.prettyprinters.Syntax {
        case (t: Importee.Name) :: Nil     => s(t)
        case (t: Importee.Wildcard) :: Nil => s(t)
        case (t: Importee.Rename) :: Nil   => s("{", t, "}")
        case importees                     => s("{ ", r(importees, ", "), " }")
      }

    }
    // NOTE: This is the current state of the art of smart prettyprinting.
    // If we prettyprint a tree that's just been parsed with the same dialect,
    // then we retain formatting. Otherwise, we don't, even in the tiniest.
    // I expect to improve on this in the nearest future, because we had it much better until recently.
    scala.meta.prettyprinters.Syntax { (x: T) =>
      // x.origin match {
      //   // NOTE: Options don't really matter,
      //   // because if we've parsed a tree, it's not gonna contain lazy seqs anyway.
      //   // case Origin.Parsed(_, originalDialect, _) if dialect == originalDialect && options == Options.Eager =>
      //   case Origin.Parsed(_, originalDialect, _) if dialect == originalDialect => s(x.pos.text)
      //   case _ => syntaxInstances.syntaxTree[T].apply(x)
      // }
      import syntaxInstances._
      import SyntacticGroup.Type._, SyntacticGroup.Term._, SyntacticGroup.Pat._, SyntacticGroup.Literal, SyntacticGroup.Path

      sealed abstract class DeltaChild[+T <: Tree : Syntax] {
        def name: String
        def showRes: Show.Result
      }

      case class SimpleDeltaChild[+T <: Tree : Syntax](name: String, delta: DeltaTree[T]) extends DeltaChild[T] {
        lazy val showRes = delta.showRes
        lazy val tree = delta.tree
      }
      case class ListDeltaChild[+T <: Tree : Syntax](name: String, deltas: List[DeltaTree[T]]) extends DeltaChild[T] {
        lazy val showRes = deltaListShow0(deltas)
        lazy val trees = deltas.map(_.tree)
      }
      case class OptionDeltaChild[+T <: Tree : Syntax](name: String, deltaOpt: Option[DeltaTree[T]]) extends DeltaChild[T] {
        lazy val showRes = deltaOptionShow0(deltaOpt)
        lazy val treeOpt: Option[T] = deltaOpt.map(_.tree)
      }
      case class ListListDeltaChild[+T <: Tree : Syntax](name: String, deltass: List[List[DeltaTree[T]]]) extends DeltaChild[T] {
        lazy val showRes = deltaListListShow0(deltass)
        lazy val treess = deltass.map(_.map(_.tree))
      }

      sealed abstract class DeltaTree[+T <: Tree : Syntax] {
        def tree: T

        def showRes: Show.Result

        def children: Map[String, DeltaChild[_ <: Tree]]
      }

      final case class DeltaLeaf[+T <: Tree : Syntax](tree: T, showRes: Show.Result) extends DeltaTree[T] {
        val children = Map()
      }

      final case class ReplacedTree[+T <: Tree : Syntax](del: DeletedTree[T], ins: InsertedTree[T], children: Map[String, DeltaChild[_ <: Tree]] = Map()) extends DeltaTree[T] {
        val tree = ins.tree
        val showRes = s(w(s"/*FROM ", del.del.showRes, " TO*/ "), ins.showRes)
      }
      final case class CopiedTree[+T <: Tree : Syntax](copied: DeltaLeaf[T], children: Map[String, DeltaChild[_ <: Tree]] = Map()) extends DeltaTree[T] {
        val tree = copied.tree
        val showRes = copied.showRes
      }
      final case class InsertedTree[+T <: Tree : Syntax](ins: DeltaLeaf[T], children: Map[String, DeltaChild[_ <: Tree]] = Map()) extends DeltaTree[T] {
        val tree = ins.tree
        val showRes = ins.showRes
      }
      final case class DeletedTree[+T <: Tree : Syntax](del: DeltaLeaf[T], children: Map[String, DeltaChild[_ <: Tree]] = Map()) extends DeltaTree[T] {
        val tree = del.tree
        val showRes = s(w(s"/*DEL[${del.tree.productPrefix}:", del.showRes, "]*/ "))
      }

      type TOExtracted[+T <: Tree] = (Diff, DeltaLeaf[T], Map[String, DeltaChild[_ <: Tree]])

      abstract class TreeObject[T <: Tree : Syntax] {
        def tpe: String

        def extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[T]]]
      }

      object TreeObject {
        def apply[T <: Tree : Syntax](implicit to: TreeObject[T]): TreeObject[T] = to

        implicit val ModAnnotTO: TreeObject[Mod.Annot] =  new TreeObject[Mod.Annot] {
          val tpe = "Mod.Annot"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Mod.Annot]]] = {
            case (ObjectType("Mod.Annot"), d) =>
              getField[Init](d)("init").map { case (d, init) =>
                ( d
                , DeltaLeaf(
                    Mod.Annot(init.tree)
                  , s(kw("@"), p2(SimpleTyp, init.delta.children("tpe").showRes), init.delta.children("argss").showRes)
                  )
                , Map(
                    "init" -> init
                  )
                )
              }
          }
        }

        implicit val ModTO: TreeObject[Mod] =  new TreeObject[Mod] {
          val tpe = "Mod"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Mod]]] = {
            case (l@ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>

              tpe0 match {
              // @branch trait Mod extends Tree
              // object Mod {
              //   @ast class Annot(init: Init) extends Mod {
              //     @deprecated("Use init instead", "1.9.0")
              //     def body = init
              //   }
                case "Mod.Annot" =>
                  ModAnnotTO.extract(l -> d)
              //   @ast class Private(within: Ref) extends Mod {
              //     checkFields(within.isWithin)
              //   }
                case "Mod.Private" =>
                  getField[Ref](d)("within").map { case (d, within) =>
                    ( d 
                    , DeltaLeaf(
                        Mod.Private(within.tree)
                      , s(kw("private"))
                      )
                    , Map(
                        "within" -> within
                      )
                    )
                  }
              // //   @ast class Protected(within: Ref) extends Mod {
              // //     checkFields(within.isWithin)
              // //   }
                case "Mod.Protected" =>
                  getField[Ref](d)("within").map { case (d, within) =>
                    ( d
                    , DeltaLeaf(
                        Mod.Protected(within.tree)
                      , within.tree match {
                          case Mod.Protected(Name.Anonymous()) => s(kw("protected"))
                          case Mod.Protected(within)           => s(kw("protected"), kw("["), within, kw("]"))
                        }
                      )
                    , Map(
                        "within" -> within
                      )
                    )
                  }              
              // //   @ast class Implicit() extends Mod
                case "Mod.Implicit" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Implicit()
                      , kw("implicit")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Final() extends Mod
                case "Mod.Final" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Final()
                      , kw("final")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Sealed() extends Mod
                case "Mod.Sealed" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Sealed()
                      , kw("sealed")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Override() extends Mod
                case "Mod.Override" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Override()
                      , kw("override")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Case() extends Mod
                case "Mod.Case" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Case()
                      , kw("case")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Abstract() extends Mod
                case "Mod.Abstract" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Abstract()
                      , kw("abstract")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Covariant() extends Mod
                case "Mod.Covariant" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Covariant()
                      , kw("+")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Contravariant() extends Mod
                case "Mod.Contravariant" =>
                  Right(
                    (d
                    , DeltaLeaf(
                        Mod.Contravariant()
                      , kw("-")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Lazy() extends Mod
                case "Mod.Lazy" =>
                  Right(
                    (d
                    , DeltaLeaf(
                        Mod.Lazy()
                      , kw("lazy")
                      )
                    , Map()
                    )
                  )
              // //   @ast class ValParam() extends Mod
                case "Mod.ValParam" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.ValParam()
                      , kw("val")
                      )
                    , Map()
                    )
                  )
                case "Mod.VarParam" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.VarParam()
                      , kw("var")
                      )
                    , Map()
                    )
                  )
              // //   @ast class Inline() extends Mod
                case "Mod.Inline" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Mod.Inline()
                      , {
                          if (!dialect.allowInlineMods) throw new UnsupportedOperationException(s"$dialect doesn't support inline modifiers")
                          kw("inline")
                        }
                      )
                    , Map()
                    )
                  )
              // // }

              }
          }

        }

        implicit val PatTO: TreeObject[Pat] = new TreeObject[Pat] {
          val tpe = "Pat"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Pat]]] = {
            case (ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) => 
              tpe0 match {
                // @ast class Var(name: scala.meta.Term.Name) extends Pat with Member.Term {
                //   // NOTE: can't do this check here because of things like `val X = 2`
                //   // checkFields(name.value(0).isLower)
                //   checkParent(ParentChecks.PatVar)
                // }
                case "Pat.Var" =>
                  getField[Term.Name](d)("name").map { case (d, name) =>
                    ( d
                    , DeltaLeaf(
                        Pat.Var(name.tree)
                      // TODO: use showRes
                      //, m(SimplePattern, s(if (guessIsBackquoted(name.tree)) s"`${name.tree.value}`" else name.tree.value))
                      , m(SimplePattern, name.showRes) 
                      )
                    , Map()
                    )
                  }
                // @ast class Wildcard() extends Pat
                case "Pat.Wildcard" =>
                  Right(
                    (d
                    , DeltaLeaf(
                        Pat.Wildcard()
                      , m(SimplePattern, kw("_"))
                      )
                    , Map()
                    )
                  )
                // @ast class SeqWildcard() extends Pat {
                //   checkParent(ParentChecks.PatSeqWildcard)
                // }
                case "Pat.SeqWildcard" =>
                  Right(
                    ( d
                    , DeltaLeaf(
                        Pat.SeqWildcard()
                      , m(SimplePattern, kw("_*"))
                      )
                    , Map()
                    )
                  )
                // @ast class Bind(lhs: Pat, rhs: Pat) extends Pat {
                //   checkFields(lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
                // }
                case "Pat.Bind" =>
                  getField[Pat](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Pat](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Pat.Bind(lhs.tree, rhs.tree)
                        , {
                            val separator = rhs.tree match {
                              case Pat.SeqWildcard() =>
                                if (dialect.allowAtForExtractorVarargs) s(" ", kw("@"))
                                else if (dialect.allowColonForExtractorVarargs) s(kw(":"))
                                else throw new UnsupportedOperationException(s"$dialect doesn't support extractor varargs")
                              case _ =>
                                s(" ", kw("@"))
                            }
                            m(Pattern2, s(p2(SimplePattern, lhs.showRes), separator, " ", p2(AnyPattern3, rhs.showRes)))
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Alternative(lhs: Pat, rhs: Pat) extends Pat
                case "Pat.Alternative" =>
                  getField[Pat](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Pat](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Pat.Alternative(lhs.tree, rhs.tree)
                        , m(Pattern, s(p2(Pattern, lhs.showRes), " ", kw("|"), " ", p2(Pattern, rhs.showRes)))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Tuple(args: List[Pat] @nonEmpty) extends Pat {
                //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Pat.Quasi]))
                // }
                case "Pat.Tuple" =>
                  getListField[Pat](d)("args").map { case (d, args) =>
                    ( d
                    , DeltaLeaf(
                        Pat.Tuple(args.trees)
                      , m(SimplePattern, s("(", r(args.deltas.map(_.showRes), ", "), ")"))
                      )
                    , Map()
                    )
                  }
                // @ast class Extract(fun: Term, args: List[Pat]) extends Pat {
                //   checkFields(fun.isExtractor)
                // }
                case "Pat.Extract" =>
                  getField[Term](d)("fun").flatMap { case (d, fun) =>
                    getListField[Pat](d)("args").map { case (d, args) =>
                      (d
                      , DeltaLeaf(
                          Pat.Extract(fun.tree, args.trees)
                        , m(SimplePattern, s(fun.showRes, args.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class ExtractInfix(lhs: Pat, op: Term.Name, rhs: List[Pat]) extends Pat
                case "Pat.ExtractInfix" =>
                  getField[Pat](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Term.Name](d)("op").flatMap { case (d, op) =>
                      getListField[Pat](d)("rhs").map { case (d, rhs) =>
                        ( d
                        , DeltaLeaf(
                            Pat.ExtractInfix(lhs.tree, op.tree, rhs.trees)
                          , {
                              // TODO
                              m(Pattern3(op.tree.value), s(p2(Pattern3(op.tree.value), lhs.showRes, left = true), " ", op.showRes, " ", rhs.deltas match {
                                case pat :: Nil => s(p2(Pattern3(op.tree.value), pat.showRes, right = true))
                                case pats       => s(deltaListShow0(pats))
                              }))  
                            } 
                          )
                        , Map()
                        )
                      }
                    }
                  }
                // @ast class Interpolate(prefix: Term.Name, parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
                //   checkFields(parts.length == args.length + 1)
                // }
                case "Pat.Interpolate" =>
                  getField[Term.Name](d)("prefix").flatMap { case (d, prefix) =>
                    getListField[Lit](d)("parts").flatMap { case (d, parts) =>
                      getListField[Pat](d)("args").map { case (d, args) =>
                        ( d
                        , DeltaLeaf(
                            Pat.Interpolate(prefix.tree, parts.trees, args.trees)
                          , {
                              // TODO
                              val parts0 = parts.trees.map{ case Lit(part: String) => part }
                              val zipped = parts0.zip(args.trees).map {
                                case (part, id: Name) if !guessIsBackquoted(id) => s(part, "$", id.value)
                                case (part, arg)                                =>
                                  s(part, "${", arg, "}")
                              }
                              m(SimplePattern, s(prefix.showRes, "\"", r(zipped), parts.trees.last, "\""))
                            }
                          )
                        , Map()
                        )
                      }
                    }
                  }
                // @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Pat]) extends Pat {
                //   checkFields(parts.length == args.length + 1)
                // }
                case "Pat.Xml" =>
                  getListField[Lit](d)("parts").flatMap { case (d, parts) =>
                    getListField[Pat](d)("args").map { case (d, args) =>
                      ( d
                      , DeltaLeaf(
                          Pat.Xml(parts.trees, args.trees)
                        , {
                            // TODO
                            if (!dialect.allowXmlLiterals) throw new UnsupportedOperationException(s"$dialect doesn't support xml literals")
                            val parts0 = parts.trees.map{ case Lit(part: String) => part }
                            val zipped = parts0.zip(args.trees).map{ case (part, arg) => s(part, "{", arg, "}") }
                            m(SimplePattern, s(r(zipped), parts.trees.last))
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Typed(lhs: Pat, rhs: Type) extends Pat {
                //   checkFields(lhs.is[Pat.Wildcard] || lhs.is[Pat.Var] || lhs.is[Pat.Quasi])
                //   checkFields(!rhs.is[Type.Var] && !rhs.is[Type.Placeholder])
                // }
                case "Pat.Typed" =>
                  getField[Pat](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Type](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Pat.Typed(lhs.tree, rhs.tree)
                        , {
                            // TODO
                            rhs.tree match {
                              case _ : Lit =>
                                if (dialect.allowLiteralTypes) m(Pattern1, s(p2(SimplePattern, lhs.showRes), kw(":"), " ", p2(Literal, rhs.showRes)))
                                else throw new UnsupportedOperationException(s"$dialect doesn't support literal types")
                              case _            => m(Pattern1, s(p2(SimplePattern, lhs.showRes), kw(":"), " ", p2(RefineTyp, rhs.showRes)))
                            }
                          }
                        )
                      , Map()
                      )
                    }
                  }
            }
          }
        }

        implicit val TermNameTO: TreeObject[Term.Name] = new TreeObject[Term.Name] {
          val tpe = "Term.Name"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Term.Name]]] = {
            case (ValueLabel(TreeNode(t@Term.Name(value))), d) =>
              Right(
                ( d
                , DeltaLeaf(
                    t
                  , m(Path, if (guessIsBackquoted(t)) s("`", value, "`") else s(value))
                  )
                , Map()
                )
              )
          }
        }

        implicit val TypeNameTO: TreeObject[Type.Name] = new TreeObject[Type.Name] {
          val tpe = "Type.Name"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Type.Name]]] = {
            case (ValueLabel(TreeNode(t@Type.Name(value))), d) =>
              Right(
                ( d
                , DeltaLeaf(
                    t
                  , m(Path, if (guessIsBackquoted(t)) s("`", t.value, "`") else s(t.value))
                  )
                , Map()
                )
              )
          }
        }

        implicit val NameTO: TreeObject[Name] = new TreeObject[Name] {
          val tpe = "Name"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Name]]] = {
            case (ValueLabel(TreeNode(Name.Anonymous())), d) => 
              Right(
                ( d
                , DeltaLeaf(
                    Name.Anonymous()
                  , s("_")
                  )
                , Map()
                )
              )

            case (ValueLabel(TreeNode(t@Name.Indeterminate(value))), d) => 
              Right(
                ( d
                , DeltaLeaf(
                    Name.Indeterminate(value)
                  , if (guessIsBackquoted(t)) s("`", value, "`") else s(value)
                  )
                , Map()
                )
              )
          }
        }

        implicit val TermRefTO: TreeObject[Term.Ref] = new TreeObject[Term.Ref] {
          val tpe = "Term.Ref"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Term.Ref]]] = {
            case (ObjectType("Term.This"), d) => 
              // @branch trait Ref extends Term with scala.meta.Ref
              // @ast class This(qual: scala.meta.Name) extends Term.Ref
              getField[Name](d)("qual"). map { case (d, qual) =>
                ( d
                , DeltaLeaf(
                    Term.This(qual.tree)
                  , {
                      val qual0 = if (qual.tree.is[Name.Anonymous]) s() else s(qual.showRes, ".")
                      m(Path, qual0, kw("this"))
                    }
                  )
                , Map()
                )
              }
              // @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Term.Ref
            case (ObjectType("Term.Super"), d) => 
              getField[Name](d)("thisp").flatMap { case (d, thisp) =>
                getField[Name](d)("superp").map { case (d, superp) =>
                  ( d
                  , DeltaLeaf(
                      Term.Super(thisp.tree, superp.tree)
                    , {
                        val thisqual = if (thisp.tree.is[Name.Anonymous]) s() else s(thisp.showRes, ".")
                        val superqual = if (superp.tree.is[Name.Anonymous]) s() else s("[", superp.showRes, "]")
                        m(Path, s(thisqual, kw("super"), superqual))
                      }
                    )
                  , Map()
                  )
                }
              }
              // @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
            case (l@ObjectType("Term.Name"), d) => 
              TermNameTO.extract(l, d)

              // @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
            case (ObjectType("Term.Select"), d) => 
              getField[Term](d)("qual").flatMap { case (d, qual) =>
                getField[Term.Name](d)("name").map { case (d, name) =>
                  val t = Term.Select(qual.tree, name.tree)
                  ( d
                  , DeltaLeaf(
                      t
                    , m(Path, s(p2(SimpleExpr, qual.showRes), if (guessIsPostfix(t)) " " else ".", name.showRes))
                    )
                  , Map()
                  )
                }
              }

              // @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
              //   checkFields(op.isUnaryOp)
              // }
            case (ObjectType("Term.ApplyUnary"), d) => 
              getField[Term.Name](d)("op").flatMap { case (d, op) =>
                getField[Term](d)("arg").map { case (d, arg) =>
                  val t = Term.ApplyUnary(op.tree, arg.tree)
                  ( d
                  , DeltaLeaf(
                      t
                    , m(PrefixExpr, s(op.showRes, p2(SimpleExpr, arg.showRes)))
                    )
                  , Map()
                  )
                }
              }
          }
        }

        implicit val InitTO: TreeObject[Init] = new TreeObject[Init] {
          val tpe = "Init"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Init]]] = {
            case (ObjectType("Init"), d) =>
              getField[Type](d)("tpe").flatMap { case (d, tpe) =>
                getField[Name](d)("name").flatMap { case (d, name) =>
                  getListListField[Term](d)("argss").map { case (d, argss) =>
                    ( d
                    , DeltaLeaf(
                        Init(tpe.tree, name.tree, argss.treess)
                      , s(if (tpe.tree.is[Type.Singleton]) kw("this") else p2(AnnotTyp, tpe.showRes), argss.showRes)
                      )
                    , Map()
                    )
                  }
                }
              }
          }
        }

        implicit val RefTO: TreeObject[Ref] = new TreeObject[Ref] {
          val tpe = "Ref"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Ref]]] = {
            NameTO.extract orElse TermRefTO.extract orElse InitTO.extract
          }
        }

        implicit val TypeBoundsTO: TreeObject[Type.Bounds] = new TreeObject[Type.Bounds] {
          val tpe = "Type.Bounds"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Type.Bounds]]] = {
            case (ObjectType("Type.Bounds"), d) =>
              getOptionField[Type](d)("lo").flatMap { case (d, lo) =>
                getOptionField[Type](d)("hi").map { case (d, hi) =>
                  ( d
                  , DeltaLeaf(
                      Type.Bounds(lo.treeOpt, hi.treeOpt)
                    , s(lo.deltaOpt.map(lo => s(" ", kw(">:"), " ", p2(Typ, lo.showRes))).getOrElse(s()), hi.deltaOpt.map(hi => s(" ", kw("<:"), " ", p2(Typ, hi.showRes))).getOrElse(s()))
                    )
                  , Map()
                  )
                }
              }
          }
        }


        implicit val TermParamTO: TreeObject[Term.Param] = new TreeObject[Term.Param] {
          val tpe = "Term.Param"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Term.Param]]] = {
            case (ObjectType("Term.Param"), d) =>
              getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                getField[Term.Name](d)("name").flatMap { case (d, name) =>
                  getOptionField[Type](d)("decltpe").flatMap { case (d, decltpe) =>
                    getOptionField[Term](d)("default").map { case (d, default) =>
                      ( d
                      , DeltaLeaf(
                          Term.Param(mods.trees, name.tree, decltpe.treeOpt, default.treeOpt)
                        , {
                            val mods0 = mods.trees.filter(!_.is[Mod.Implicit]) // NOTE: `implicit` in parameters is skipped in favor of `implicit` in the enclosing parameter list
                            s(w(mods0, " "), name.showRes, deltaOptionTypeShow(decltpe), default.deltaOpt.map(t => s(" ", kw("="), " ", t.showRes)).getOrElse(s()))
                          }
                        )
                      , Map()
                      )
                    }
                  }
                }
              }
          }
        }


        implicit val TypeParamTO: TreeObject[Type.Param] = new TreeObject[Type.Param] {
          val tpe = "Type.Param"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Type.Param]]] = {
            case (ObjectType("Type.Param"), d) =>
              getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                getField[Term.Name](d)("name").flatMap { case (d, name) =>
                  getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                    getField[Type.Bounds](d)("tbounds").flatMap { case (d, tbounds) =>
                      getListField[Type](d)("vbounds").flatMap { case (d, vbounds) =>
                        getListField[Type](d)("cbounds").map { case (d, cbounds) =>
                          ( d
                          , DeltaLeaf(
                              Type.Param(mods.trees, name.tree, tparams.trees, tbounds.tree, vbounds.trees, cbounds.trees)
                            , {
                                val mods0 = mods.trees.filter(m => !m.is[Mod.Covariant] && !m.is[Mod.Contravariant])
                                require(mods.trees.length - mods.trees.length <= 1)
                                val variance = mods.trees.foldLeft("")((curr, m) => if (m.is[Mod.Covariant]) "+" else if (m.is[Mod.Contravariant]) "-" else curr)
                                val tbounds0 = s(tbounds.showRes)
                                val vbounds0 = {
                                  if (vbounds.deltas.nonEmpty && !dialect.allowViewBounds) throw new UnsupportedOperationException(s"$dialect doesn't support view bounds")
                                  r(vbounds.deltas.map { t => s(" ", kw("<%"), " ", t.showRes) })
                                }
                                val cbounds0 = r(cbounds.deltas.map { t => s(kw(":"), " ", t.showRes) })
                                s(w(mods0, " "), variance, name.showRes, tparams.showRes, tbounds0, vbounds0, cbounds0)
                              }
                            )
                          , Map()
                          )
                        }
                      }
                    }
                  }
                }
              }
          }
        }


        implicit val TypeTO: TreeObject[Type] = new TreeObject[Type] {
          val tpe = "Type"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Type]]] = {
            case (ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>
              tpe0 match {
                // @branch trait Ref extends Type with scala.meta.Ref
                // @ast class Name(value: String @nonEmpty) extends scala.meta.Name with Type.Ref
                // @ast class Select(qual: Term.Ref, name: Type.Name) extends Type.Ref {
                case "Type.Select" =>
                  getField[Term.Ref](d)("qual").flatMap { case (d, qual) =>
                    getField[Type.Name](d)("name").map { case (d, name) =>
                      ( d
                      , DeltaLeaf(
                          Type.Select(qual.tree, name.tree)
                        , m(SimpleTyp, s(qual.showRes, kw("."), name.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                //   checkFields(qual.isPath || qual.is[Term.Super] || qual.is[Term.Ref.Quasi])
                // }
                // @ast class Project(qual: Type, name: Type.Name) extends Type.Ref
                case "Type.Project" =>
                  getField[Type](d)("qual").flatMap { case (xs, qual) =>
                    getField[Type.Name](d)("name").map { case (xs, name) =>
                      ( d
                      , DeltaLeaf(
                          Type.Project(qual.tree, name.tree)
                        , m(SimpleTyp, s(p2(SimpleTyp, qual.showRes), kw("#"), name.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Singleton(ref: Term.Ref) extends Type.Ref {
                //   checkFields(ref.isPath || ref.is[Term.Super])
                // }
                case "Type.Singleton" =>
                  getField[Term.Ref](d)("ref").map { case (d, ref) =>
                    ( d
                    , DeltaLeaf(
                        Type.Singleton(ref.tree)
                      , m(SimpleTyp, s(p2(SimpleExpr1, ref.showRes), ".", kw("type")))
                      )
                    , Map()
                    )
                  }
                // @ast class Apply(tpe: Type, args: List[Type] @nonEmpty) extends Type
                case "Type.Apply" =>
                  getField[Type](d)("tpe").flatMap { case (d, tpe) =>
                    getListField[Type](d)("args").map { case (d, args) =>
                      ( d
                      , DeltaLeaf(
                          Type.Apply(tpe.tree, args.trees)
                        , m(SimpleTyp, s(p2(SimpleTyp, tpe.showRes), kw("["), r(args.deltas.map(arg => p2(Typ, arg.showRes)), ", "), kw("]")))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class ApplyInfix(lhs: Type, op: Name, rhs: Type) extends Type
                case "Type.ApplyInfix" =>
                  getField[Type](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Type.Name](d)("op").flatMap { case (d, op) =>
                      getField[Type](d)("rhs").map { case (d, rhs) =>
                        ( d
                        , DeltaLeaf(
                            // TODO
                            Type.ApplyInfix(lhs.tree, op.tree, rhs.tree)
                          , m(InfixTyp(op.tree.value), s(p2(InfixTyp(op.tree.value), lhs.showRes, left = true), " ", op.showRes, " ", p2(InfixTyp(op.tree.value), rhs.showRes, right = true)))
                          )
                        , Map()
                        )
                      }
                    }
                  }
                // @ast class Function(params: List[Type], res: Type) extends Type
                case "Type.Function" =>
                  getListField[Type](d)("params").flatMap { case (d, params) =>
                    getField[Type](d)("res").map { case (d, res) =>
                    val t = Type.Function(params.trees, res.tree)
                      ( d
                      , DeltaLeaf(
                          t
                        , {
                            val params0 = params.deltas match {
                              case param +: Nil if !param.tree.is[Type.Tuple] => s(p2(AnyInfixTyp, param.showRes))
                              case params => s("(", r(params.map(param => p2(ParamTyp, param.showRes)), ", "), ")")
                            }
                            m(Typ, s(s(), params0, " ", kw("=>"), " ", p2(Typ, res.showRes)))  
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class ImplicitFunction(params: List[Type], res: Type) extends Type
                case "Type.ImplicitFunction" =>
                  getListField[Type](d)("params").flatMap { case (d, params) =>
                    getField[Type](d)("res").map { case (d, res) =>
                    val t = Type.Function(params.trees, res.tree)
                      ( d
                      , DeltaLeaf(
                          t
                        , {
                            val params0 = params.deltas match {
                              case param +: Nil if !param.tree.is[Type.Tuple] => s(p2(AnyInfixTyp, param.showRes))
                              case params => s("(", r(params.map(param => p2(ParamTyp, param.showRes)), ", "), ")")
                            }
                            m(Typ, s(s(kw("implicit"), " "), params0, " ", kw("=>"), " ", p2(Typ, res.showRes)))  
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Tuple(args: List[Type] @nonEmpty) extends Type {
                //   checkFields(args.length > 1 || (args.length == 1 && args.head.is[Type.Quasi]))
                // }
                case "Type.Tuple" =>
                  getListField[Type](d)("args").map { case (d, args) =>
                    ( d
                    , DeltaLeaf(
                        Type.Tuple(args.trees)
                      , m(SimpleTyp, s("(", r(args.deltas.map(_.showRes), ", "), ")"))
                      )
                    , Map()
                    )
                  }
                // @ast class With(lhs: Type, rhs: Type) extends Type
                case "Type.With" =>
                  getField[Type](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Type](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Type.With(lhs.tree, rhs.tree)
                        , {
                            if (!dialect.allowWithTypes) throw new UnsupportedOperationException(s"$dialect doesn't support with types")
                            m(WithTyp, s(p2(WithTyp, lhs.showRes), " with ", p2(WithTyp, rhs.showRes)))
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class And(lhs: Type, rhs: Type) extends Type
                case "Type.And" =>
                  getField[Type](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Type](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Type.And(lhs.tree, rhs.tree)
                        , {
                            if (!dialect.allowAndTypes) throw new UnsupportedOperationException(s"$dialect doesn't support and types")
                            m(InfixTyp("&"), s(p2(InfixTyp("&"), lhs.showRes, left = true), " ", "&", " ", p2(InfixTyp("&"), rhs.showRes, right = true)))
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Or(lhs: Type, rhs: Type) extends Type
                case "Type.Or" =>
                  getField[Type](d)("lhs").flatMap { case (d, lhs) =>
                    getField[Type](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Type.Or(lhs.tree, rhs.tree)
                        , {
                            if (!dialect.allowOrTypes) throw new UnsupportedOperationException(s"$dialect doesn't support or types")
                            m(InfixTyp("|"), s(p2(InfixTyp("|"), lhs.showRes, left = true), " ", "|", " ", p2(InfixTyp("|"), rhs.showRes, right = true)))                              
                          }
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Refine(tpe: Option[Type], stats: List[Stat]) extends Type {
                //   checkFields(stats.forall(_.isRefineStat))
                // }
                case "Type.Refine" =>
                  getOptionField[Type](d)("tpe").flatMap { case (d, tpe) =>
                    getListField[Stat](d)("stats").map { case (d, stats) =>
                      val t = Type.Refine(tpe.treeOpt, stats.trees)
                      ( d
                      , DeltaLeaf(
                          t
                        , m(RefineTyp, tpe.treeOpt.map(tpe => s(p(WithTyp, tpe), " ")).getOrElse(s("")), "{", w(" ", r(t.stats, "; "), " ", t.stats.nonEmpty), "}")
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Existential(tpe: Type, stats: List[Stat] @nonEmpty) extends Type {
                //   checkFields(stats.forall(_.isExistentialStat))
                // }
                case "Type.Existential" =>
                  getField[Type](d)("tpe").flatMap { case (d, tpe) =>
                    getListField[Stat](d)("stats").map { case (d, stats) =>
                      ( d
                      , DeltaLeaf(
                          Type.Existential(tpe.tree, stats.trees)
                        , m(Typ, s(p2(AnyInfixTyp, tpe.showRes), " ", kw("forSome"), " { ", r(stats.deltas.map(_.showRes), "; "), " }"))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Annotate(tpe: Type, annots: List[Mod.Annot] @nonEmpty) extends Type
                case "Type.Annotate" =>
                  getField[Type](d)("tpe").flatMap { case (d, tpe) =>
                    getListField[Mod.Annot](d)("annots").map { case (d, annots) =>
                      ( d
                      , DeltaLeaf(
                          Type.Annotate(tpe.tree, annots.trees)
                        , m(AnnotTyp, s(p2(SimpleTyp, tpe.showRes), " ", annots.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Lambda(tparams: List[Type.Param], tpe: Type) extends Type {
                //   checkParent(ParentChecks.TypeLambda)
                // }
                case "Type.Lambda" =>
                  getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                    getField[Type](d)("tpe").map { case (d, tpe) =>
                      ( d
                      , DeltaLeaf(
                          Type.Lambda(tparams.trees, tpe.tree)
                        , m(Typ, tparams.showRes, " ", kw("=>"), " ", p2(Typ, tpe.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Method(paramss: List[List[Term.Param]], tpe: Type) extends Type {
                //   checkParent(ParentChecks.TypeMethod)
                // }
                case "Type.Method" =>
                  getListListField[Term.Param](d)("paramss").flatMap { case (d, paramss) =>
                    getField[Type](d)("tpe").map { case (d, tpe) =>
                      ( d
                      , DeltaLeaf(
                          Type.Method(paramss.treess, tpe.tree)
                        , m(Typ, paramss.showRes, kw(":"), " ", p2(Typ, tpe.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                // @ast class Placeholder(bounds: Bounds) extends Type
                case "Type.Placeholder" =>
                  getField[Type.Bounds](d)("bounds").map { case (d, bounds) =>
                    ( d
                    , DeltaLeaf(
                        Type.Placeholder(bounds.tree)
                      , m(SimpleTyp, s(kw("_"), bounds.showRes))
                      )
                    , Map()
                    )
                  }

                // @ast class ByName(tpe: Type) extends Type {
                //   checkParent(ParentChecks.TypeByName)
                // }
                case "Type.ByName" =>
                  getField[Type](d)("tpe").map { case (d, tpe) =>
                    ( d
                    , DeltaLeaf(
                        Type.ByName(tpe.tree)
                      , m(ParamTyp, s(kw("=>"), " ", p2(Typ, tpe.showRes)))
                      )
                    , Map()
                    )
                  }
                // @ast class Repeated(tpe: Type) extends Type {
                //   checkParent(ParentChecks.TypeRepeated)
                // }
                case "Type.Repeated" =>
                  getField[Type](d)("tpe").map { case (d, tpe) =>
                    ( d
                    , DeltaLeaf(
                        Type.Repeated(tpe.tree)
                      , m(ParamTyp, s(p2(Typ, tpe.showRes), kw("*")))
                      )
                    , Map()
                    )
                  }
                // @ast class Var(name: Name) extends Type with Member.Type {
                //   checkFields(name.value(0).isLower)
                //   checkParent(ParentChecks.TypeVar)
                // }
                case "Type.Var" =>
                  getField[Type.Name](d)("name").map { case (xs, name) =>
                    (d
                    , DeltaLeaf(
                        Type.Var(name.tree)
                        // TODO
                      , m(SimpleTyp, s(name.showRes))
                      )
                    , Map()
                    )
                  }
              }
          }
        }

        implicit val TermTO: TreeObject[Term] = new TreeObject[Term] {
          val tpe = "Term"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Term]]] = {
            case (l@ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) => 
              tpe0 match {
                // @branch trait Term extends Stat
                // object Term {
                //   @branch trait Ref extends Term with scala.meta.Ref
                //   @ast class This(qual: scala.meta.Name) extends Term.Ref
                  case "Term.This" =>
                    TermRefTO.extract(l, d)
                //   @ast class Super(thisp: scala.meta.Name, superp: scala.meta.Name) extends Term.Ref
                  case "Term.Super" =>
                    TermRefTO.extract(l, d)
                //   @ast class Name(value: Predef.String @nonEmpty) extends scala.meta.Name with Term.Ref with Pat
                //   @ast class Select(qual: Term, name: Term.Name) extends Term.Ref with Pat
                  case "Term.Select" =>
                    TermRefTO.extract(l, d)
                //   @ast class Interpolate(prefix: Name, parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
                //     checkFields(parts.length == args.length + 1)
                //   }
                  case "Term.Interpolate" =>
                    TermRefTO.extract(l, d)
                //   @ast class Xml(parts: List[Lit] @nonEmpty, args: List[Term]) extends Term {
                //     checkFields(parts.length == args.length + 1)
                //   }
                  case "Term.Xml" =>
                    getListField[Lit](d)("parts").flatMap { case (xs, parts) =>
                      getListField[Term](d)("args").map { case (xs, args) =>
                        ( d
                        , DeltaLeaf(
                            Term.Xml(parts.trees, args.trees)
                          , {
                              if (!dialect.allowXmlLiterals) throw new UnsupportedOperationException(s"$dialect doesn't support xml literals")
                              // TODO
                              val parts0 = parts.trees.map{ case Lit(part: String) => part }
                              val zipped = parts0.zip(args.deltas).map{ case (part, arg) => s(part, "{", p2(Expr, arg.showRes), "}") }
                              m(SimpleExpr1, s(r(zipped), parts0.last))  
                            }
                          )
                        , Map()
                        )
                      }
                    }

                //   @ast class Apply(fun: Term, args: List[Term]) extends Term
                  case "Term.Apply" =>
                    getField[Term](d)("fun").flatMap { case (d, fun) =>
                      getListField[Term](d)("args").map { case (d, args) =>
                        ( d
                        , DeltaLeaf(
                            Term.Apply(fun.tree, args.trees)
                          , m(SimpleExpr1, s(p2(SimpleExpr1, fun.showRes), deltaListTermShow(args)))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class ApplyType(fun: Term, targs: List[Type] @nonEmpty) extends Term
                  case "Term.ApplyType" =>
                    getField[Term](d)("fun").flatMap { case (d, fun) =>
                      getListField[Type](d)("targs").map { case (d, targs) =>
                        ( d
                        , DeltaLeaf(
                            Term.ApplyType(fun.tree, targs.trees)
                          , m(SimpleExpr1, s(p2(SimpleExpr, fun.showRes), targs.showRes))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class ApplyInfix(lhs: Term, op: Name, targs: List[Type], args: List[Term]) extends Term
                  case "Term.ApplyInfix" =>
                    getField[Term](d)("lhs").flatMap { case (d, lhs) =>
                      getField[Term.Name](d)("op").flatMap { case (d, op) =>
                        getListField[Type](d)("targs").flatMap { case (d, targs) =>
                          getListField[Term](d)("args").map { case (d, args) =>
                            ( d
                            , DeltaLeaf(
                                Term.ApplyInfix(lhs.tree, op.tree, targs.trees, args.trees)
                              , {
                                  // TODO
                                  val args0 = args.deltas match {
                                    case arg :: Nil if arg.tree == Lit.Unit() =>
                                      s("(())")
                                    case arg :: Nil => arg.tree match {
                                      case _:Term =>
                                        s(p2(InfixExpr(op.tree.value), arg.showRes, right = true))
                                      case _ => arg.showRes
                                    }
                                    case args => deltaListShow0(args)
                                  }

                                  m(InfixExpr(op.tree.value), s(p2(InfixExpr(op.tree.value), lhs.showRes, left = true), " ", op.showRes, targs.showRes, " ", args.showRes))
                                }
                              )
                            , Map()
                            )
                          }
                        }
                      }
                    }
                //   @ast class ApplyUnary(op: Name, arg: Term) extends Term.Ref {
                //     checkFields(op.isUnaryOp)
                //   }
                  case "Term.ApplyUnary" =>
                    getField[Term.Name](d)("op").flatMap { case (d, op) =>
                      getField[Term](d)("arg").map { case (d, arg) =>
                        ( d
                        , DeltaLeaf(
                            Term.ApplyUnary(op.tree, arg.tree)
                          , m(PrefixExpr, s(op.showRes, p2(SimpleExpr, arg.showRes)))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Assign(lhs: Term, rhs: Term) extends Term {
                //     checkFields(lhs.is[Term.Quasi] || lhs.is[Term.Ref] || lhs.is[Term.Apply])
                //     checkParent(ParentChecks.TermAssign)
                //   }
                  case "Term.Assign" =>
                    getField[Term](d)("lhs").flatMap { case (d, lhs) =>
                      getField[Term](d)("rhs").map { case (d, rhs) =>
                        ( d
                        , DeltaLeaf(
                            Term.Assign(lhs.tree, rhs.tree)
                          , m(Expr1, s(p2(SimpleExpr1, lhs.showRes), " ", kw("="), " ", p2(Expr, rhs.showRes)))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Return(expr: Term) extends Term
                  case "Term.Return" =>
                    getField[Term](d)("expr").map { case (d, expr) =>
                      val t = Term.Return(expr.tree)
                      ( d
                      , DeltaLeaf(
                          t
                        , m(Expr1, s(kw("return"), if (guessHasExpr(t)) s(" ", p2(Expr, expr.showRes)) else s()))
                        )
                      , Map()
                      )
                    }
                //   @ast class Throw(expr: Term) extends Term
                  case "Term.Throw" =>
                    getField[Term](d)("expr").map { case (d, expr) =>
                      ( d
                      , DeltaLeaf(
                          Term.Throw(expr.tree)
                        , m(Expr1, s(kw("throw"), " ", p2(Expr, expr.showRes)))
                        )
                      , Map()
                      )
                    }
                //   @ast class Ascribe(expr: Term, tpe: Type) extends Term
                  case "Term.Ascribe" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getField[Type](d)("tpe").map { case (d, tpe) =>
                        ( d
                        , DeltaLeaf(
                            Term.Ascribe(expr.tree, tpe.tree)
                          , m(Expr1, s(p2(PostfixExpr, expr.showRes), kw(":"), " ", tpe.showRes))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Annotate(expr: Term, annots: List[Mod.Annot] @nonEmpty) extends Term
                  case "Term.Annotate" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getListField[Mod.Annot](d)("annots").map { case (d, annots) =>
                        ( d
                        , DeltaLeaf(
                            Term.Annotate(expr.tree, annots.trees)
                          , m(Expr1, s(p2(PostfixExpr, expr.showRes), kw(":"), " ", annots.showRes))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Tuple(args: List[Term] @nonEmpty) extends Term {
                //     // tuple must have more than one element
                //     // however, this element may be Quasi with "hidden" list of elements inside
                //     checkFields(args.length > 1 || (args.length == 1 && args.head.is[Term.Quasi]))
                //   }
                  case "Term.Tuple" =>
                    getListField[Term](d)("args").map { case (d, args) =>
                      ( d
                      , DeltaLeaf(
                          Term.Tuple(args.trees)
                        , m(SimpleExpr1, s("(", r(args.deltas.map(_.showRes), ", "), ")"))
                        )
                      , Map()
                      )
                    }
                //   @ast class Block(stats: List[Stat]) extends Term {
                //     checkFields(stats.forall(_.isBlockStat))
                //   }
                  case "Term.Block" =>
                    getListField[Stat](d)("stats").map { case (d, stats) =>
                      ( d
                      , DeltaLeaf(
                          Term.Block(stats.trees)
                        , {
                            // TODO
                            import Term.{Block, Function}
                            def pstats(s: List[Stat]) = r(s.map(i(_)), "")
                            stats.trees match {
                              case Function(Term.Param(mods, name: Term.Name, tptopt, _) :: Nil, Block(stats)) :: Nil if mods.exists(_.is[Mod.Implicit]) =>
                                m(SimpleExpr, s("{ ", kw("implicit"), " ", name, tptopt.map(s(kw(":"), " ", _)).getOrElse(s()), " ", kw("=>"), " ", pstats(stats), n("}")))
                              case Function(Term.Param(mods, name: Term.Name, None, _) :: Nil, Block(stats)) :: Nil =>
                                m(SimpleExpr, s("{ ", name, " ", kw("=>"), " ", pstats(stats), n("}")))
                              case Function(Term.Param(_, _: Name.Anonymous, _, _) :: Nil, Block(stats)) :: Nil =>
                                m(SimpleExpr, s("{ ", kw("_"), " ", kw("=>"), " ", pstats(stats), n("}")))
                              case Function(params, Block(stats)) :: Nil =>
                                m(SimpleExpr, s("{ (", r(params, ", "), ") => ", pstats(stats), n("}")))
                              case _ =>
                                m(SimpleExpr, if (stats.trees.isEmpty) s("{}") else s("{", /*pstats(stats.trees)*/ r(stats.deltas.map(t => i(t.showRes))), ""), n("}"))
                            }  
                          }
                        )
                      , Map()
                      )
                    }
                //   @ast class If(cond: Term, thenp: Term, elsep: Term) extends Term
                  case "Term.If" =>
                    getField[Term](d)("cond").flatMap { case (d, cond) =>
                      getField[Term](d)("thenp").flatMap { case (d, thenp) =>
                        getField[Term](d)("elsep").map { case (d, elsep) =>
                          val t = Term.If(cond.tree, thenp.tree, elsep.tree)
                          ( d
                          , DeltaLeaf(
                              t
                            , m(Expr1, s(kw("if"), " (", cond.showRes, ") ", p2(Expr, thenp.showRes), if (guessHasElsep(t)) s(" ", kw("else"), " ", p2(Expr, elsep.showRes)) else s()))
                            )
                          , Map()
                          )
                        }
                      }
                    }
                //   @ast class Match(expr: Term, cases: List[Case] @nonEmpty) extends Term
                  case "Term.Match" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getListField[Case](d)("cases").map { case (d, cases) =>
                        ( d
                        , DeltaLeaf(
                            Term.Match(expr.tree, cases.trees)
                          , m(Expr1, s(p2(PostfixExpr, expr.showRes), " ", kw("match"), " {", r(cases.deltas.map{ t => i(t.showRes) }, ""), n("}")))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Try(expr: Term, catchp: List[Case], finallyp: Option[Term]) extends Term
                  case "Term.Try" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getListField[Case](d)("catchp").flatMap { case (d, catchp) =>
                        getOptionField[Term](d)("finallyp").map { case (d, finallyp) =>
                          ( d
                          , DeltaLeaf(
                              Term.Try(expr.tree, catchp.trees, finallyp.treeOpt)
                            , {
                                m(Expr1, s(kw("try"), " ", p2(Expr, expr.showRes),
                                  if (catchp.trees.nonEmpty) s(" ", kw("catch"), " {", r(catchp.deltas.map(t => i(t.showRes)), ""), n("}")) else s(""),
                                  finallyp.deltaOpt.map { finallyp => s(" ", kw("finally"), " ", finallyp.showRes) }.getOrElse(s())))  
                              }
                            )
                          , Map()
                          )
                        }
                      }
                    }
                //   @ast class TryWithHandler(expr: Term, catchp: Term, finallyp: Option[Term]) extends Term
                  case "Term.TryWithHandler" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getField[Term](d)("catchp").flatMap { case (d, catchp) =>
                        getOptionField[Term](d)("finallyp").map { case (d, finallyp) =>
                          ( d
                          , DeltaLeaf(
                              Term.TryWithHandler(expr.tree, catchp.tree, finallyp.treeOpt)
                            , {
                                m(Expr1, s(kw("try"), " ", p2(Expr, expr.showRes), " ", kw("catch"), " ", catchp.showRes,
                                  finallyp.deltaOpt.map { finallyp => s(" ", kw("finally"), " ", finallyp.showRes) }.getOrElse(s())))  
                              }
                            )
                          , Map()
                          )
                        }
                      }
                    }
                //   @ast class Function(params: List[Term.Param], body: Term) extends Term {
                //     checkFields(params.forall(param => param.is[Term.Param.Quasi] || (param.name.is[scala.meta.Name.Anonymous] ==> param.default.isEmpty)))
                //     checkFields(params.exists(_.is[Term.Param.Quasi]) || params.exists(_.mods.exists(_.is[Mod.Implicit])) ==> (params.length == 1))
                //   }
                  case "Term.Function" =>
                    getListField[Term.Param](d)("params").flatMap { case (d, params) =>
                      getField[Term](d)("body").map { case (d, body) =>
                        ( d
                        , DeltaLeaf(
                            Term.Function(params.trees, body.tree)
                          , {
                              // TODO
                              params.trees match {
                                case Term.Param(mods, name: Term.Name, tptopt, _) :: Nil if mods.exists(_.is[Mod.Implicit]) =>
                                  m(Expr, s(kw("implicit"), " ", name, tptopt.map(s(kw(":"), " ", _)).getOrElse(s()), " ", kw("=>"), " ", p2(Expr, body.showRes)))
                                case Term.Param(mods, name: Term.Name, None, _) :: Nil =>
                                  m(Expr, s(name, " ", kw("=>"), " ", p2(Expr, body.showRes)))
                                case Term.Param(_, _: Name.Anonymous, decltpeOpt, _) :: Nil =>
                                  val param = decltpeOpt match {
                                    case Some(decltpe) => s(kw("("), kw("_"), kw(":"), decltpe, kw(")"))
                                    case None => s(kw("_"))
                                  }
                                  m(Expr, param, " ", kw("=>"), " ", p2(Expr, body.showRes))
                                case params =>
                                  m(Expr, s("(", r(params, ", "), ") ", kw("=>"), " ", p2(Expr, body.showRes)))
                              }
                            }
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class PartialFunction(cases: List[Case] @nonEmpty) extends Term
                  case "Term.PartialFunction" =>
                    getListField[Case](d)("cases").map { case (d, cases) =>
                      ( d
                      , DeltaLeaf(
                          Term.PartialFunction(cases.trees)
                        , m(SimpleExpr, s("{", r(cases.deltas.map{t => i(t.showRes)}, ""), n("}")))
                        )
                      , Map()
                      )
                    }
                //   @ast class While(expr: Term, body: Term) extends Term
                  case "Term.While" =>
                    getField[Term](d)("expr").flatMap { case (d, expr) =>
                      getField[Term](d)("body").map { case (d, body) =>
                        ( d
                        , DeltaLeaf(
                            Term.While(expr.tree, body.tree)
                          , m(Expr1, s(kw("while"), " (", expr.showRes, ") ", p2(Expr, body.showRes)))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class Do(body: Term, expr: Term) extends Term
                  case "Term.Do" =>
                    getField[Term](d)("body").flatMap { case (d, body) =>
                      getField[Term](d)("expr").map { case (d, expr) =>
                        ( d
                        , DeltaLeaf(
                            Term.Do(body.tree, expr.tree)
                          , m(Expr1, s(kw("do"), " ", p2(Expr, body.showRes), " ", kw("while"), " (", expr.showRes, ")"))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class For(enums: List[Enumerator] @nonEmpty, body: Term) extends Term {
                //     checkFields(enums.head.is[Enumerator.Generator] || enums.head.is[Enumerator.Quasi])
                //   }
                  case "Term.For" =>
                    getListField[Enumerator](d)("enums").flatMap { case (d, enums) =>
                      getField[Term](d)("body").map { case (d, body) =>
                        ( d
                        , DeltaLeaf(
                            Term.For(enums.trees, body.tree)
                          , m(Expr1, s(kw("for"), " (", r(enums.deltas.map(_.showRes), "; "), ") ", body.showRes))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class ForYield(enums: List[Enumerator] @nonEmpty, body: Term) extends Term
                  case "Term.ForYield" =>
                    getListField[Enumerator](d)("enums").flatMap { case (d, enums) =>
                      getField[Term](d)("body").map { case (d, body) =>
                        ( d
                        , DeltaLeaf(
                            Term.ForYield(enums.trees, body.tree)
                          , m(Expr1, s(kw("for"), " (", r(enums.deltas.map(_.showRes), "; "), ") ", kw("yield"), " ", body.showRes))
                          )
                        , Map()
                        )
                      }
                    }
                //   @ast class New(init: Init) extends Term
                  case "Term.New" =>
                    getField[Init](d)("init").map { case (d, init) =>
                      ( d
                      , DeltaLeaf(
                          Term.New(init.tree)
                        , m(SimpleExpr, s(kw("new"), " ", init.tree))
                        )
                      , Map()
                      )
                    }
                //   @ast class NewAnonymous(templ: Template) extends Term
                  case "Term.NewAnonymous" =>
                    getField[Template](d)("templ").map { case (d, templ) =>
                      ( d
                      , DeltaLeaf(
                          Term.NewAnonymous(templ.tree)
                        , {
                          // TODO
                            val needsExplicitBraces = {
                              val selfIsEmpty = templ.tree.self.name.is[Name.Anonymous] && templ.tree.self.decltpe.isEmpty
                              templ.tree.early.isEmpty && templ.tree.inits.length < 2 && selfIsEmpty && templ.tree.stats.isEmpty
                            }
                            m(SimpleExpr, s(kw("new"), " ", templ.showRes), w(" {", "", "}", needsExplicitBraces))  
                          }
                        )
                      , Map()
                      )
                    }
                //   @ast class Placeholder() extends Term
                  case "Term.Placeholder" =>
                    Right(
                      ( d
                      , DeltaLeaf(
                          Term.Placeholder()
                        , m(SimpleExpr1, kw("_"))
                        )
                      , Map()
                    ))

                //   @ast class Eta(expr: Term) extends Term
                  case "Term.Eta" =>
                    getField[Term](d)("expr").map { case (d, expr) =>
                      ( d
                      , DeltaLeaf(
                          Term.Eta(expr.tree)
                        , m(SimpleExpr, s(p2(SimpleExpr1, expr.showRes), " ", kw("_")))
                        )
                      , Map()
                      )
                    }
                //   @ast class Repeated(expr: Term) extends Term {
                //     checkParent(ParentChecks.TermRepeated)
                //   }
                  case "Term.Repeated" =>
                    getField[Term](d)("expr").map { case (d, expr) =>
                      ( d
                      , DeltaLeaf(
                          Term.Repeated(expr.tree)
                        , s(p2(PostfixExpr, expr.showRes), kw(":"), " ", kw("_*"))
                        )
                      , Map()
                      )
                    }

                // //   def fresh(): Term.Name = fresh("fresh")
                // //   def fresh(prefix: String): Term.Name = Term.Name(prefix + Fresh.nextId())
              }
          }
        }

        implicit val DeclTO: TreeObject[Decl] = new TreeObject[Decl] {
          val tpe = "Decl"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Decl]]] = {
            case (ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>
              tpe0 match {
                // @branch trait Decl extends Stat
                // object Decl {
                //   @ast class Val(mods: List[Mod],
                //                  pats: List[Pat] @nonEmpty,
                //                  decltpe: scala.meta.Type) extends Decl
                case "Decl.Val" =>
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getListField[Pat](d)("pats").flatMap { case (d, pats) =>
                      getField[Type](d)("decltpe").map { case (d, decltpe) =>
                        ( d
                        , DeltaLeaf(
                            Decl.Val(mods.trees, pats.trees, decltpe.tree)
                          , s(w(mods.showRes, " "), kw("val"), " ", r(pats.deltas.map(_.showRes), ", "), kw(":"), " ", decltpe.showRes)
                          )
                        , Map()
                        )
                      }
                    }
                  }
                //   @ast class Var(mods: List[Mod],
                //                  pats: List[Pat] @nonEmpty,
                //                  decltpe: scala.meta.Type) extends Decl
                case "Decl.Var" =>
                  getListField[Mod](d)("mods").flatMap { case (xs, mods) =>
                    getListField[Pat](d)("pats").flatMap { case (xs, pats) =>
                      getField[Type](d)("decltpe").map { case (xs, decltpe) =>
                        ( d
                        , DeltaLeaf(
                            Decl.Var(mods.trees, pats.trees, decltpe.tree)
                          , s(w(mods.showRes, " "), kw("var"), " ", r(pats.deltas.map(_.showRes), ", "), kw(":"), " ", decltpe.showRes)
                          )
                        , Map()
                        )
                      }
                    }
                  }
                //   @ast class Def(mods: List[Mod],
                //                  name: Term.Name,
                //                  tparams: List[scala.meta.Type.Param],
                //                  paramss: List[List[Term.Param]],
                //                  decltpe: scala.meta.Type) extends Decl with Member.Term
                case "Decl.Def" =>
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Term.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getListListField[Term.Param](d)("paramss").flatMap { case (d, paramss) =>
                          getField[Type](d)("decltpe").map { case (d, decltpe) =>
                            ( d
                            , DeltaLeaf(
                                Decl.Def(mods.trees, name.tree, tparams.trees, paramss.treess, decltpe.tree)
                              , s(w(mods.showRes, " "), kw("def"), " ", name.showRes, tparams.showRes, deltaListListTermParamShow(paramss), kw(":"), " ", decltpe.showRes)
                              )
                            , Map()
                            )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Type.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getField[Type.Bounds](d)("bounds").map { case (d, bounds) =>
                          ( d
                          , DeltaLeaf(
                              Decl.Type(mods.trees, name.tree, tparams.trees, bounds.tree)
                            , s(w(mods.showRes, " "), kw("type"), " ", name.showRes, tparams.showRes, bounds.showRes)
                            )
                          , Map()
                          )
                        }
                      }
                    }
                  }
              }
          }
        }


        implicit val DefnTO: TreeObject[Defn] = new TreeObject[Defn] {
          val tpe = "Defn"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Defn]]] = {
            case (l@ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>
              tpe0 match {
                // @branch trait Defn extends Stat
                // object Defn {
                //   @ast class Val(mods: List[Mod],
                //                  pats: List[Pat] @nonEmpty,
                //                  decltpe: Option[scala.meta.Type],
                //                  rhs: Term) extends Defn {
                //     checkFields(pats.forall(!_.is[Term.Name]))
                //   }
                case "Defn.Val" =>
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getListField[Pat](d)("pats").flatMap { case (d, pats) =>
                      getOptionField[Type](d)("decltpe").flatMap { case (d, decltpe) =>
                        getField[Term](d)("rhs").map { case (d, rhs) =>
                          ( d
                          , DeltaLeaf(
                              Defn.Val(mods.trees, pats.trees, decltpe.treeOpt, rhs.tree)
                            , s(w(mods.showRes, " "), kw("val"), " ", r(pats.deltas.map(_.showRes), ", "), decltpe.showRes, " ", kw("="), " ", rhs.showRes)
                            )
                          , Map()
                          )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getListField[Pat](d)("pats").flatMap { case (d, pats) =>
                      getOptionField[Type](d)("decltpe").flatMap { case (d, decltpe) =>
                        getOptionField[Term](d)("rhs").map { case (d, rhs) =>
                          ( d
                          , DeltaLeaf(
                              Defn.Var(mods.trees, pats.trees, decltpe.treeOpt, rhs.treeOpt)
                            , s(w(mods.showRes, " "), kw("var"), " ", r(pats.deltas.map(_.showRes), ", "), decltpe.showRes, " ", kw("="), " ", rhs.deltaOpt.map(t => s(t.showRes)).getOrElse(s(kw("_"))))
                            )
                          , Map()
                          )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Term.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getListListField[Term.Param](d)("paramss").flatMap { case (d, paramss) =>
                          getOptionField[Type](d)("decltpe").flatMap { case (d, decltpe) =>
                            getField[Term](d)("body").map { case (d, body) =>
                              ( d
                              , DeltaLeaf(
                                  Defn.Def(mods.trees, name.tree, tparams.trees, paramss.treess, decltpe.treeOpt, body.tree)
                                , s(w(mods.showRes, " "), kw("def"), " ", name.showRes, tparams.showRes, deltaListListTermParamShow(paramss), deltaOptionTypeShow(decltpe), " = ", body.showRes)
                                )
                              , Map()
                              )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Term.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getListListField[Term.Param](d)("paramss").flatMap { case (xs, paramss) =>
                          getOptionField[Type](d)("decltpe").flatMap { case (xs, decltpe) =>
                            getField[Term](d)("body").map { case (xs, body) =>
                              ( d
                              , DeltaLeaf(
                                  Defn.Macro(mods.trees, name.tree, tparams.trees, paramss.treess, decltpe.treeOpt, body.tree)
                                , s(w(mods.showRes, " "), kw("def"), " ", name.showRes, tparams.showRes, paramss.showRes, decltpe.showRes, " ", kw("="), " ", kw("macro"), " ", body.showRes)
                                )
                              , Map()
                              )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Type.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getField[Type](d)("body").map { case (d, body) =>
                          ( d
                          , DeltaLeaf(
                              Defn.Type(mods.trees, name.tree, tparams.trees, body.tree)
                            , s(w(mods.showRes, " "), kw("type"), " ", name.showRes, tparams.showRes, " ", kw("="), " ", body.showRes)
                            )
                          , Map()
                          )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Type.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getField[Ctor.Primary](d)("ctor").flatMap { case (d, ctor) =>
                          getField[Template](d)("templ").map { case (d, templ) =>
                            ( d
                            , DeltaLeaf(
                                Defn.Class(mods.trees, name.tree, tparams.trees, ctor.tree, templ.tree)
                              , s(w(mods.showRes, " "), kw("class"), " ", name.showRes, tparams.showRes, w(" ", ctor.showRes, ctor.tree.mods.nonEmpty), templ.showRes)
                              )
                            , Map()
                            )
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
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Type.Name](d)("name").flatMap { case (d, name) =>
                      getListField[Type.Param](d)("tparams").flatMap { case (d, tparams) =>
                        getField[Ctor.Primary](d)("ctor").flatMap { case (d, ctor) =>
                          getField[Template](d)("templ").map { case (d, templ) =>
                            ( d
                            , DeltaLeaf(
                                Defn.Trait(mods.trees, name.tree, tparams.trees, ctor.tree, templ.tree)
                              , {
                                  if (dialect.allowTraitParameters || ctor.tree.mods.isEmpty) {
                                    s(w(mods.showRes, " "), kw("trait"), " ", name.showRes, tparams.showRes, w(" ", ctor.showRes, ctor.tree.mods.nonEmpty), templ.showRes)
                                  } else {
                                    throw new UnsupportedOperationException(s"$dialect doesn't support trait parameters")
                                  }  
                                }
                              )
                            , Map()
                            )
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
                  DefnObjectTO.extract(l, d)
              }

          }
        }

        implicit val ImportTO: TreeObject[Import] = new TreeObject[Import] {
          val tpe = "Import"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Import]]] = {
            case (ObjectType(`tpe`), d) =>
              getListField[Importer](d)("importers").map { case (d, importers) =>
                ( d
                , DeltaLeaf(
                    Import(importers.trees)
                  , s(kw("import"), " ", r(importers.deltas.map(_.showRes), ", "))
                  )
                , Map()
                )
              }
          }
        }

        implicit val ImporterTO: TreeObject[Importer] = new TreeObject[Importer] {
          val tpe = "Importer"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Importer]]] = {
            case (ObjectType(`tpe`), d) =>
              getField[Term.Ref](d)("ref").flatMap { case (d, ref) =>
                getListField[Importee](d)("importees").map { case (d, importees) =>
                  ( d
                  , DeltaLeaf(
                      Importer(ref.tree, importees.trees)
                    , s(ref.showRes, ".", importees.showRes)
                    )
                  , Map()
                  )
                }
              }
          }
        }


        implicit val SelfTO: TreeObject[Self] = new TreeObject[Self] {
          val tpe = "Self"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Self]]] = {
            case (ObjectType(`tpe`), d) =>
              getField[Name](d)("name").flatMap { case (d, name) =>
                getOptionField[Type](d)("decltpe").map { case (d, decltpe) =>
                  ( d
                  , DeltaLeaf(
                      Self(name.tree, decltpe.treeOpt)
                    , s(name.showRes, decltpe.showRes)
                    )
                  , Map()
                  )
                }
              }
          }
        }

        implicit val LitTO: TreeObject[Lit] = new TreeObject[Lit] {
          val tpe = "Lit"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Lit]]] = {
            case (ValueLabel(TreeNode(t@Lit(value))), d) =>
                Right(
                  ( d
                  , DeltaLeaf(
                      t
                    , t match {
                        // Lit
                        case Lit.Boolean(value) => m(Literal, s(value.toString))
                        case Lit.Byte(value)    => m(Literal, s("ByteLiterals.", if (value == 0) "Zero" else if (value > 0) "Plus" + value else "Minus" + value))
                        case Lit.Short(value)   => m(Literal, s("ShortLiterals.", if (value == 0) "Zero" else if (value > 0) "Plus" + value else "Minus" + value))
                        case Lit.Int(value)     => m(Literal, s(value.toString))
                        case Lit.Long(value)    => m(Literal, s(value.toString + "L"))
                        case t @ Lit.Float(value)  =>
                          val n = value.toFloat
                          if (java.lang.Float.isNaN(n)) s("Float.NaN")
                          else {
                            n match {
                              case Float.PositiveInfinity => s("Float.PositiveInfinity")
                              case Float.NegativeInfinity => s("Float.NegativeInfinity")
                              case _ =>
                                s(value, "f")
                            }
                          }
                        case t @ Lit.Double(value) =>
                          val n = value.toDouble
                          if (java.lang.Double.isNaN(n)) s("Double.NaN")
                          else {
                            n match {
                              case Double.PositiveInfinity => s("Double.PositiveInfinity")
                              case Double.NegativeInfinity => s("Double.NegativeInfinity")
                              case _ =>
                                s(value, "d")
                            }
                          }
                        case Lit.Char(value)    => m(Literal, s(enquote(value.toString, SingleQuotes)))
                        // Strings should be triple-quoted regardless of what newline style is used.
                        case Lit.String(value)  => m(Literal, s(enquote(value.toString, if (value.contains("\n")) TripleQuotes else DoubleQuotes)))
                        case Lit.Symbol(value)  => m(Literal, s("'", value.name))
                        case Lit.Null()         => m(Literal, s(kw("null")))
                        case Lit.Unit()         => m(Literal, s("()"))

                      }
                    )
                  , Map()
                  )
                )
          }
        }


        implicit val CaseTO: TreeObject[Case] = new TreeObject[Case] {
          val tpe = "Case"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Case]]] = {
            case (ObjectType(`tpe`), d)  =>
              getField[Pat](d)("pat").flatMap { case (d, pat) =>
                getOptionField[Term](d)("cond").flatMap { case (d, cond) =>
                  getField[Term](d)("body").map { case (d, body) =>
                    val t = Case(pat.tree, cond.treeOpt, body.tree)
                    ( d
                    , DeltaLeaf(
                        t
                      , { 
                          // TODO
                          val ppat = p2(Pattern, pat.showRes)
                          val pcond = cond.deltaOpt.map(cond => s(" ", kw("if"), " ", p2(PostfixExpr, cond.showRes))).getOrElse(s())
                          val stats: List[Stat] = body.tree match {
                            case Term.Block(stats) => stats
                            case body => List(body)
                          }
                          val isOneLiner = {
                            def isOneLiner(t: Case) = stats match {
                              case Nil => true
                              case head :: Nil => head.is[Lit] || head.is[Term.Name]
                              case _ => false
                            }
                            t.parent match {
                              case Some(Term.Match(_, cases)) => cases.forall(isOneLiner)
                              case Some(Term.PartialFunction(cases)) => cases.forall(isOneLiner)
                              case _ => isOneLiner(t)
                            }
                          }
                          val pbody = (stats, isOneLiner) match {
                            case (Nil, true) => s("")
                            case (List(stat), true) => s(" ", stat)
                            case (stats, _) => r(stats.map(t => i(t)), "")
                          }
                          s("case ", ppat, pcond, " ", kw("=>"), pbody)  
                        }
                      )
                    , Map()
                    )
                  }
                }
              }
          }
        }

        implicit val EnumeratorTO: TreeObject[Enumerator] = new TreeObject[Enumerator] {
          val tpe = "Enumerator"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Enumerator]]] = {
            case (ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>
              tpe0 match {
                // @branch trait Enumerator extends Tree
                // object Enumerator {
                //   @ast class Generator(pat: Pat, rhs: Term) extends Enumerator
                case "Enumerator.Generator" =>
                  getField[Pat](d)("pat").flatMap { case (d, pat) =>
                    getField[Term](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Enumerator.Generator(pat.tree, rhs.tree)
                        , s(p2(Pattern1, pat.showRes), " <- ", p2(Expr, rhs.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                //   @ast class Val(pat: Pat, rhs: Term) extends Enumerator
                case "Enumerator.Val" =>
                  getField[Pat](d)("pat").flatMap { case (d, pat) =>
                    getField[Term](d)("rhs").map { case (d, rhs) =>
                      ( d
                      , DeltaLeaf(
                          Enumerator.Val(pat.tree, rhs.tree)
                        , s(p2(Pattern1, pat.showRes), " = ", p2(Expr, rhs.showRes))
                        )
                      , Map()
                      )
                    }
                  }
                //   @ast class Guard(cond: Term) extends Enumerator
                case "Enumerator.Guard" =>
                  getField[Term](d)("cond").map { case (xs, cond) =>
                    ( d
                    , DeltaLeaf(
                        Enumerator.Guard(cond.tree)
                      , s(kw("if"), " ", p2(PostfixExpr, cond.showRes))
                      )
                    , Map()
                    )
                  }
                // }
            }
          }
        }

        implicit val CtorPrimaryTO: TreeObject[Ctor.Primary] = new TreeObject[Ctor.Primary] {
          val tpe = "Ctor.Primary"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Ctor.Primary]]] = {
            case (ObjectType(`tpe`), d) =>
              // @branch trait m extends Tree with Member
              // object Ctor {
              //   @ast class Primary(mods: List[Mod],
              //                      name: Name,
              //                      paramss: List[List[Term.Param]]) extends Ctor
              getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                getField[Name](d)("name").flatMap { case (d, name) =>
                  getListListField[Term.Param](d)("paramss").map { case (d, paramss) =>
                    ( d
                    , DeltaLeaf(
                        Ctor.Primary(mods.trees, name.tree, paramss.treess)
                      , s(w(mods.trees, " ", mods.trees.nonEmpty && paramss.treess.nonEmpty), deltaListListTermParamShow(paramss))
                      )
                    , Map()
                    )
                  }
                }
              }
          }
        }

        implicit val CtorTO: TreeObject[Ctor] = new TreeObject[Ctor] {
          val tpe = "Ctor"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Ctor]]] = {
            case (l@ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) =>
              tpe0 match {
                // @branch trait m extends Tree with Member
                // object Ctor {
                //   @ast class Primary(mods: List[Mod],
                //                      name: Name,
                //                      paramss: List[List[Term.Param]]) extends Ctor
                case "Ctor.Primary" =>
                  CtorPrimaryTO.extract(l, d)
                //   @ast class Secondary(mods: List[Mod],
                //                        name: Name,
                //                        paramss: List[List[Term.Param]] @nonEmpty,
                //                        init: Init,
                //                        stats: List[Stat]) extends Ctor with Stat {
                //     checkFields(stats.forall(_.isBlockStat))
                //   }
                // }
                case "Ctor.Secondary" =>
                  getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                    getField[Name](d)("name").flatMap { case (d, name) =>
                      getListListField[Term.Param](d)("paramss").flatMap { case (d, paramss) =>
                        getField[Init](d)("init").flatMap { case (d, init) =>
                          getListField[Stat](d)("stats").map { case (d, stats) =>
                            ( d
                            , DeltaLeaf(
                                Ctor.Secondary(mods.trees, name.tree, paramss.treess, init.tree, stats.trees)
                              , {
                                  if (stats.trees.isEmpty) s(w(mods.showRes, " "), kw("def"), " ", kw("this"), paramss.showRes, " = ", init.showRes)
                                  else s(w(mods.showRes, " "), kw("def"), " ", kw("this"), paramss.showRes, " {", i(init.showRes), "", r(stats.deltas.map(t => i(t.showRes)), ""), n("}"))
                                }
                              )
                            , Map()
                            )
                          }
                        }
                      }
                    }
                  }
              }
          }
        }

        implicit val DefnObjectTO: TreeObject[Defn.Object] = new TreeObject[Defn.Object] {
          val tpe = "Defn.Object"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Defn.Object]]] = {
            case (ObjectType(`tpe`), d) => 
              getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                getField[Term.Name](d)("name").flatMap { case (d, name) =>
                  getField[Template](d)("templ").map { case (d, templ) =>
                    ( d
                    , DeltaLeaf(
                        Defn.Object(mods.trees, name.tree, templ.tree)
                      , s(w(mods.showRes, " "), kw("object"), " ", name.showRes, templ.showRes)
                      )
                    , Map(
                        "mods" -> mods
                      , "name" -> name
                      , "templ" -> templ
                      )
                    )
                  }
                }
              }
          }

        }

        implicit val TemplateTO: TreeObject[Template] = new TreeObject[Template] {
          val tpe = "Template"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Template]]] = {
            case (ObjectType(`tpe`), d) =>
              getListField[Stat](d)("early").flatMap { case (d, early) =>
                getListField[Init](d)("inits").flatMap { case (d, inits) =>
                  getField[Self](d)("self").flatMap { case (d, self) =>
                    getListField[Stat](d)("stats").map { case (d, stats) =>
                      val t = Template(early.trees, inits.trees, self.tree, stats.trees)

                      def res = {
                        val isSelfEmpty = t.self.name.is[Name.Anonymous] && t.self.decltpe.isEmpty
                        val isSelfNonEmpty = !isSelfEmpty
                        val isBodyEmpty = isSelfEmpty && t.stats.isEmpty
                        val isTemplateEmpty = t.early.isEmpty && t.inits.isEmpty && isBodyEmpty
                        
                        if (isTemplateEmpty) s()
                        else {
                          val pearly = if (!t.early.isEmpty) s("{ ", r(early.deltas.map(_.showRes), "; "), " } with ") else s()
                          val pparents = w(r(inits.deltas.map(_.showRes), " with "), " ", !t.inits.isEmpty && !isBodyEmpty)
                          val pbody = {
                            val isOneLiner = t.stats.length == 0 || (t.stats.length == 1 && !s(stats.deltas.head.showRes).toString.contains(EOL))
                            (isSelfNonEmpty, stats.deltas) match {
                              case (false, Nil) => s()
                              case (false, List(stat)) if isOneLiner => s("{ ", stat.showRes, " }")
                              case (false, stats) => s("{", r(stats.map(t => i(t.showRes)), ""), n("}"))
                              case (true, Nil) => s("{ ", self.showRes, " => }")
                              case (true, List(stat)) if isOneLiner => s("{ ", self.showRes, " => ", stat.showRes, " }")
                              case (true, stats) => s("{ ", self.showRes, " =>", r(stats.map(t => i(t.showRes)), ""), n("}"))
                            }
                          }
                          s(pearly, pparents, pbody)
                        }
                      }

                      ( d
                      , DeltaLeaf(
                            t
                          , if ( 
                              t.early.isEmpty 
                              && t.inits.isEmpty
                              && t.self.name.is[Name.Anonymous]
                              && t.self.decltpe.isEmpty
                              && t.stats.isEmpty
                            ) s()
                            else if (
                              t.inits.nonEmpty
                              || t.early.nonEmpty
                            ) s(" extends ", res)
                            else s(" ", res)
                        )
                      , Map()
                      )
                    }
                  }
                }
              }
            }
        }

        implicit val PkgTO: TreeObject[Pkg] = new TreeObject[Pkg] {
          val tpe = "Pkg"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Pkg]]] = {
            case (ObjectType(`tpe`), d) =>
              getField[Term.Ref](d)("ref").flatMap { case (d, ref) =>
                getListField[Stat](d)("stats").map { case (d, stats) =>
                  val t = Pkg(ref.tree, stats.trees)
                  ( d
                  , DeltaLeaf(
                      t
                    , {
                        if (guessHasBraces(t)) s(kw("package"), " ", ref.showRes, " {", r(stats.deltas.map(t => i(t.showRes)), ""), n("}"))
                        else s(kw("package"), " ", ref.showRes, r(stats.deltas.map(t => n(t.showRes))))
                      }
                    )
                  , Map()
                  )
                }
              }
          }
        }

        implicit val PkgObjectTO: TreeObject[Pkg.Object] = new TreeObject[Pkg.Object] {
          val tpe = "Pkg.Object"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Pkg.Object]]] = {
            case (ObjectType(`tpe`), d) =>
              getListField[Mod](d)("mods").flatMap { case (d, mods) =>
                getField[Term.Name](d)("name").flatMap { case (d, name) =>
                  getField[Template](d)("templ").map { case (d, templ) =>
                    ( d
                    , DeltaLeaf(
                        Pkg.Object(mods.trees, name.tree, templ.tree)
                      , s(kw("package"), " ", w(mods.showRes, " "), kw("object"), " ", name.showRes, templ.showRes)
                      )
                    , Map()
                    )
                  }
                }
              }
          }
        }


        implicit val ImporteeTO: TreeObject[Importee] = new TreeObject[Importee] {
          val tpe = "Importee"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Importee]]] = {
            case (ObjectType(tpe0), d) if (tpe0.startsWith(tpe)) => 
              tpe0 match {
                // @branch trait Importee extends Tree with Ref
                // object Importee {
                //   @ast class Wildcard() extends Importee
                case "Importee.Wildcard" => Right(
                  ( d
                  , DeltaLeaf(
                      Importee.Wildcard()
                    , kw("_")
                    )
                  , Map()
                  )
                )

                //   @ast class Name(name: scala.meta.Name) extends Importee {
                //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
                //   }
                case "Importee.Name" =>
                  getField[Name](d)("name").map { case (d, name) =>
                    ( d
                    , DeltaLeaf(
                        Importee.Name(name.tree)
                      , s(name.showRes)
                      )
                    , Map()
                    )
                  }
                //   @ast class Rename(name: scala.meta.Name, rename: scala.meta.Name) extends Importee {
                //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
                //     checkFields(rename.is[scala.meta.Name.Quasi] || rename.is[scala.meta.Name.Indeterminate])
                //   }
                case "Importee.Rename" =>
                  getField[Name](d)("name").flatMap { case (d, name) =>
                    getField[Name](d)("rename").map { case (d, rename) =>
                      ( d
                      , DeltaLeaf(
                          Importee.Rename(name.tree, rename.tree)
                        , s(name.showRes, " ", kw("=>"), " ", rename.showRes)
                        )
                      , Map()
                      )
                    }
                  }
                //   @ast class Unimport(name: scala.meta.Name) extends Importee {
                //     checkFields(name.is[scala.meta.Name.Quasi] || name.is[scala.meta.Name.Indeterminate])
                //   }
                // }
                case "Importee.Unimport" =>
                  getField[Name](d)("name").map { case (d, name) =>
                    ( d
                    , DeltaLeaf(
                        Importee.Unimport(name.tree)
                      , s(name.showRes, " ", kw("=>"), " ", kw("_"))
                      )
                    , Map()
                    )
                  }
              }
          }
        }


        implicit val StatTO: TreeObject[Stat] = new TreeObject[Stat] {
          val tpe = "Stat"

          val extract: PartialFunction[(Label, Diff), PatchError[TOExtracted[Stat]]] = {
            TermTO.extract orElse DeclTO.extract orElse DefnTO.extract orElse PkgTO.extract orElse
            ImportTO.extract orElse PkgTO.extract orElse PkgObjectTO.extract
          }
        }
      }

      def deltaListShow0[T <: Tree : Syntax](dts: List[DeltaTree[T]]): Show.Result = {        
        val ls: List[Show.Result] = dts.map { dt => dt.showRes }
        Show.Sequence(ls:_*)
      }
      def deltaListShow[T <: Tree : Syntax](dts: ListDeltaChild[T]): Show.Result = {
        deltaListShow0(dts.deltas)
      }

      def deltaOptionShow0[T <: Tree : Syntax](dt: Option[DeltaTree[T]]): Show.Result = {
        dt match {
          case None => Show.None
          case Some(dt) => s(dt.showRes)
        }
      }
      def deltaOptionShow[T <: Tree : Syntax](dt: OptionDeltaChild[T]): Show.Result = {
        deltaOptionShow0(dt.deltaOpt)
      }

      def deltaListListShow0[T <: Tree : Syntax](dtss: List[List[DeltaTree[T]]]): Show.Result = {
        val ls: List[Show.Result] = dtss.map { dt =>
          val s = dt.map(_.showRes)
          Show.Sequence(s:_*)
        }
        Show.Sequence(ls:_*)
      }      

      def deltaObject[T <: Tree : Syntax : TreeObject]: PartialFunction[(Label, Diff), PatchError[TOExtracted[T]]] = {
        TreeObject[T].extract orElse {
          case d => Left(PatchErrorMsg(s"can't extract ${TreeObject[T].tpe} from diff, bad diff $d"))
        }
      }

      def deltaListTermShow0(args: List[DeltaTree[Term]]): Show.Result = {
        args.map(_.tree) match {
          case (b: Term.Block) :: Nil                                                     => s(" ", args.head.showRes)
          case (f @ Term.Function(params, _)) :: Nil if !params.exists(_.decltpe.isEmpty) => s(" { ", args.head.showRes, " }")
          case _                                                                          => s("(", r(args.map(_.showRes), ", "), ")")
        }
      }
      def deltaListTermShow(args: ListDeltaChild[Term]): Show.Result = {
        deltaListTermShow0(args.deltas)
      }

      def deltaListTermParamShow0(params: List[DeltaTree[Term.Param]]): Show.Result = {
        s("(", r(params.map(_.showRes), ", "), ")")
      }
      def deltaListTermParamShow(params: ListDeltaChild[Term.Param]): Show.Result = {
        deltaListTermParamShow0(params.deltas)
      }

      def deltaListListTermParamShow0(paramss: List[List[DeltaTree[Term.Param]]]): Show.Result = {
        r(paramss.map(params => {
          s("(", w("implicit ", r(params.map(_.showRes), ", "), params.exists(_.tree.mods.exists(_.is[Mod.Implicit]))), ")")
        }), "")
      }
      def deltaListListTermParamShow(args: ListListDeltaChild[Term.Param]): Show.Result = {
        deltaListListTermParamShow0(args.deltass)
      }

      def deltaOptionTypeShow0(argOpt: Option[DeltaTree[Type]]): Show.Result = {
        argOpt.map { t => s(kw(":"), " ", t.showRes) }.getOrElse(s())
      }
      def deltaOptionTypeShow(args: OptionDeltaChild[Type]): Show.Result = {
        deltaOptionTypeShow0(args.deltaOpt)
      }

      // implicit def syntaxParams: scala.meta.prettyprinters.Syntax[List[Term.Param]] = scala.meta.prettyprinters.Syntax { params =>
      //   s("(", r(params, ", "), ")")
      // }
      // implicit def syntaxParamss: scala.meta.prettyprinters.Syntax[List[List[Term.Param]]] = scala.meta.prettyprinters.Syntax { paramss =>
      //   r(paramss.map(params => {
      //     s("(", w("implicit ", r(params, ", "), params.exists(_.mods.exists(_.is[Mod.Implicit]))), ")")
      //   }), "")
      // }

      def getDeltaTree[T <: Tree : Syntax : TreeObject](d: Diff): PatchError[(Diff, DeltaTree[T])] = {
        d match {
          case End =>
            Left(PatchErrorMsg(s"can't get diff field, empty diff $d"))

          case Del(ValueLabel(TreeNode(del)), Ins(ValueLabel(TreeNode(ins)), rest)) =>
            val delt = del.asInstanceOf[T]
            val inst = ins.asInstanceOf[T]
            Right(rest -> ReplacedTree(
              DeletedTree(DeltaLeaf(delt, s(delt)))
            , InsertedTree(DeltaLeaf(inst, s(inst)))
            ))

          case Cpy(l@ObjectType(_), d) =>
            //getObject(tpe, rest).map { case (d, dt) => d -> dt.asInstanceOf[DeltaTree[T]] }
            deltaObject[T](implicitly[Syntax[T]], TreeObject[T])(l, d).map {
              case (d, dl, cs) =>
                d -> CopiedTree(dl, cs)
            }

          case Ins(l@ObjectType(_), d) =>
            deltaObject[T](implicitly[Syntax[T]], TreeObject[T])(l, d).map {
              case (d, dl, cs) =>
                d -> InsertedTree(dl, cs)
            }

          case Del(l@ObjectType(_), d) =>
            deltaObject[T](implicitly[Syntax[T]], TreeObject[T])(l, d).map {
              case (d, dl, cs) =>
                d -> DeletedTree(dl, cs)
            }

          case Cpy(ValueLabel(TreeNode(tree)), d) =>
            val t = tree.asInstanceOf[T]
            Right(d -> CopiedTree(DeltaLeaf(t, s(t))))

          case Ins(ValueLabel(TreeNode(tree)), d) =>
            val t = tree.asInstanceOf[T]
            Right(d -> InsertedTree(DeltaLeaf(t, s(t))))

          case Del(ValueLabel(TreeNode(tree)), d) =>
            val t = tree.asInstanceOf[T]
            Right(d -> DeletedTree(DeltaLeaf(t, s(t))))

        }
      }


      def getField[T <: Tree : Syntax : TreeObject](d: Diff)(n: String): PatchError[(Diff, SimpleDeltaChild[T])] = {
        d match {
          case End =>
            Left(PatchErrorMsg(s"can't get diff field $n, empty diff $d"))

          // Can't insert/delete a field
          case Cpy(SimpleFieldLabel(`n`), rest) =>
            getDeltaTree[T](rest).map { case (d, t) => d -> SimpleDeltaChild(n, t) }

          case e => 
            Left(PatchErrorMsg(s"can't get diff field $n, $e is not simple field"))
        }
      }

      def getListField[T <: Tree : Syntax : TreeObject](d: Diff)(n: String): PatchError[(Diff, ListDeltaChild[T])] = {
        d match {
          case End =>
            Left(PatchErrorMsg(s"can't get list diff field $n, empty diff $d"))

          // Can't insert/delete a field
          case Cpy(TreeListFieldLabel(`n`, sz), rest) =>
            def stepListField(d: Diff, sz: Int, xs: List[DeltaTree[T]]): PatchError[(Diff, List[DeltaTree[T]])] = {
              if(sz > 0) {
                for {
                  res <- getDeltaTree[T](d)
                  (d2, delta) = res
                  res2 <- stepListField(d2, sz - 1, xs :+ delta)
                } yield res2
              } else {
                Right((d, xs))
              }
            }

            stepListField(rest, sz, Nil).map { case (d, ds) =>
              d -> ListDeltaChild(n, ds)
            }

          case e => 
            Left(PatchErrorMsg(s"can't get list diff field $n, $e is not list field"))

        }
      }      

      def getListListField[T <: Tree : Syntax : TreeObject](d: Diff)(n: String): PatchError[(Diff, ListListDeltaChild[T])] = {
        d match {
          case End =>
            Left(PatchErrorMsg(s"can't get listlist diff field $n, empty diff $d"))

          case Cpy(TreeListListFieldLabel(`n`, sz), rest) =>
            def stepListListField(d: Diff, sz: Int, xs: List[List[DeltaTree[T]]]): PatchError[(Diff, List[List[DeltaTree[T]]])] = {
              if(sz > 0) {
                for {
                  res <- getListField[T](d)(n)
                  (d2, ds) = res
                  res2 <- stepListListField(d2, sz - 1, xs :+ ds.deltas)
                } yield res2
              } else {
                Right((d, xs))
              }
            }

            stepListListField(rest, sz, Nil).map { case (d, ds) =>
              d -> ListListDeltaChild(n, ds)
            }

          case e => 
            Left(PatchErrorMsg(s"can't get listlist diff field $n, $e is not list of list field"))

        }
      }      


      def getOptionField[T <: Tree : Syntax : TreeObject](d: Diff)(n: String): PatchError[(Diff, OptionDeltaChild[T])] = {
        d match {
          case End =>
            Left(PatchErrorMsg(s"can't get option diff field $n, empty diff $d"))

          case Cpy(TreeOptionFieldLabel(`n`, isDef), rest) =>
            if (isDef) getDeltaTree[T](rest).map { case (d, dt) => d -> OptionDeltaChild(n, Some(dt)) }
            else Right(rest -> OptionDeltaChild(n, None))

          case e => 
            Left(PatchErrorMsg(s"can't get option diff field $n, $e is not simple field"))
        }
      }

      val getObject: PartialFunction[(Label, Diff), PatchError[TOExtracted[Tree]]] = {
        TreeObject[Template].extract orElse TreeObject[Term.Param].extract orElse
        TreeObject[Stat].extract orElse
        TreeObject[Type.Param].extract orElse TreeObject[Type.Bounds].extract orElse
        TreeObject[Type].extract orElse TreeObject[Pat].extract orElse
        TreeObject[Ctor].extract orElse
        TreeObject[Mod].extract orElse TreeObject[Enumerator].extract
      }

      def step(d: Diff): PatchError[List[Show.Result]] = d match {
        // case Cpy(ValueLabel(TreeNode(tree)), d) => 
        //   s(
        //     syntaxInstances.syntaxTree(tree),
        //     apply(dialect)(d)
        //   )
        case Cpy(l@ObjectType(tpe), d) =>
          getObject(l, d).flatMap { case (d, r, _) =>
            d match {
              case End => Right(List(r.showRes))
              case d   => step(d).map { rs => r.showRes +: rs }
            }
          }

        case End => Right(List(Show.None))

        // case err => Left(PatchErrorMsg(err.toStri))
      }

      step(x) match {
        case Left(err) => throw new UnsupportedOperationException(s"Error: $err")
        case Right(rs) => Show.Sequence(rs:_*)
      }
    }
  }
}
