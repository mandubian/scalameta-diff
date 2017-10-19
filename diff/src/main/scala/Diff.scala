package scala.meta
package diff

sealed trait Diff {
  def score: Int
}
final case class Ins(label: Label, diff: Diff) extends Diff {
  lazy val score = 1 + diff.score
}
final case class Del(label: Label, diff: Diff) extends Diff {
  lazy val score = 1 + diff.score
}
final case class Cpy(label: Label, diff: Diff) extends Diff {
  // why + 1... cpy is non impacting
  // lazy val score = 1 + diff.score
  lazy val score = 0 + diff.score
}
case object End extends Diff {
  lazy val score = 0
}


object Diff {

  def concat(diff1: Diff, diff2: Diff): Diff = {
    diff1 match {
      case End => diff2
      case Ins(label, d) => Ins(label, concat(d, diff2))
      case Del(label, d) => Del(label, concat(d, diff2))
      case Cpy(label, d) => Cpy(label, concat(d, diff2))
    }
  }

  def apply(older: Tree, newer: Tree): Diff =
    apply(List(TreeNode(older)), List(TreeNode(newer)))

  def apply(older: List[MetaTree], newer: List[MetaTree]): Diff = {

    (older, newer) match {
      case (Nil, Nil) =>
        End

      case (Nil, y :: ys ) =>
        // println(s"insert y.label:${y.label} y.fieldChildren:${y.fieldChildren} ys:$ys")
        y.label match {
          case ObjectType(tpe) =>
            val y1@TreeNode(_) = y
            Ins(ValueLabel(y1), apply(Nil, ys))
          case _ =>
            Ins(y.label, apply(Nil, y.fieldChildren ++ ys))
        }

      case (x :: xs, Nil) =>
        // println(s"delete x.label:${x.label} y.fieldChildren:${x.fieldChildren} xs:$xs")
        x.label match {
          case ObjectType(tpe) =>
            val x1@TreeNode(_) = x
            Del(ValueLabel(x1), apply(xs, Nil))
          case _ =>
            Del(x.label, apply(x.fieldChildren ++ xs, Nil))
        }

      case (x :: xs, y :: ys) =>
        def bestDelOrInsapply(xLabel: Label, xRest: List[MetaTree], yLabel: Label, yRest: List[MetaTree]): Diff = {
          val del = x.label match {
            case ObjectType(tpe) =>
              val x1@TreeNode(xx1) = x
              Del(ValueLabel(x1), apply(xs, y :: ys))
            case _ =>
              Del(xLabel, apply(xRest ++ xs, y :: ys))
          }

          val ins = y.label match {
            case ObjectType(tpe) =>
              val y1@TreeNode(yy1) = y
              Ins(ValueLabel(y1), apply(x :: xs, ys))
            case _ =>
              Ins(yLabel, apply(x :: xs, yRest ++ ys))
          }
          // println(s"cpy del:$del ins:$ins del.score:${del.score} ins.score:${ins.score}")

          if(del.score <= ins.score) del else ins
        }


        if(Label.equals(x.label, y.label)) {

          val cpyDiff = x.label match {
            case ObjectType(tpe) =>
              val dxsys = apply(xs, ys)

              val subd = apply(x.fieldChildren, y.fieldChildren)
              // if only CPY & END then we copy the whole tree, no need to diff it
              // println(s"subd:$subd \n score:${subd.score} \n x:$x \n xs:$xs \n----\n")
              if(subd.score == 0) {
                // in this case, we know we have a TreeNode
                val x1@TreeNode(_) = x
                // CpyTree(x1, apply(xs, ys))
                Cpy(ValueLabel(x1), dxsys)
              }
              else //CpySubTree(x.label, subd, dxsys)
                Cpy(x.label, concat(subd, dxsys))
            case _ =>
              // println(s" x:$x \n x.label:${x.label} \n x.fieldChildren:${x.fieldChildren}\n y:$y \n y.label:${y.label}\n y.fieldChildren:${y.fieldChildren}\n xs:$xs ys:$ys \n----\n")
              Cpy(x.label, apply(x.fieldChildren ++ xs, y.fieldChildren ++ ys)) 
          }
          // here we could try to find better solution trying to ins y or delete x
          // but it consumes a lot more so let's test further...
          // val insDiff = Ins(y.label, concat(apply(List(x), y.fieldChildren), dxsys))
          // val delDiff = Del(x.label, concat(apply(x.fieldChildren, List(y)), dxsys))
          // if(delDiff.score <= insDiff.score)
          //   if(cpyDiff.score <= delDiff.score) cpyDiff else delDiff
          // else
          //   if(cpyDiff.score <= insDiff.score) cpyDiff else insDiff
          cpyDiff
        }
        else {
          // here we could be smarter too
          // like 
          bestDelOrInsapply(x.label, x.fieldChildren, y.label, y.fieldChildren)
        }
    }
  }

  def delete(label: Label, xs: List[MetaTree]): PatchError[List[MetaTree]] = {
    // println(s"delete label:$label xs:$xs")
    xs match {
      case Nil =>
        label match {
          case TreeListFieldLabel(n, 0) => Right(TreeListField(n, List()) +: xs)
          case TreeOptionFieldLabel(n, false) => Right(TreeOptionField(n, None) +: xs)
          case _ =>
            // println(s"delete label:$label xs:$xs")
            Left(PatchErrorMsg(s"Can't delete $label: no input trees"))
        }
              
      case x :: xs =>
        label match {
          case ValueLabel(tree) =>
            if(tree == x) Right(xs)
            else Left(PatchErrorMsg(s"Can't delete $label: expected $label, found ${x.label}"))
          case _ => 
            if(Label.equals(x.label, label)) {
              Right(x.fieldChildren ++ xs)
            }
            else {
              // println(s"delete label:$label xs:$xs x:$x xlabel:${x.label}")
              Left(PatchErrorMsg(s"Can't delete $label: expected $label, found ${x.label}"))
            }
        }
    }
  }

  def insert(label: Label, xs: List[MetaTree]): PatchError[(List[MetaTree], MetaTree)] = {
    label match {
      case ValueLabel(tree) => Right((xs, tree))
      case fl: FieldLabel => fl match {
        case SimpleFieldLabel(n) =>
          xs match {
            case TreeNode(x) :: xs => Right((xs, TreeField(n, x)))
            case x :: xs => Left(PatchErrorMsg(s"Can't insert $label: expected TreeNode, found $x"))
            case Nil => Left(PatchErrorMsg(s"Can't insert $label: no input trees"))
          }
        case TreeListFieldLabel(n, sz) =>
          val (xs0, xs1) = xs.splitAt(sz)

          if(xs0.length < sz) Left(PatchErrorMsg(s"Can't insert $label: expected at least $sz trees, got ${xs.length}"))
          else {
            val trees = xs0.collect { case TreeNode(t) => t }
            Right((xs1, TreeListField(n, trees)))
          }
        case TreeListListFieldLabel(n, sz) =>
          val (xs0, xs1) = xs.splitAt(sz)

          if(xs0.length < sz) Left(PatchErrorMsg(s"Can't insert $label: expected at least $sz trees, got ${xs.length}"))
          else {
            val treess = xs0.collect { case TreeListField(_, t) => t }
            Right((xs1, TreeListListField(n, treess)))
          }
        case TreeOptionFieldLabel(n, isDef) =>
          if(isDef) {
            xs match {
              case TreeNode(x) :: xs => Right((xs, TreeOptionField(n, Some(x))))
              case x :: xs => Left(PatchErrorMsg(s"Can't insert $label: expected TreeNode, found $x"))
              case Nil => Left(PatchErrorMsg("Can't insert $label: no input trees"))
            }
          } else Right((xs, TreeOptionField(n, None)))
      }
      case PosLabel(origin) => Right((xs, PosField(origin)))
      case ObjectType(tpe) =>
        MetaTree.rebuildTree(xs)(tpe).map { case (l, tree) => l -> TreeNode(tree) }
        // shouldn't happen
        // Left(PatchErrorMsg(s"Can't insert unexpected $label"))
    }
  }

  def cpySub(label: Label, subd: Diff, xs: List[MetaTree]): PatchError[(List[MetaTree], MetaTree)] = {
    label match {
      case ObjectType(tpe) =>
        // println(s"cpySub($label, subd:$subd, xs:$xs)")
        xs match {
          case x :: xs =>
            if(Label.equals(x.label, label)) {
              for {
                subxs <- patch(subd, x.fieldChildren)
                tree  <- MetaTree.rebuildTree(subxs)(tpe)
              } yield {
                (xs, TreeNode(tree._2))
              }
            }
            else {
              Left(PatchErrorMsg(s"Can't cpySub $label: expected $label, found ${x.label}"))
            }
          case Nil =>
            Left(PatchErrorMsg(s"Can't cpySub $label: no input trees"))
        }
      case l => Left(PatchErrorMsg(s"Can't cpySub $label: unexpected label $l"))
    }
  }

  def patch(diff: Diff, tree: Tree): PatchError[Tree] =
    patch(diff, List(TreeNode(tree))).flatMap {
      case List(TreeNode(tree)) => Right(tree)
      case _ => Left(PatchErrorMsg(s"Can't patch $tree: expected single element result"))
    }

  def patch(diff: Diff, xs: List[MetaTree]): PatchError[List[MetaTree]] = {
    (diff, xs) match {
      case (Ins(label, d), xs) =>
        for {
          xs0 <- patch(d, xs)
          opt <- insert(label, xs0)
        } yield {
          val (xs1, ins) = opt
          ins +: xs1
        }
      
      case (Del(label, d), xs) =>
        // println(s"Del($label, $xs)")
        for {
          xs0 <- delete(label, xs)
          xs1 <- patch(d, xs0)
        } yield (xs1)
              
      case (Cpy(label, d), xs) =>
        // println(s"Cpy(label:$label, xs:$xs)")

        for {
          xs0 <- delete(label, xs)
          xs1 <- patch(d, xs0)
          opt <- insert(label, xs1)
        } yield {
          val (xs2, f) = opt
          (f +: xs2)
        }

      case (End, Nil) => Right(Nil)

      case (End, _) => Left(PatchErrorMsg("still having element in tree but diff has been consumed"))
    }
  }

  def extractSource(diff: Diff, xs: List[MetaTree] = Nil): PatchError[List[MetaTree]] = {
    diff match {
      case End => Right(xs)
      
      case Ins(lbl, d) => 
        extractSource(d, xs).map { dxs => xs ++ dxs }
      
      case Del(lbl, d) =>
        for {
          // first build next parts
          xs1 <- extractSource(d, xs)
          // then insert by consuming what has been built
          res <- insert(lbl, xs1)
          (xs2, x) = res
        } yield {
          x +: xs2
        }

      case Cpy(lbl, d) =>
        for {
          // first build next parts
          xs1 <- extractSource(d, xs)
          res <- insert(lbl, xs1)
        } yield {
          val (xs2, x) = res
          x +: xs2
        }

    }
  }

  def extractTarget(diff: Diff, xs: List[MetaTree] = Nil): PatchError[List[MetaTree]] = {
    diff match {
      case End => Right(xs)

      case Ins(lbl, d) =>
        for {
          // first build next parts
          xs1 <- extractTarget(d, xs)
          // then insert by consuming what has been built
          res <- insert(lbl, xs1)
        } yield {
          val (xs2, x) = res
          x +: xs2
        }

      case Del(lbl, d) =>
        extractTarget(d, xs).map { dxs => xs ++ dxs }

      case Cpy(lbl, d) =>
        for {
          // first build next parts
          xs1 <- extractTarget(d, xs)
          res <- insert(lbl, xs1)
        } yield {
          val (xs2, x) = res
          x +: xs2
        }

    }
  }

  def showInsert(label: Label, xs: List[MetaTree]): PatchError[List[MetaTree]] = {
    xs match {
      case Annotation(x) :: xs => showInsert(label, xs).map { xs => Annotation(x) +: xs }
      case _ =>
        label match {
          case ValueLabel(tree) => Right(tree +: xs)
          case fl: FieldLabel => fl match {
            case SimpleFieldLabel(n) =>
              xs match {
                case TreeNode(x) :: xs => Right(TreeField(n, x) +: xs)
                // case Annotation(x) :: xs => showInsert(label, xs).map { xs => Annotation(x) +: xs }
                case x :: xs => Left(PatchErrorMsg(s"Can't insert $label: expected TreeNode, found $x"))
                case Nil => Left(PatchErrorMsg(s"Can't insert $label: no input trees"))
              }
            case TreeListFieldLabel(n, sz) =>
              val (xs0, xs1) = xs.splitAt(sz)

              if(xs0.length < sz) Left(PatchErrorMsg(s"Can't insert $label: expected at least $sz trees, got ${xs.length}"))
              else {
                val trees = xs0.collect { case TreeNode(t) => t }
                Right(TreeListField(n, trees) +: xs1)
              }
            case TreeListListFieldLabel(n, sz) =>
              val (xs0, xs1) = xs.dropWhile { case Annotation(_) => true; case _ => false }.splitAt(sz)

              if(xs0.length < sz) Left(PatchErrorMsg(s"Can't insert $label: expected at least $sz trees, got ${xs.length}"))
              else {
                val treess = xs0.collect { case TreeListField(_, t) => t }
                Right(TreeListListField(n, treess) +: xs1)
              }
            case TreeOptionFieldLabel(n, isDef) =>
              if(isDef) {
                xs match {
                  case TreeNode(x) :: xs => Right(TreeOptionField(n, Some(x)) +: xs)
                  // case Annotation(x) :: xs => showInsert(label, xs).map { xs => Annotation(x) +: xs }
                  case x :: xs => Left(PatchErrorMsg(s"Can't insert $label: expected TreeNode, found $x"))
                  case Nil => Left(PatchErrorMsg("Can't insert $label: no input trees"))
                }
              } else Right(TreeOptionField(n, None) +: xs)
          }
          case PosLabel(origin) => Right(PosField(origin) +: xs)
          case ObjectType(tpe) =>
            MetaTree.rebuildTree(xs)(tpe).map { case (l, tree) => TreeNode(tree) +: l }
        }
    }
  }

  def showDiff(diff: Diff, xs: List[MetaTree] = Nil): PatchError[(List[MetaTree], String)] = {
    diff match {

      case Cpy(lbl, d) =>
        for {
          xs1 <- showDiff(d, xs)
          (xs2, str) = xs1
          res <- showInsert(lbl, xs2)
        } yield {
          res match {
            case TreeNode(x) :: xs =>              
              res -> str
            case xs =>
              res -> str
          }
        }

      case End => Right((List(), ""))

      case Del(ValueLabel(TreeNode(del)), d@Ins(ValueLabel(TreeNode(ins)), _)) =>
        showDiff(d, xs).map {
          case (xs, str) =>
            xs -> (del.pos + str)
        }

      case Del(_, d) =>
        showDiff(d, xs)

      case Ins(lbl, d) =>
        for {
          xs1 <- showDiff(d, xs)
          (xs2, str) = xs1
          res <- showInsert(lbl, xs2)
        } yield {
          res match {
            case TreeNode(x) :: xs =>              
              res -> str
            case xs =>
              res -> str
          }
        }

    }
  }

}


