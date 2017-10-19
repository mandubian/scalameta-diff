package scala.meta
package diff

sealed trait MemoDiff {
  def diff: Diff
}
final case class EmptyMD(
  override val diff: Diff
) extends MemoDiff

final case class NoSrcMD(
    target: Label
  , override val diff: Diff
  , targetFieldsNext: MemoDiff
) extends MemoDiff

final case class NoTargetMD(
    src: Label
  , override val diff: Diff
  , srcFieldsNext: MemoDiff
) extends MemoDiff

final case class SrcTargetMD(
    src: Label, target: Label
  , override val diff: Diff
  , srcTargetFieldsNext: MemoDiff
  , srcFieldsTargetNext: MemoDiff
  , srcFieldsTargetFieldsNext: MemoDiff
) extends MemoDiff


object MemoDiff {

  private def extendWithSrcLabel(src: Label, d: MemoDiff): MemoDiff = {
    d match {
      case EmptyMD(_) =>
        NoTargetMD(src, Del(src, d.diff), d)

      case NoTargetMD(_, _, _) =>
        NoTargetMD(src, Del(src, d.diff), d)

      case NoSrcMD(y, diff, c) =>
        val i = extendWithSrcLabel(src, c)
        SrcTargetMD(src, y, Ins(src, c.diff), i, d, c)

      case SrcTargetMD(x, y, diff, c, _, _) =>
        val i = extendWithSrcLabel(src, c)
        SrcTargetMD(src, y, best(src, y, i, d, c), i, d, c)

    }
  }

  private def extendWithTargetLabel(target: Label, i: MemoDiff): MemoDiff = {
    i match {
      case EmptyMD(_) =>
        NoSrcMD(target, Ins(target, i.diff), i)

      case NoSrcMD(_, _, _) =>
        NoSrcMD(target, Ins(target, i.diff), i)

      case NoTargetMD(x, diff, c) =>
        val d = extendWithTargetLabel(target, c)
        SrcTargetMD(x, target, best(x, target, i, d, c), i, d, c)

      case SrcTargetMD(x, y, diff, _, c, _) =>
        val d = extendWithTargetLabel(target, c)
        SrcTargetMD(x, target, best(x, target, i, d, c), i, d, c)

    }
  }

  private def best(x: Label, y: Label, i: MemoDiff, d: MemoDiff, c: MemoDiff): Diff = {
    if(Label.equals(x, y)) {
      Cpy(x, c.diff)
    } else {
      val del = Del(x, d.diff)
      val ins = Ins(y, i.diff)

      if(del.score <= ins.score) del else ins         
    }
  }

  def apply(older: Tree, newer: Tree): MemoDiff =
    apply(List(TreeNode(older)), List(TreeNode(newer)))


  def apply(older: List[MetaTree], newer: List[MetaTree]): MemoDiff = {
    (older, newer) match {
      case (Nil, Nil) =>
        EmptyMD(End)

      case (Nil, y :: ys) =>
        val d = apply(Nil, y.fieldChildren ++ ys)
        NoSrcMD(y.label, Ins(y.label, d.diff), d)

      case (x :: xs, Nil) =>
        val d = apply(x.fieldChildren ++ xs, Nil)
        NoTargetMD(x.label, Del(x.label, d.diff), d)

      case (x :: xs, y :: ys) =>
        if(Label.equals(x.label, y.label)) {
          x.label match {
            case ObjectType(tpe) =>
              val c = apply(xs, ys)

              val subd = Diff(x.fieldChildren, y.fieldChildren)
              // if only CPY & END then we copy the whole tree, no need to diff it
              val b = if(subd.score == 0) {
                // in this case, we know we have a TreeNode
                val x1@TreeNode(_) = x
                // CpyTree(x1, diff(xs, ys))
                Cpy(ValueLabel(x1), c.diff)
              }
              else //CpySubTree(x.label, subd, c.diff)
                Cpy(x.label, Diff.concat(subd, c.diff))

              val i = extendWithSrcLabel(x.label, c)
              val d = extendWithTargetLabel(y.label, c)
              // val b = best(x.label, y.label, i, d, c)
              SrcTargetMD(x.label, y.label, b, i, d, c)

            case _ =>
              val c = apply(x.fieldChildren ++ xs, y.fieldChildren ++ ys)
              val i = extendWithSrcLabel(x.label, c)
              val d = extendWithTargetLabel(y.label, c)
              // val b = best(x.label, y.label, i, d, c)
              val b = Cpy(x.label, c.diff)
              SrcTargetMD(x.label, y.label, b, i, d, c)
          }
        }
        else {
          (x.label, y.label) match {
            case (ObjectType(tpe), ObjectType(tpe2)) =>
              val x1@TreeNode(_) = x
              val xLabel = ValueLabel(x1)
              val y1@TreeNode(_) = y
              val yLabel = ValueLabel(y1)
              val c = apply(xs, ys)
              val i = extendWithSrcLabel(xLabel, c)
              val d = extendWithTargetLabel(yLabel, c)

              val b = best(xLabel, yLabel, i, d, c)
              SrcTargetMD(xLabel, yLabel, b, i, d, c)
              // val d = apply(xs, y :: ys)
              // val del = Del(ValueLabel(x1), d.diff)

              // val i = apply(x :: xs, ys)
              // val ins = Ins(y, i.diff)

            case (ObjectType(tpe), _) =>
              val x1@TreeNode(_) = x
              val xLabel = ValueLabel(x1)
              val c = apply(xs, y.fieldChildren ++ ys)
              val i = extendWithSrcLabel(xLabel, c)
              val d = extendWithTargetLabel(y.label, c)

              val b = best(xLabel, y.label, i, d, c)
              SrcTargetMD(xLabel, y.label, b, i, d, c)

            case (_, ObjectType(tpe)) =>
              val y1@TreeNode(_) = x
              val yLabel = ValueLabel(y1)
              val c = apply(x.fieldChildren ++ xs, ys)
              val i = extendWithSrcLabel(x.label, c)
              val d = extendWithTargetLabel(yLabel, c)

              val b = best(x.label, yLabel, i, d, c)
              SrcTargetMD(x.label, yLabel, b, i, d, c)

            case _ =>
              val c = apply(x.fieldChildren ++ xs, y.fieldChildren ++ ys)
              val i = extendWithSrcLabel(x.label, c)
              val d = extendWithTargetLabel(y.label, c)
              val b = best(x.label, y.label, i, d, c)
              SrcTargetMD(x.label, y.label, b, i, d, c)
          }
        }
    }
  }


}