package scala.meta

package object diff {
  case class PatchErrorMsg(msg: String) extends RuntimeException(msg)
  type PatchError[A] = Either[PatchErrorMsg, A]
}
