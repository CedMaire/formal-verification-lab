package fol

import scallion.input.Positioner

package object parser {
  sealed trait Position
  case object NoPosition extends Position
  case class InPart(part: Int, index: Int, line: Int, column: Int)
      extends Position

  class PartPositioner(part: Int) extends Positioner[Char, Position] {
    override val start: Position = InPart(part, 0, 1, 1)
    override def increment(pos: Position, chr: Char): Position = pos match {
      case NoPosition => NoPosition
      case InPart(p, i, l, c) =>
        if (chr == '\n') {
          InPart(p, i + 1, l + 1, 1)
        } else {
          InPart(p, i + 1, l, c + 1)
        }
    }
  }
}
