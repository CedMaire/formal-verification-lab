import scala.language.experimental.macros

package object fol {

  /** Type of primitive expressions. */
  type Constant = String

  /** Type for identifiers. */
  type Identifier = String

  /** Type for functions. */
  type Function = String

  /** Type for predicates. */
  type Predicate = String

  implicit class FOLQuasiQuoter(val sc: StringContext) {

    object fol {
      def apply(args: Any*): Any = macro parser.Macros.fol_apply
      def unapply(arg: Formula): Option[Any] = macro parser.Macros.fol_unapply
    }

    object expr {
      def apply(args: Any*): Any = macro parser.Macros.expr_apply
      def unapply(arg: Expr): Option[Any] = macro parser.Macros.expr_unapply
    }
  }
}
