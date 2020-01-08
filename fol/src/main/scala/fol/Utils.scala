package fol

object Utils {
  def randomElem[T](a: Array[T]): T = {
    require(a.length > 0)
    a(util.Random.nextInt(a.length))
  }
}
