package faba.data

import faba.engine.ELattice
import scala.xml.Elem

import org.objectweb.asm.Type
import scala.collection.mutable
import scala.collection.immutable.Iterable

case class Method(internalClassName: String, methodName: String, methodDesc: String) {
  override def toString =
    s"$internalClassName $methodName$methodDesc"

  def internalPackageName =
    internalClassName.lastIndexOf('/') match {
      case -1 => ""
      case i => internalClassName.substring(0, i)
    }
}

sealed trait Direction
case class In(paramIndex: Int) extends Direction
case class InOut(paramIndex: Int, in: Value) extends Direction
case object Out extends Direction

case class Key(method: Method, direction: Direction) {
  override def toString = direction match {
    case Out => s"$method"
    case In(index) => s"$method #$index"
    case InOut(index, _) => s"$method #$index"
  }
}

object Values extends Enumeration {
  val Bot, NotNull, Null, True, False, Top = Value
}

object `package` {
  implicit val lattice = ELattice(Values)
  type Value = Values.Value
}

object XmlUtils {

  def toXmlAnnotations(solutions: Iterable[(Key, Value)]): List[Elem] = {
    var annotations = Map[String, List[Elem]]()
    val inOuts = mutable.HashMap[Method, List[(InOut, Value)]]()
    for ((key, value) <- solutions) {
      key.direction match {
        case In(paramIndex) if value == Values.NotNull =>
          val method = key.method
          annotations = annotations.updated(
            s"${annotationKey(method)} ${paramIndex}",
            List(<annotation name='org.jetbrains.annotations.NotNull'/>)
          )
        case Out if value == Values.NotNull =>
          val method = key.method
          annotations = annotations.updated(
            annotationKey(method),
            List(<annotation name='org.jetbrains.annotations.NotNull'/>)
          )
        case inOut:InOut =>
          inOuts(key.method) = (inOut, value) :: inOuts.getOrElse(key.method, Nil)
        case _ =>

      }
    }
    for ((method, inOuts) <- inOuts) {
      val key = annotationKey(method)
      val arity = Type.getArgumentTypes(method.methodDesc).size
      val contractValues = inOuts.map { case (InOut(i, inValue), outValue) =>
        (0 until arity).map { j =>
          if (i == j) contractValueString(inValue) else "_" }.mkString("", ",", s"->${contractValueString(outValue)}")
      }.mkString("\"", ";", "\"")
      val contractAnnotation =
        <annotation name='org.jetbrains.annotations.Contract'>
          <val val={contractValues}/>
        </annotation>
      annotations = annotations.updated(key, contractAnnotation :: annotations.getOrElse(key, Nil))
    }
    annotations.map {
      case (k, v) => <item name={k}>{v}</item>
    }.toList.sortBy(s => (s \\ "@name").toString())
  }

  def contractValueString(v: Value): String = v match {
    case Values.NotNull => "!null"
    case Values.Null => "null"
    case Values.True => "true"
    case Values.False => "false"
    case _ => sys.error(s"unexpected $v")
  }

  def annotationKey(method: Method): String =
    if (method.methodName == "<init>")
      s"${canonical(method.internalClassName)} ${simpleName(method.internalClassName)}${parameters(method)}"
    else
      s"${canonical(method.internalClassName)} ${returnType(method)} ${method.methodName}${parameters(method)}"


  private def returnType(method: Method): String =
    canonical(Type.getReturnType(method.methodDesc).getClassName)

  def canonical(name: String): String =
    name.replace('/', '.').replace('$', '.')

  private def simpleName(internalName: String): String = {
    val cn = canonical(internalName)
    cn.lastIndexOf('.') match {
      case -1 => cn
      case i => cn.substring(i + 1)
    }
  }

  private def parameters(method: Method): String =
    Type.getArgumentTypes(method.methodDesc).map(t => canonical(t.getClassName)).mkString("(", ", ",")")

}

