package faba.data

import faba.engine.ELattice
import scala.xml.Elem

import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.signature.{SignatureReader, SignatureVisitor}
import scala.collection.mutable
import scala.collection.immutable.Iterable

case class MethodExtra(signature: Option[String], access: Int)

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

  def toXmlAnnotations(solutions: Iterable[(Key, Value)], extras: Map[Method, MethodExtra]): List[Elem] = {
    var annotations = Map[String, List[Elem]]()
    val inOuts = mutable.HashMap[Method, List[(InOut, Value)]]()
    for ((key, value) <- solutions) {
      key.direction match {
        case In(paramIndex) if value == Values.NotNull =>
          val method = key.method
          val extra = extras(method)
          annotations = annotations.updated(
            s"${annotationKey(method, extra)} ${paramIndex}",
            List(<annotation name='org.jetbrains.annotations.NotNull'/>)
          )
        case Out if value == Values.NotNull =>
          val method = key.method
          val extra = extras(method)
          annotations = annotations.updated(
            annotationKey(method, extra),
            List(<annotation name='org.jetbrains.annotations.NotNull'/>)
          )
        case inOut:InOut =>
          inOuts(key.method) = (inOut, value) :: inOuts.getOrElse(key.method, Nil)
        case _ =>

      }
    }
    for ((method, inOuts) <- inOuts) {
      val key = annotationKey(method, extras(method))
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

  def annotationKey(method: Method, extra: MethodExtra): String =
    if (method.methodName == "<init>")
      s"${canonical(method.internalClassName)} ${simpleName(method.internalClassName)}${parameters(method, extra)}"
    else
      s"${canonical(method.internalClassName)} ${returnType(method, extra)} ${method.methodName}${parameters(method, extra)}"


  private def returnType(method: Method, extra: MethodExtra): String =
    extra.signature match {
      case Some(sig) =>
        val sb = new StringBuilder()
        new SignatureReader(sig).accept(new SignatureVisitor(Opcodes.ASM5) {
          override def visitReturnType(): SignatureVisitor =
            new GenericTypeRenderer(sb)
        })
        sb.toString()
      case None =>
        canonical(Type.getReturnType(method.methodDesc).getClassName)
    }


  def canonical(name: String): String =
    name.replace('/', '.').replace('$', '.')

  private def simpleName(internalName: String): String = {
    val cn = canonical(internalName)
    cn.lastIndexOf('.') match {
      case -1 => cn
      case i => cn.substring(i + 1)
    }
  }

  private def parameters(method: Method, extra: MethodExtra): String = {
    extra.signature match {
      case Some(sig) =>
        val renderer = new GenericMethodParametersRenderer()
        new SignatureReader(sig).accept(renderer)
        renderer.parameters()
      case None =>
        val argTypes = Type.getArgumentTypes(method.methodDesc)
        argTypes.map(t => canonical(t.getClassName)).mkString("(", ", ",")")
    }
  }

  class GenericMethodParametersRenderer extends SignatureVisitor(Opcodes.ASM5) {

    private val sb = new StringBuilder("(")
    private var first = true

    def parameters(): String = sb.append(')').toString

    override def visitParameterType(): SignatureVisitor = {
      if (first) {
        first = false
        // "(" is already appended
      }
      else {
        sb.append(", ")
      }
      new GenericTypeRenderer(sb)
    }
  }

  class GenericTypeRenderer(val sb: StringBuilder) extends SignatureVisitor(Opcodes.ASM5) {
    private var angleBracketOpen = false

    private def openAngleBracketIfNeeded(): Boolean =
      if (!angleBracketOpen) {
        angleBracketOpen = true
        sb.append("<")
        true
      }
      else
        false

    private def closeAngleBracketIfNeeded() {
      if (angleBracketOpen) {
        angleBracketOpen = false
        sb.append(">")
      }
    }

    private def beforeTypeArgument() {
      val first = openAngleBracketIfNeeded()
      if (!first) sb.append(",")
    }

    protected def endType() {

    }

    override def visitBaseType(descriptor: Char) {
      sb.append(descriptor match {
        case 'V' => "void"
        case 'B' => "byte"
        case 'J' => "long"
        case 'Z' => "boolean"
        case 'I' => "int"
        case 'S' => "short"
        case 'C' => "char"
        case 'F' => "float"
        case 'D' => "double"
        case _ => sys.error(s"Unknown base type: $descriptor")
      })
      endType()
    }

    override def visitTypeVariable(name: String) {
      sb.append(name)
      endType()
    }

    override def visitArrayType(): SignatureVisitor =
      new GenericTypeRenderer(sb) {
        override def endType() {
          sb.append("[]")
        }
      }

    override def visitClassType(name: String) {
      sb.append(XmlUtils.canonical(name))
    }

    override def visitInnerClassType(name: String) {
      closeAngleBracketIfNeeded()
      sb.append(".").append(XmlUtils.canonical(name))
    }

    override def visitTypeArgument() {
      beforeTypeArgument()
      sb.append("?")
    }

    override def visitTypeArgument(wildcard: Char): SignatureVisitor = {
      beforeTypeArgument()
      wildcard match {
        case SignatureVisitor.EXTENDS => sb.append("? extends ")
        case SignatureVisitor.SUPER => sb.append("? super ")
        case SignatureVisitor.INSTANCEOF =>
        case _ => sys.error(s"Unknown wildcard: $wildcard")
      }
      new GenericTypeRenderer(sb)
    }

    override def visitEnd() {
      closeAngleBracketIfNeeded()
      endType()
    }
  }
}

