package faba.data

import faba.engine.StableAwareId
import org.objectweb.asm.signature.{SignatureVisitor, SignatureReader}
import scala.xml.Elem

import org.objectweb.asm.{Opcodes, Type}
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

case class Key(method: Method, direction: Direction, stable: Boolean) extends StableAwareId[Key] {
  override def toString = direction match {
    case Out => s"$method"
    case In(index) => s"$method #$index"
    case InOut(index, v) => s"$method #$index #$v"
  }

  override def mkUnstable =
    if (!stable) this else Key(method, direction, false)

  override def mkStable =
    if (stable) this else Key(method, direction, true)
}

object Values extends Enumeration {
  val Bot, NotNull, Null, True, False, Pure, LocalEffect, LocalObject, NonLocalObject, Top = Value
}

object `package` {
  type Value = Values.Value
}

case class Annotations(notNulls: Set[Key], contracts: Map[Key, String])

object Utils {

  def toAnnotations(solutions: Iterable[(Key, Value)]): Annotations = {
    val inOuts = mutable.HashMap[Method, List[(InOut, Value)]]()
    var notNulls = Set[Key]()
    var contracts = Map[Key, String]()
    for ((key, value) <- solutions) {
      key.direction match {
        case In(paramIndex) if value == Values.NotNull =>
          notNulls = notNulls + key
        case Out if value == Values.NotNull =>
          notNulls = notNulls + key
        case inOut:InOut =>
          inOuts(key.method) = (inOut, value) :: inOuts.getOrElse(key.method, Nil)
        case _ =>

      }
    }
    for ((method, inOuts) <- inOuts) {
      val key = Key(method, Out, true)
      val arity = Type.getArgumentTypes(method.methodDesc).size
      val contractValues = inOuts.map { case (InOut(i, inValue), outValue) =>
        (0 until arity).map { j =>
          if (i == j) contractValueString(inValue) else "_" }.mkString("", ",", s"->${contractValueString(outValue)}")
      }.sorted.mkString(";")
      contracts = contracts + (key -> contractValues)
    }
    Annotations(notNulls, contracts)
  }

  def contractValueString(v: Value): String = v match {
    case Values.NotNull => "!null"
    case Values.Null => "null"
    case Values.True => "true"
    case Values.False => "false"
    case Values.Bot => "bot"
    case Values.Top => "top"
  }

}

case class MethodExtra(signature: Option[String], access: Int)

object XmlUtils {

  val REGEX_PATTERN = "(?<=[^\\$\\.])\\${1}(?=[^\\$])".r // disallow .$ or $$
  val pureAnnotations = List(<annotation name='org.jetbrains.annotations.Pure'/>)
  val notNullAnn = <annotation name='org.jetbrains.annotations.NotNull'/>

  def toXmlAnnotations(solutions: Iterable[(Key, Value)], pureSolutions: Iterable[(Key, Value)], extras: Map[Method, MethodExtra], debug: Boolean = false): List[Elem] = {
    var annotations = Map[String, List[Elem]]()
    val inOuts = mutable.HashMap[Method, List[(InOut, Value)]]()
    for ((key, value) <- solutions) {
      key.direction match {
        case In(paramIndex) if value == Values.NotNull =>
          val method = key.method
          val aKey = s"${annotationKey(method, extras(method))} $paramIndex"
          val anns = annotations.getOrElse(aKey, Nil)
          annotations = annotations.updated(aKey, (notNullAnn :: anns).sortBy(_.toString()))
        case In(paramIndex) if value == Values.Null =>
          val method = key.method
          val aKey = s"${annotationKey(method, extras(method))} $paramIndex"
          val anns = annotations.getOrElse(aKey, Nil)
          annotations = annotations.updated(
            aKey,
            (<annotation name='org.jetbrains.annotations.Nullable'/> :: anns).sortBy(_.toString())
          )
        case Out if value == Values.NotNull && !debug =>
          val method = key.method
          annotations = annotations.updated(
            annotationKey(method, extras(method)),
            List(<annotation name='org.jetbrains.annotations.NotNull'/>)
          )
        case Out if debug =>
          val method = key.method
          annotations = annotations.updated(
            annotationKey(method, extras(method)),
            List(<annotation name={value.toString.toLowerCase}/>)
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
          if (i == j) Utils.contractValueString(inValue) else "_" }.mkString("", ",", s"->${Utils.contractValueString(outValue)}")
      }.sorted.mkString("\"", ";", "\"")
      val contractAnnotation =
        <annotation name='org.jetbrains.annotations.Contract'>
          <val val={contractValues}/>
        </annotation>
      if (annotations.get(key).isEmpty) {
        annotations = annotations.updated(key, contractAnnotation :: annotations.getOrElse(key, Nil))
      }
    }
    for ((key, value) <- pureSolutions) {
      if (value == Values.Pure) {
        val method = key.method
        val annKey = annotationKey(method, extras(method))
        annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: pureAnnotations)
      }
    }
    annotations.map {
      case (k, v) => <item name={k}>{v}</item>
    }.toList.sortBy(s => (s \\ "@name").toString())
  }

  // the main logic to interact with IDEA
  def annotationKey(method: Method, extra: MethodExtra): String =
    if (method.methodName == "<init>")
      s"${internalName2Idea(method.internalClassName)} ${simpleName(method.internalClassName)}${parameters(method, extra)}"
    else
      s"${internalName2Idea(method.internalClassName)} ${returnType(method, extra)} ${method.methodName}${parameters(method, extra)}"

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
        binaryName2Idea(Type.getReturnType(method.methodDesc).getClassName)
    }

  private def simpleName(internalName: String): String = {
    val ideaName = internalName2Idea(internalName)
    ideaName.lastIndexOf('.') match {
      case -1 => ideaName
      case i => ideaName.substring(i + 1)
    }
  }

  private def parameters(method: Method, extra: MethodExtra): String = {
    val result = extra.signature match {
      // RetentionPolicy enum has wrong signature - workaround for it
      case Some(sig) if !sig.startsWith("()") =>
        val renderer = new GenericMethodParametersRenderer()
        new SignatureReader(sig).accept(renderer)
        renderer.parameters()
      case _ =>
        Type.getArgumentTypes(method.methodDesc).map(t => binaryName2Idea(t.getClassName)).mkString("(", ", ", ")")
    }
    if ((extra.access & Opcodes.ACC_VARARGS) != 0) result.replace("[])", "...)")
    else result
  }

  private def internalName2Idea(internalName: String): String = {
    val binaryName = Type.getObjectType(internalName).getClassName
    if (binaryName.indexOf('$') >= 0) {
      REGEX_PATTERN.replaceAllIn(binaryName, "\\.")
    } else {
      binaryName
    }
  }

  // class FQN as it rendered by IDEA in external annotations
  private def binaryName2Idea(binaryName: String): String = {
    if (binaryName.indexOf('$') >= 0) {
      REGEX_PATTERN.replaceAllIn(binaryName, "\\.")
    } else {
      binaryName
    }
  }

  class GenericMethodParametersRenderer extends SignatureVisitor(Opcodes.ASM5) {
    private val sb = new StringBuilder("(")
    private var first = true

    def parameters(): String = sb.append(')').toString

    override def visitParameterType(): SignatureVisitor = {
      if (first) first = false // "(" is already appended
      else sb.append(", ")
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
      else false

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

    protected def endType() = ()

    override def visitBaseType(descriptor: Char) {
      sb.append(Type.getType(descriptor.toString).getClassName)
      endType()
    }

    override def visitTypeVariable(name: String) {
      sb.append(name)
      endType()
    }

    override def visitArrayType(): SignatureVisitor =
      new GenericTypeRenderer(sb) {
        override def endType() =
          sb.append("[]")
      }

    override def visitClassType(name: String) =
      sb.append(internalName2Idea(name))

    override def visitInnerClassType(name: String) {
      closeAngleBracketIfNeeded()
      sb.append(".").append(internalName2Idea(name))
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
