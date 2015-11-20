package faba.data

import faba.asm.PurityAnalysis
import faba.engine.{Negator, IKey}
import org.objectweb.asm.signature.{SignatureVisitor, SignatureReader}
import scala.collection.mutable.ListBuffer
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

case class Key(method: Method, direction: Direction, stable: Boolean, negated: Boolean = false) extends IKey[Key] {
  override def toString = direction match {
    case Out => s"$method"
    case In(index) => s"$method #$index"
    case InOut(index, v) => s"$method #$index #$v"
  }

  override def mkUnstable =
    if (!stable) this else Key(method, direction, false)

  override def mkStable =
    if (stable) this else Key(method, direction, true)

  override def negate: Key = Key(method, direction, stable, true)
}

object Values extends Enumeration {
  // current hack for advanced equations (see purity.scala)
  // ThisObject, LocalObject, NonLocalObjects - receivers
  // ThisObject - this
  // LocalObject - object created in this method (method being analyzed)
  // NonLocalObject - we do not know about origins
  val Bot, NotNull, Null, True, False, Top = Value
}

object ValuesNegator extends Negator[Value] {
  override def negate(v: Value): Value = v match {
    case Values.True => Values.False
    case Values.False => Values.True
    case x => x
  }
}

object `package` {
  type Value = Values.Value
}

case class Annotations(notNulls: Set[Key], contracts: Map[Key, String], effects: Map[Key, Set[PurityAnalysis.EffectQuantum]])

object Utils {

  def toAnnotations(solutions: Iterable[(Key, Value)], effects: Map[Key, Set[PurityAnalysis.EffectQuantum]]): Annotations = {
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

    Annotations(notNulls, contracts, effects)
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
  val nullableResultAnnotations = List(<annotation name='org.jetbrains.annotations.Nullable'/>)
  val notNullResultAnnotations = List(<annotation name='org.jetbrains.annotations.NotNull'/>)
  val localAnnotations = List(<annotation name='org.jetbrains.annotations.LocalEffect'/>)
  val notNullAnn = <annotation name='org.jetbrains.annotations.NotNull'/>

  // intermediate data structure to serialize @Contract annotations
  class Contract {
    var pure = false
    var clauses = ListBuffer[(InOut, Value)]()
  }

  def toXmlAnnotations(solutions: Iterable[(Key, Value)],
                       nullableResults: Iterable[(Key, Value)],
                       pureSolutions: Iterable[(Key, Set[PurityAnalysis.EffectQuantum])],
                       extras: Map[Method, MethodExtra],
                       knownClasses: Set[String],
                       debug: Boolean = false): List[Elem] = {
    var annotations = Map[String, List[Elem]]()
    var notNullResults: Set[String] = Set()

    // preparations for contracts
    val contracts = mutable.HashMap[Method, Contract]()

    for {
      (key, value) <- solutions
      annKey <- annotationKey(key.method, extras(key.method), knownClasses)
    } {

      key.direction match {
        case In(paramIndex) if value == Values.NotNull =>
          val method = key.method
          val aKey = s"$annKey $paramIndex"
          val anns = annotations.getOrElse(aKey, Nil)
          annotations = annotations.updated(aKey, (notNullAnn :: anns).sortBy(_.toString()))
        case In(paramIndex) if value == Values.Null =>
          val method = key.method
          val aKey = s"$annKey $paramIndex"
          val anns = annotations.getOrElse(aKey, Nil)
          annotations = annotations.updated(
            aKey,
            (<annotation name='org.jetbrains.annotations.Nullable'/> :: anns).sortBy(_.toString())
          )
        case Out if value == Values.NotNull && !debug =>
          notNullResults = notNullResults + annKey
        case Out if debug =>
          val method = key.method
          annotations = annotations.updated(
            annKey,
            List(<annotation name={value.toString.toLowerCase}/>)
          )
        case inOut:InOut =>
          if (!contracts.contains(key.method)) {
            contracts(key.method) = new Contract()
          }
          contracts(key.method).clauses += (inOut -> value)
        case _ =>

      }
    }

    // processing purity
    for ((key, value) <- pureSolutions) {
      // pure
      if (value == Set()) {
        if (!contracts.contains(key.method)) {
          contracts(key.method) = new Contract()
        }
        contracts(key.method).pure = true
      }
      var paramsChanged: List[Int] = Nil
      for (effect <- value) {
        effect match {
          case PurityAnalysis.ThisChangeQuantum =>
            val method = key.method
            for (annKey <- annotationKey(method, extras(method), knownClasses)) {
              annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: localAnnotations)
            }
          case PurityAnalysis.ParamChangeQuantum(n) =>
            paramsChanged = n :: paramsChanged
          case _ =>

        }
      }
      if (paramsChanged.nonEmpty) {
        val paramsChangedStr = paramsChanged.sorted.mkString(",")
        val method = key.method
        for (annKey <- annotationKey(method, extras(method), knownClasses)) {
          val paramsAnnotations = List(<annotation name='org.jetbrains.annotations.ParamChange' params={paramsChangedStr}/>)
          annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: paramsAnnotations)
        }
      }
    }

    // merging contracts and purity
    for {
      (method, contract) <- contracts
      annKey <- annotationKey(method, extras(method), knownClasses)
    } {
      val arity = Type.getArgumentTypes(method.methodDesc).size

      val contractValues: Option[String] =
        if (!notNullResults(annKey) && contract.clauses.nonEmpty)
          // to this moment `annotations` contains only @NotNull methods (for this key)
          // if @NotNull is already inferred, we do not output @Contract clauses
          // (but we may output @Contract(pure=true) part of contract annotation)
          Some(contract.clauses.map { case (InOut(i, inValue), outValue) =>
            (0 until arity).map { j =>
              if (i == j) Utils.contractValueString(inValue) else "_" }.mkString("", ",", s"->${Utils.contractValueString(outValue)}")
          }.sorted.mkString("\"", ";", "\""))
        else None

      val pure = contract.pure

      val contractAnnotation: Option[Elem] = (contractValues, pure) match {
        case (Some(values), false) =>
          Some(<annotation name='org.jetbrains.annotations.Contract'>
            <val val={values}/>
          </annotation>)
        case (Some(values), true) =>
          Some(<annotation name='org.jetbrains.annotations.Contract'>
            <val name="value" val={values}/>
            <val name="pure" val="true"/>
          </annotation>)
        case (None, true) =>
          Some(<annotation name='org.jetbrains.annotations.Contract'>
            <val name="pure" val="true"/>
          </annotation>)
        case (_, _) =>
          None
      }

      contractAnnotation.foreach { ann =>
        annotations = annotations.updated(annKey, ann :: annotations.getOrElse(annKey, Nil))
      }

    }

    for {
      (key, value) <- nullableResults
      annKey <- annotationKey(key.method, extras(key.method), knownClasses)
    } {
      annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: nullableResultAnnotations)
    }

    for (annKey <- notNullResults) {
      annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: notNullResultAnnotations)
    }

    val keys = annotations.keys.toList.sorted

    keys.map {
      k => <item name={k}>{annotations(k)}</item>
    }
  }

  def fullMethod(method: Method, knownClasses: Set[String], extra: MethodExtra): Boolean = {
    isKnowType(Type.getReturnType(method.methodDesc), knownClasses) &&
      Type.getArgumentTypes(method.methodDesc).forall(isKnowType(_, knownClasses)) &&
      (extra.access & Opcodes.ACC_SYNTHETIC) == 0 &&
      isGoodName(method.internalClassName)
  }

  def isGoodName(internalClassName: String): Boolean = {
    val qn = internalName2Idea(internalClassName)
    val parts = qn.split('.')
    !parts.exists(s => s.forall(Character.isDigit))
  }

  def isKnowType(tp: Type, knownClasses: Set[String]): Boolean =
    tp.getSort match {
      case Type.ARRAY =>
        isKnowType(tp.getElementType, knownClasses)
      case Type.OBJECT =>
        knownClasses(tp.getInternalName)
      case _ =>
        true
    }

  // the main logic to interact with IDEA
  def annotationKey(method: Method, extra: MethodExtra, knownClasses: Set[String]): Option[String] =
    if (!fullMethod(method, knownClasses, extra))
      None
    else if (method.methodName == "<init>")
      Some(s"${internalName2Idea(method.internalClassName)} ${simpleName(method.internalClassName)}${parameters(method, extra)}")
    else
      Some(s"${internalName2Idea(method.internalClassName)} ${returnType(method, extra)} ${method.methodName}${parameters(method, extra)}")

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
        tp2Idea(Type.getReturnType(method.methodDesc))
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
        Type.getArgumentTypes(method.methodDesc).map(t => tp2Idea(t)).mkString("(", ", ", ")")
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
  private def tp2Idea(tp: Type): String = {
    val binaryName = tp.getClassName
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
