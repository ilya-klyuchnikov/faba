package faba.data

import org.objectweb.asm.signature.{SignatureReader, SignatureVisitor}
import org.objectweb.asm.{Opcodes, Type}

import scala.collection.immutable.Iterable
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.xml.Elem

/**
 * Case class to uniquely identify java methods in bytecode (part of `faba.data.Key`)
 *
 * @param internalClassName the name of the class owning this method in asm format
 *                          (org.objectweb.asm.tree.ClassNode#name)
 * @param methodName method name (org.objectweb.asm.tree.MethodNode#name)
 * @param methodDesc method descriptor in asm format (see org.objectweb.asm.tree.MethodNode#desc)
 */
case class Method(internalClassName: String, methodName: String, methodDesc: String) {
  override def toString =
    s"$internalClassName $methodName$methodDesc"

  def internalPackageName =
    internalClassName.lastIndexOf('/') match {
      case -1 => ""
      case i => internalClassName.substring(0, i)
    }
}

/**
 * Information about method for inference with hierarchy.
 * Fields are in the same order as in `org.objectweb.asm.tree.ClassNode`
 * and `org.objectweb.asm.tree.MethodNode`
 *
 * @param classAccess  (org.objectweb.asm.tree.ClassNode#access)
 * @param className    (org.objectweb.asm.tree.ClassNode#name)
 * @param superName    (org.objectweb.asm.tree.ClassNode#superName)
 * @param interfaces   (org.objectweb.asm.tree.ClassNode#interfaces)
 * @param methodAccess (org.objectweb.asm.tree.MethodNode#access)
 * @param methodName   (org.objectweb.asm.tree.MethodNode#name)
 * @param methodDesc   (org.objectweb.asm.tree.MethodNode#desc)
 *
 */
case class MethodCoordinates(classAccess: Int,
                             className: String,
                             superName: String,
                             interfaces: List[String],
                             methodAccess: Int,
                             methodName: String,
                             methodDesc: String)

/**
 * Additional information about method. Used for dumping inferred annotations into
 * IDEA external annotations format.
 * @param signature corresponds to `org.objectweb.asm.tree.MethodNode#signature`
 * @param access corresponds to `org.objectweb.asm.tree.MethodNode#access`
 */
case class MethodExtra(signature: Option[String], access: Int)

/**
 * Direction of analysis (part of `faba.data.Key`)
 */
sealed trait Direction
/**
 * `In(i)` direction of analysis = analysis of the i-th parameter (for `@NotNull` and `@Nullable`).
 * @param paramIndex index of a parameter being analyzed.
 */
case class In(paramIndex: Int) extends Direction

/**
 * `Out` direction of analysis = analysis of the method's result (`@NotNull`, `@Nullable` or pure).
 */
case object Out extends Direction

/**
 * `InOut(i, v)` = analysis of the method's result assuming that a value `v` is passed into the i-th parameter.
 * Used for denoting inference of `@Contract` clauses. For example, for method `Object foo(Object o1, Object o2)`
 * inference of the clause `@Contract("null,_->null")` will use `InOut(0, Values.Null)` direction.
 * @param paramIndex index of a parameter in question
 * @param in value passed into this parameter
 */
case class InOut(paramIndex: Int, in: Value) extends Direction

/**
 * Trait to abstract `stable` aspect of `faba.data.Key`.
 * Because of `PolymorphicId`, `faba.engine.Solver` is quite generic (knows nothing about `faba.data.Key`).
 *
 * @tparam Id id of an entity
 * @see [[faba.data.Key#stable]]
 */
trait PolymorphicId[Id] {
  /**
   * Whether this id stable (= effectively final).
   */
  val stable: Boolean

  /**
   * Converts current id into a stable one.
   * @return unstable id
   */
  def mkUnstable: Id

  /**
   * Converts current id into a unstable one.
   * @return stable id
   */
  def mkStable: Id
}

/**
 * Analysis key. Used to uniquely identify ids (variables) in equations.
 * @note `NotNull`, `Nullable` and purity result analyses will have the same key for the same method.
 *       `NotNull` and `Nullable` parameter analyses will have the same key for the same method.
 *       However, this is not a problem since `NotNull` and `Nullable` equations are put into different solvers.
 *       It is possible, that later key will be extended with "analysis coordinate" as well (as in IDEA).
 *
 * @param method method id (method coordinate)
 * @param direction direction coordinate
 * @param stable stability coordinate (virtual/final method).
 *               `stable` flag is used at declaration site and call site.
 *               `stable=true` at declaration site means that a method is effectively final.
 *               `stable=true` at call site means that a call to this method is not virtual.
 */
case class Key(method: Method, direction: Direction, stable: Boolean) extends PolymorphicId[Key] {
  override def toString = direction match {
    case Out => s"$method"
    case In(index) => s"$method #$index"
    case InOut(index, v) => s"$method #$index #$v"
  }

  override def mkUnstable =
    if (!stable) this else Key(method, direction, stable = false)

  override def mkStable =
    if (stable) this else Key(method, direction, stable = true)
}

/**
 * Enumeration to represent abstract values for result of analyses.
 * Interpretation of these values may be specific to an analysis.
 */
object Values extends Enumeration {
  val Bot, NotNull, Null, True, False, Pure, Top = Value
}

object `package` {
  type Value = Values.Value
  /**
   * To limit long analysis by the number of elementary operations.
   */
  val stepsLimit = 1 << 15
}

/**
 * Exception is thrown when analysis is trying to perform
 * more elementary steps then [[faba.data.LimitReachedException#limit]].
 */
class LimitReachedException extends Exception("Limit reached exception")

/**
 * Auxiliary data structure to support testing.
 * @param notNulls keys of methods and parameters inferred to be `@NotNull`
 * @param contracts map of `methodKey->contractString`
 */
case class Annotations(notNulls: Set[Key], nullable: Set[Key], contracts: Map[Key, String])

/**
 * Utility to transform solutions into annotations.
 */
object AnnotationsUtil {

  def toAnnotations(solutions: Iterable[(Key, Value)], nullableParams: Set[Key]): Annotations = {
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
      val key = Key(method, Out, stable = true)
      val arity = Type.getArgumentTypes(method.methodDesc).size
      val contractValues = inOuts.map { case (InOut(i, inValue), outValue) =>
        (0 until arity).map { j =>
          if (i == j) contractValueString(inValue) else "_" }.mkString("", ",", s"->${contractValueString(outValue)}")
      }.sorted.mkString(";")
      contracts = contracts + (key -> contractValues)
    }

    Annotations(notNulls, nullableParams, contracts)
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

/**
 * Utility to dump solutions of equations in the format of IDEA external annotations.
 */
object XmlUtils {

  val REGEX_PATTERN = "(?<=[^\\$\\.])\\${1}(?=[^\\$])".r // disallow .$ or $$
  val nullableResultAnnotations = List(<annotation name='org.jetbrains.annotations.Nullable'/>)
  val notNullAnn = <annotation name='org.jetbrains.annotations.NotNull'/>

  // intermediate data structure to serialize @Contract annotations
  class Contract {
    var pure = false
    var clauses = ListBuffer[(InOut, Value)]()
  }

  def toXmlAnnotations(solutions: Iterable[(Key, Value)],
                       nullableResults: Iterable[(Key, Value)],
                       pureSolutions: Iterable[(Key, Value)],
                       extras: Map[Method, MethodExtra],
                       debug: Boolean = false): List[Elem] = {
    var annotations = Map[String, List[Elem]]()

    // preparations for contracts
    val contracts = mutable.HashMap[Method, Contract]()

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
          if (!contracts.contains(key.method)) {
            contracts(key.method) = new Contract()
          }
          contracts(key.method).clauses += (inOut -> value)
        case _ =>

      }
    }

    // processing purity
    for ((key, value) <- pureSolutions) {
      if (value == Values.Pure) {
        if (!contracts.contains(key.method)) {
          contracts(key.method) = new Contract()
        }
        contracts(key.method).pure = true
      }
    }

    // merging contracts and purity
    for ((method, contract) <- contracts) {
      val key = annotationKey(method, extras(method))
      val arity = Type.getArgumentTypes(method.methodDesc).size

      val contractValues: Option[String] =
        if (annotations.get(key).isEmpty && contract.clauses.nonEmpty)
          // to this moment `annotations` contains only @NotNull methods (for this key)
          // if @NotNull is already inferred, we do not output @Contract clauses
          // (but we may output @Contract(pure=true) part of contract annotation)
          Some(contract.clauses.map { case (InOut(i, inValue), outValue) =>
            (0 until arity).map { j =>
              if (i == j) AnnotationsUtil.contractValueString(inValue) else "_" }.mkString("", ",", s"->${AnnotationsUtil.contractValueString(outValue)}")
          }.sorted.mkString("\"", ";", "\""))
        else None

      val pure = contract.pure

      val contractString: Option[String] = (contractValues, pure) match {
        case (Some(values), false) =>
          Some(values)
        case (Some(values), true) =>
          Some(s"value=$values,pure=true")
        case (None, true) =>
          Some("pure=true")
        case (_, _) =>
          None
      }

      val contractAnnotation = contractString.map { values =>
        <annotation name='org.jetbrains.annotations.Contract'>
          <val val={values}/>
        </annotation>
      }

      contractAnnotation.foreach { ann =>
        annotations = annotations.updated(key, ann :: annotations.getOrElse(key, Nil))
      }

    }

    for ((key, value) <- nullableResults) {
      val method = key.method
      val annKey = annotationKey(method, extras(method))
      annotations = annotations.updated(annKey, annotations.getOrElse(annKey, Nil) ::: nullableResultAnnotations)
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
