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

  val resolveDirection: ResolveDirection.Value

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

object ResolveDirection extends Enumeration {
  // INVOKESTATIC, INVOKESPECIAL
  val Upward = Value
  // INVOKEINTERFACE, INVOKEVIRTUAL
  val Downward = Value
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
 * @param resolveDirection stability coordinate (virtual/final method).
 */
case class Key(method: Method, direction: Direction, resolveDirection: ResolveDirection.Value) extends PolymorphicId[Key] {
  val stable =
    resolveDirection == ResolveDirection.Upward

  override def toString = direction match {
    case Out => s"$method"
    case In(index) => s"$method #$index"
    case InOut(index, v) => s"$method #$index #$v"
  }

  // TODO - more clear name like "changeDirection"
  override def mkUnstable =
    Key(method, direction, resolveDirection = ResolveDirection.Downward)

  // TODO - more clear name like "changeDirection"
  override def mkStable =
    Key(method, direction, resolveDirection = ResolveDirection.Upward)
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
 * Auxiliary data structure to have an explicit result of inference.
 * Fields are self-explaining.
 */
case class InferenceResult(
  notNullParameters: Set[Key],
  nullableParameters: Set[Key],
  notNullMethods: Set[Key],
  nullableMethods: Set[Key],
  pureMethods: Set[Key],
  contractClauses: Map[Key, Value]
) {
  def byPackage(): Map[String, InferenceResult] = {

    val notNullParametersByPackage =
      notNullParameters.groupBy(k => k.method.internalPackageName)
    val nullableParametersByPackage =
      nullableParameters.groupBy(k => k.method.internalPackageName)
    val notNullMethodsByPackage =
      notNullMethods.groupBy(k => k.method.internalPackageName)
    val nullableMethodsByPackage =
      nullableMethods.groupBy(k => k.method.internalPackageName)
    val pureMethodsByPackage =
      pureMethods.groupBy(k => k.method.internalPackageName)
    val contractClausesByPackage =
      contractClauses.groupBy(kv => kv._1.method.internalPackageName)

    val allPackages =
      notNullParametersByPackage.keySet ++
      nullableParametersByPackage.keySet ++
      notNullMethodsByPackage.keySet ++
      nullableMethodsByPackage.keySet ++
      pureMethodsByPackage.keySet ++
      contractClausesByPackage.keySet

    allPackages.iterator.map { pkg =>
      pkg -> InferenceResult(
        notNullParametersByPackage.getOrElse(pkg, Set()),
        nullableParametersByPackage.getOrElse(pkg, Set()),
        notNullMethodsByPackage.getOrElse(pkg, Set()),
        nullableMethodsByPackage.getOrElse(pkg, Set()),
        pureMethodsByPackage.getOrElse(pkg, Set()),
        contractClausesByPackage.getOrElse(pkg, Map())
      )
    }.toMap
  }
}

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
      val key = Key(method, Out, ResolveDirection.Upward)
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
  val nullableAnn = <annotation name='org.jetbrains.annotations.Nullable'/>

  // intermediate data structure to serialize @Contract annotations
  class Contract {
    var pure = false
    var clauses = ListBuffer[(InOut, Value)]()
  }

  def toXmlAnnotations(result: InferenceResult, extras: Map[Method, MethodExtra]): List[Elem] = {
    var annotations = Map[String, List[Elem]]()

    // preparations for contracts
    val contracts = mutable.HashMap[Key, Contract]()

    // @NotNull parameters
    for (key <- result.notNullParameters) {
      val In(paramIndex) = key.direction
      val method = key.method
      val aKey = s"${annotationKey(key, extras(method))} $paramIndex"
      val paramAnnotations = annotations.getOrElse(aKey, Nil)
      annotations = annotations.updated(aKey, (notNullAnn :: paramAnnotations).sortBy(_.toString))
    }

    // @Nullable parameters
    for (key <- result.nullableParameters) {
      val In(paramIndex) = key.direction
      val method = key.method
      val aKey = s"${annotationKey(key, extras(method))} $paramIndex"
      val paramAnnotations = annotations.getOrElse(aKey, Nil)
      annotations = annotations.updated(aKey, (nullableAnn :: paramAnnotations).sortBy(_.toString))
    }

    // @NotNull methods
    for (key <- result.notNullMethods) {
      val method = key.method
      val aKey = annotationKey(key, extras(method))
      val methodAnnotations = annotations.getOrElse(aKey, Nil)
      annotations = annotations.updated(aKey, (notNullAnn :: methodAnnotations).sortBy(_.toString))
    }

    // @Nullable methods
    for (key <- result.nullableMethods) {
      val method = key.method
      val aKey = annotationKey(key, extras(method))
      val methodAnnotations = annotations.getOrElse(aKey, Nil)
      annotations = annotations.updated(aKey, (nullableAnn :: methodAnnotations).sortBy(_.toString))
    }

    // @Contract pure = true
    for (key <- result.pureMethods) {
      if (!contracts.contains(key)) {
        contracts(key) = new Contract()
      }
      contracts(key).pure = true
    }

    // constructing @Contract annotations
    for ((key, value) <- result.contractClauses) {
      key.direction match {
        case inOut:InOut =>
          val contractsKey = key.copy(direction = Out)
          if (!contracts.contains(contractsKey)) {
            contracts(contractsKey) = new Contract()
          }
          contracts(contractsKey).clauses += (inOut -> value)
        case _ =>

      }
    }

    // merging contracts and purity
    for ((key, contract) <- contracts) {

      val arity = Type.getArgumentTypes(key.method.methodDesc).size

      val contractValues: Option[String] =
        if (!result.notNullMethods(key) && contract.clauses.nonEmpty)
          Some(contract.clauses.map {
            case (InOut(i, inValue), outValue) =>
              (0 until arity).map {
                case `i` => AnnotationsUtil.contractValueString(inValue)
                case _ => "_"
              }.mkString("", ",", s"->${AnnotationsUtil.contractValueString(outValue)}")
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

      val annKey = annotationKey(key, extras(key.method))
      contractAnnotation.foreach { ann =>
        annotations = annotations.updated(annKey, ann :: annotations.getOrElse(annKey, Nil))
      }
    }

    annotations.map {
      case (k, v) => <item name={k}>{v}</item>
    }.toList.sortBy(s => sortKey((s \\ "@name").toString()))
  }

  // the main logic to interact with IDEA
  def annotationKey(key: Key, extra: MethodExtra): String = {
    val method = key.method
    val rawKey = if (method.methodName == "<init>")
      s"${internalName2Idea(method.internalClassName)} ${simpleName(method.internalClassName)}${parameters(method, extra)}"
    else
      s"${internalName2Idea(method.internalClassName)} ${returnType(method, extra)} ${method.methodName}${parameters(method, extra)}"
    key.resolveDirection match {
      case ResolveDirection.Upward =>
        rawKey
      case ResolveDirection.Downward =>
        val access = if ((extra.access & Opcodes.ACC_ABSTRACT) != 0) "abstract " else ""
        s"${access}virtual $rawKey"
    }
  }

  def sortKey(keyString: String) =
    if (keyString.startsWith("virtual "))
      (keyString.substring("virtual ".length), 1)
    else if (keyString.startsWith("abstract virtual "))
      (keyString.substring("abstract virtual ".length), 1)
    else
      (keyString, 0)

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
