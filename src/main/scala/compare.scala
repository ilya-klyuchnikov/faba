package faba

import faba.data.ResolveDirection

object Compare {
  def main(args: Array[String]) {
    val source = CmdUtils.getIn(args)
    // with inheritance
    val result1 = new MainProcessor(true).process(source)
    // without inheritance
    val result2 = new MainProcessor(false).process(source)

    //val notNullParamDelta =
    //  result2.notNullParameters -- result1.notNullParameters

    val notNullParam1Count =
      result1.notNullParameters.size
    val notNullParam1UpwardCount =
      result1.notNullParameters.count(k => k.resolveDirection == ResolveDirection.Upward)
    val notNullParam1DownwardCount =
      result1.notNullParameters.count(k => k.resolveDirection == ResolveDirection.Downward)

    val notNullParam2Count =
      result2.notNullParameters.size
    val notNullParam2UpwardCount =
      result2.notNullParameters.count(k => k.resolveDirection == ResolveDirection.Upward)
    val notNullParam2DownwardCount =
      result2.notNullParameters.count(k => k.resolveDirection == ResolveDirection.Downward)

    val nullableParam1Count =
      result1.nullableParameters.size
    val nullableParam1UpwardCount =
      result1.nullableParameters.count(k => k.resolveDirection == ResolveDirection.Upward)
    val nullableParam1DownwardCount =
      result1.nullableParameters.count(k => k.resolveDirection == ResolveDirection.Downward)

    val nullableParam2Count =
      result2.nullableParameters.size
    val nullableParam2UpwardCount =
      result2.nullableParameters.count(k => k.resolveDirection == ResolveDirection.Upward)
    val nullableParam2DownwardCount =
      result2.nullableParameters.count(k => k.resolveDirection == ResolveDirection.Downward)

    val notNullMethod1Count =
      result1.notNullMethods.size
    val notNullMethod1UpwardCount =
      result1.notNullMethods.count(k => k.resolveDirection == ResolveDirection.Upward)
    val notNullMethod1DownwardCount =
      result1.notNullMethods.count(k => k.resolveDirection == ResolveDirection.Downward)

    val notNullMethod2Count =
      result2.notNullMethods.size
    val notNullMethod2UpwardCount =
      result2.notNullMethods.count(k => k.resolveDirection == ResolveDirection.Upward)
    val notNullMethod2DownwardCount =
      result2.notNullMethods.count(k => k.resolveDirection == ResolveDirection.Downward)

    val stat =
      s"""
        |                             | ${i("FABA 1.1")                       } | ${i("FABA 1.2")                       }
        |
        | @NotNull parameters         | ${i(notNullParam1Count)               } | ${i(notNullParam2Count)               }
        | @NotNull parameters Up      | ${i(notNullParam1UpwardCount)         } | ${i(notNullParam2UpwardCount)         }
        | @NotNull parameters Down    | ${i(notNullParam1DownwardCount)       } | ${i(notNullParam2DownwardCount)       }
        |
        | @Nullable parameters        | ${i(nullableParam1Count)              } | ${i(nullableParam2Count)              }
        | @Nullable parameters Up     | ${i(nullableParam1UpwardCount)        } | ${i(nullableParam2UpwardCount)        }
        | @Nullable parameters Down   | ${i(nullableParam1DownwardCount)      } | ${i(nullableParam2DownwardCount)      }
        |
        | @NotNull methods            | ${i(notNullMethod1Count)              } | ${i(notNullMethod2Count)              }
        | @NotNull methods Up         | ${i(notNullMethod1UpwardCount)        } | ${i(notNullMethod2UpwardCount)        }
        | @NotNull methods Down       | ${i(notNullMethod1DownwardCount)      } | ${i(notNullMethod2DownwardCount)      }
      """.stripMargin

    println(stat)
  }


  def i(n: Int) = {
    val s = n.toString
    " " * (10 - s.length) + s
  }

  def i(s: String) = {
    " " * (10 - s.length) + s
  }

}