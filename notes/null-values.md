# `null` values in analysis

`faba.analysis.NullValue` for representing `null` values in analysis has following internals:

```scala
@AsmAbstractValue
case class NullValue(origin: Int)
     extends BasicValue(Type.getObjectType("null"))
     with Trackable
```

The reason for `NullValue` to be trackable is that we need to distinguish different `null` values during analysis.

An illustrative example of usefulness of tracking `null`s.

`java.sql.Date#valueOf(String)` (in JDK7_45) has following implementation:

```java
public static Date valueOf(String s) {
    ...
    Date d = null;
    ...
    if (d == null) {
        throw new java.lang.IllegalArgumentException();
    }
    return d;
}

```

In bytecode (in a general case) a connection between values and variables is lost.
So, when processing `IFNULL` instruction for `if (d == null)` we need to propagate information that `d != null` in later instructions.
The simple way to do it is to propagate constraint that value originated at corresponding index (`Date d = null`) is not `null` anymore.
