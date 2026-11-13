# Bundled Java PathFinder

These unmodified JPF 8 binaries require Java 11 and were built from
[jpf-core revision `0916082fac`](https://github.com/javapathfinder/jpf-core/commit/0916082fac91405e11ec7ce55f9068ce84d61aaa):

- `jpf.jar`: the host JVM's model checker and native peers.
- `jpf-classes.jar`: the Java classes modeled by JPF.

The binaries were obtained from the
[TLA+ repository's pinned copy](https://github.com/tlaplus/tlaplus/tree/d8fb231de4e4b5d02c1b2ed1ac759c086f694021/tlatools/org.lamport.tlatools/lib).
They are included here so the example needs no other checkout or dependency
download. JPF is distributed under the [Apache License 2.0](LICENSE-2.0.txt).

[jpf.properties](../jpf.properties) contains the matching defaults, adapted from
[the same repository revision](https://github.com/tlaplus/tlaplus/blob/d8fb231de4e4b5d02c1b2ed1ac759c086f694021/tlatools/org.lamport.tlatools/test-verify/jpf.properties).
Its dependency paths point to these bundled jars; the unrelated test classpaths
and absent annotations jar have been removed.
