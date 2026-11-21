abstract sig Entry {
    parent: lone Dir
}
sig File extends Entry {}
sig Dir extends Entry {}
one sig Root extends Dir {}

fact RootHasNoParent {
    no Root.parent
}
fact NonRootHasOneParent {
    all e: Entry - Root | one e.parent
}
fact NoSelfParent {
    all d: Dir | d not in d.parent
}
fact NoMutualParent {
    all d1, d2: Dir | d1 != d2 and d1 in d2.parent implies d2 not in d1.parent
}
fact NoCycle3 {
    all d1, d2, d3: Dir |
        (d1 != d2 and d2 != d3 and d1 != d3 and
         d2 in d1.parent and d3 in d2.parent) implies d1 not in d3.parent
}

assert FileHasParent {
    all f: File | some f.parent
}
assert NoThreeDirCycle {
    no disj d1, d2, d3: Dir |
        d2 in d1.parent and d3 in d2.parent and d1 in d3.parent
}
assert NonRootDirParentIsRoot {
    all d: Dir - Root | d.parent = Root
}

check FileHasParent for 4
check FileHasParent for 5
check FileHasParent for 6

check NoThreeDirCycle for 4
check NoThreeDirCycle for 5
check NoThreeDirCycle for 6

check NonRootDirParentIsRoot for 4
check NonRootDirParentIsRoot for 5
check NonRootDirParentIsRoot for 6
