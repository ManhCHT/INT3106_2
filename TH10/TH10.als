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
fact NoCycle {
    no e: Entry | e in e.^parent
}
fact ReachRoot {
    all e: Entry - Root | Root in e.^parent
}
fact MaxThreeDirectChildren {
    all d: Dir | #{e: Entry | e.parent = d} <= 3
}

pred FileAtDepthThree {
    some f: File | Root in f.(parent.parent.parent)
}
pred DirWithTwoDirectFiles {
    some d: Dir | #{f: File | f.parent = d} = 2
}
pred DirWithAtLeastThreeSubtreeFiles {
    some d: Dir | #{f: File | d in f.^parent} >= 3
}

assert NonRootHasRootAncestor {
    all e: Entry - Root |  Root in e.^parent
}
assert AncestorIsAsymmetric {
    all a, b: Entry | a in b.^parent implies b not in a.^parent
}
assert DirectCapImpliesSubtreeFileCap {
    all d: Dir | #{e: Entry | e.parent = d} <= 3 implies #{f: File | d in f.^parent} <= 3
}

run {} for 6
run FileAtDepthThree for 6
run DirWithTwoDirectFiles for 6
run DirWithAtLeastThreeSubtreeFiles for 6

run FileAtDepthThree for 8
run DirWithTwoDirectFiles for 8
run DirWithAtLeastThreeSubtreeFiles for 8

check NonRootHasRootAncestor for 6
check NonRootHasRootAncestor for 8

check AncestorIsAsymmetric for 6
check AncestorIsAsymmetric for 8

check DirectCapImpliesSubtreeFileCap for 6
check DirectCapImpliesSubtreeFileCap for 8
