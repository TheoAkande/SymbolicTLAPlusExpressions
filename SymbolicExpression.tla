------------------------ MODULE SymbolicExpression ------------------------
EXTENDS Naturals, Bags, Sequences

CONSTANTS Atoms, LTRelation (* {atom} X {atom} *)

RECURSIVE AtomLEHelp(_, _, _)
AtomLEHelp(a, b, decreasingAtoms) ==
    \/ a = b
    \/ <<a, b>> \in LTRelation
    \/ 
        \E c \in decreasingAtoms : 
            /\ <<a, c>> \in LTRelation 
            /\ AtomLEHelp(c, b, decreasingAtoms \ {a, b, c})

AtomLE(a, b) == AtomLEHelp(a, b, Atoms)

(* EXPR == EMPTY | atom | <<EXPR, EXPR>> | [EXPR -> Nat] *)
EMPTY == [type |-> "empty", val |-> {}]
NonEmptyBase == {"atom", "max"}

LOCAL MakeBag(a) == [x \in {a} |-> 1]
LOCAL ExprToBag(a) ==
    CASE a.type = "empty" -> EmptyBag
        [] a.type \in NonEmptyBase -> MakeBag(a)
        [] a.type = "sum" -> a.val

(* Atom to Expression *)
Expr(a) == [type |-> "atom", val |-> <<a>>] (* Have to make val a function bc TLC sucks *)
(* Bag to Expression *)
Sum(expr) == [type |-> "sum", val |-> expr]
(* Two Expressions to max of them *)
MakeMax(e1, e2) ==  [type |-> "max", val |-> <<e1, e2>>]
(* Bag to Expression *)
ToExpr(bag) ==
    IF bag = EmptyBag THEN EMPTY
    ELSE IF BagCardinality(bag) = 1 THEN 
        CHOOSE v \in (DOMAIN bag) : TRUE (* Since only one item *)
    ELSE Sum(bag)

RECURSIVE LE(_, _), Subset(_, _)
LE(a, b) ==
    CASE a.type = "empty" -> TRUE
        [] b.type = "empty" -> 
            a.type = "empty"
        [] a.type = "atom" /\ b.type = "atom" -> 
            a.val = b.val \/ AtomLE(a.val[1], b.val[1])
        [] a.type = "max" /\ b.type = "max" -> 
            \/
                /\ LE(a.val[1], b.val[1]) 
                /\ LE(a.val[2], b.val[2])
            \/
                /\ LE(a.val[1], b.val[2]) 
                /\ LE(a.val[2], b.val[1])
        [] a.type # "max" /\ b.type = "max" ->
            \/ LE(a, b.val[1])
            \/ LE(a, b.val[2])
        [] a.type = "max" /\ b.type # "max" ->
            /\ LE(a.val[1], b)
            /\ LE(a.val[2], b)
        [] a.type = "sum" /\ b.type = "sum" ->
            Subset(a.val, b.val)
        [] a.type = "sum" /\ b.type \in NonEmptyBase ->
            LE(a, Sum(MakeBag(b)))
        [] a.type \in NonEmptyBase /\ b.type = "sum" ->
            Subset(MakeBag(a), b.val)

(* 
    A helper for LE; takes in two bags of symbolic expressions and is true if 
    a is a subset of b.
    Note that we can't use typical bag subseteq because we need to use the LE
    relation
*)
Subset(a, b) ==
    IF a = EmptyBag THEN TRUE
    ELSE 
        LET 
            x == CHOOSE v \in DOMAIN a : TRUE
            n == CopiesIn(x, a)
        IN 
            \E y \in DOMAIN b : LET m == CopiesIn(y, b) IN
                /\ n <= m
                /\ LE(x, y)
                /\ Subset(a (-) [v \in {x} |-> n], b (-) [v \in {y} |-> n])


RECURSIVE Equal(_, _)
Equal(a, b) ==
    CASE a.type = "empty" ->
        \/ b.type = "empty" 
        \/
            /\ b.type = "sum" 
            /\ b.val = EmptyBag
        [] b.type = "empty" -> 
            \/ a.type = "empty" 
            \/ 
                /\ a.type = "sum" 
                /\ a.val = EmptyBag
        [] a.type = "atom" /\ b.type = "atom" -> 
            a.val = b.val
        [] a.type = "max" /\ b.type = "max" -> 
            \/
                /\ Equal(a.val[1], b.val[1])
                /\ Equal(a.val[2], b.val[2])
            \/
                /\ Equal(a.val[1], b.val[2])
                /\ Equal(a.val[2], b.val[1])
        [] a.type = "sum" /\ b.type = "sum" ->
            /\
                \A v1 \in (DOMAIN a.val) :
                    \E v2 \in (DOMAIN b.val) :
                        /\ a.val[v1] = b.val[v2]
                        /\ Equal(v1, v2)
            /\
                \A v1 \in (DOMAIN b.val) :
                    \E v2 \in (DOMAIN a.val) :
                        /\ a.val[v1] = b.val[v2]
                        /\ Equal(v1, v2)
        [] a.type # b.type /\ a.type # "empty" /\ b.type # "empty" -> 
            FALSE

RECURSIVE SetToEqualSeq(_)
LOCAL SetToEqualSeq(S) ==
  IF S = {} THEN <<>>
  ELSE 
    LET x == CHOOSE x \in S : TRUE
    IN SetToEqualSeq({v \in S : ~Equal(v, x)}) \o <<x>>

LOCAL BagDomainUnion(a, b) ==
    LET 
        seqA == SetToEqualSeq(DOMAIN a)
        seqB == SetToEqualSeq(DOMAIN b)
        superSequence == seqA \o seqB 
        domainInts == {
            x \in 1..Len(superSequence) :
                ~(\E v \in 1..(x-1) : Equal(superSequence[x], superSequence[v]))
        }
    IN
        { superSequence[i] : i \in domainInts}

(* 
    Note that the use of this SHOULD enforce that a bag never has two items
    a, b such that a and b are syntactically different but semantically the 
    same.
*)
LOCAL BagAdd(a, b) ==
    [
        e \in BagDomainUnion(a, b) |->
            IF 
                /\ e \in (DOMAIN a) 
                /\ \lnot (\E x \in (DOMAIN b) : Equal(e, x))
            THEN
                CopiesIn(e, a)
            ELSE IF 
                /\ e \in (DOMAIN b) 
                /\ \lnot (\E x \in (DOMAIN a) : Equal(e, x))
            THEN
                CopiesIn(e, b)
            ELSE IF 
                e \in (DOMAIN a)
            THEN
                LET 
                    o == CHOOSE v \in (DOMAIN b) : Equal(e, v) 
                IN 
                    CopiesIn(e, a) + CopiesIn(o, b)  
            ELSE 
                LET 
                    o == CHOOSE v \in (DOMAIN a) : Equal(e, v) 
                IN 
                    CopiesIn(e, b) + CopiesIn(o, a)  
    ]

LOCAL Filter(a) == 
    LET
        domain == {v \in (DOMAIN a) : a[v] > 0}
    IN
        IF domain = {} THEN EmptyBag
        ELSE [e \in domain |-> a[e]]

(*
    x -> max(a[x] - b[x], 0)
*)
LOCAL CappedBagSub(a, b) ==
    LET 
        sub == [
            v \in (DOMAIN a) |->
                IF 
                    \E p \in (DOMAIN b) : Equal(p, v) 
                THEN 
                    LET 
                        p == CHOOSE q \in (DOMAIN b) : Equal(q, v)
                        nv == CopiesIn(v, a)
                        np == CopiesIn(p, b)
                    IN 
                        IF np > nv THEN 0 ELSE nv - np
                ELSE 
                    CopiesIn(v, a)
        ]
    IN
        Filter(sub)


Add(a, b) ==
    CASE a.type = "empty" -> b
        [] b.type = "empty" -> a
        [] a.type = "sum" /\ b.type = "sum" -> 
            Sum(BagAdd(a.val, b.val))
        [] a.type = "sum" /\ b.type \in NonEmptyBase -> 
            Sum(BagAdd(a.val, MakeBag(b)))
        [] a.type \in NonEmptyBase /\ b.type = "sum" -> 
            Sum(BagAdd(b.val, MakeBag(a)))
        [] a.type \in NonEmptyBase /\ b.type \in NonEmptyBase -> 
            Sum(BagAdd(MakeBag(a), MakeBag(b)))

Mult(a, n) ==
    IF n = 0 \/ a.type = "empty" THEN EMPTY
    ELSE
        IF a.type \in NonEmptyBase THEN Sum([x \in {a} |-> n])
        ELSE Sum([expr \in BagToSet(a.val) |-> a[expr] * n])

Unknown(a, b) ==
    \lnot LE(a, b) /\ \lnot LE(b, a) 

RECURSIVE Max(_, _)
Max(a, b) ==
    IF LE(a, b) /\ \lnot LE(b, a) THEN b
    ELSE IF LE(b, a) /\ \lnot LE(a, b) THEN a
    ELSE IF Equal(a, b) THEN a
    ELSE
        LET 
            bagA == ExprToBag(a)
            bagB == ExprToBag(b)
            aLeft == CappedBagSub(bagA, bagB)
            bLeft == CappedBagSub(bagB, bagA)
            common == 
                CappedBagSub(
                    CappedBagSub(
                        BagAdd(bagA, bagB), aLeft
                    ), bLeft
                )
            maxExpr == MakeMax(ToExpr(aLeft), ToExpr(bLeft))
        IN (* neither aLeft nor bLeft SHOULD be empty but common can *)
            IF common = EmptyBag THEN maxExpr
            ELSE Sum([x \in {Sum(common), maxExpr} |-> 1]) (* faster than doing a BagAdd *)

=============================================================================
