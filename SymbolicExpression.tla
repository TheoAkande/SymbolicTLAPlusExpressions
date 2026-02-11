------------------------ MODULE SymbolicExpression ------------------------
(* 
    This module does not exactly work because of the way that TLC evaluates 
    sets and assigns types. Two possible workarounds:
    1. Define custom java class for this module to sidestep TLC
    2. Use expression id map which is not really convenient
*)
EXTENDS Naturals, Bags, Sequences, FiniteSets

RECURSIVE AtomLEHelp(_, _, _, _)
LOCAL AtomLEHelp(a, b, atoms, LTRelation) ==
    \/ a = b
    \/ <<a, b>> \in LTRelation
    \/ 
        \E c \in atoms : 
            /\ <<a, c>> \in LTRelation 
            /\ AtomLEHelp(c, b, atoms \ {a, b, c}, LTRelation)

LOCAL AtomLE(a, b, LTRelation) ==
    LET
        atoms == DOMAIN(LTRelation) \cup {LTRelation[x] : x \in DOMAIN LTRelation}
    IN 
        AtomLEHelp(a, b, atoms, LTRelation)

(* EXPR == EMPTY | atom | <<EXPR, EXPR>> | [EXPR -> Nat] *)
EMPTY == [type |-> "empty", val |-> {}]
NonEmptyBase == {"atom", "max"}

LOCAL MakeBag(a) == [x \in {a} |-> 1]
LOCAL ExprToBag(a) ==
    CASE a.type = "empty" -> EmptyBag
        [] a.type \in NonEmptyBase -> MakeBag(a)
        [] a.type = "sum" -> a.val

(* Atom to Expression *)
Expr(a) == [type |-> "atom", val |-> a]
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

RECURSIVE LE(_, _, _), Subset(_, _, _)
LE(a, b, LT) ==
    CASE a.type = "empty" -> TRUE
        [] b.type = "empty" -> 
            a.type = "empty"
        [] a.type = "atom" /\ b.type = "atom" -> 
            a.val = b.val \/ AtomLE(a.val, b.val, LT)
        [] a.type = "max" /\ b.type = "max" -> 
            \E i \in 1..2 : \E j \in 1..2 :
                /\ LE(a.val[1], b.val[i], LT)
                /\ LE(a.val[2], b.val[j], LT)
        [] a.type # "max" /\ b.type = "max" ->
            \/ LE(a, b.val[1], LT)
            \/ LE(a, b.val[2], LT)
        [] a.type = "max" /\ b.type # "max" ->
            /\ LE(a.val[1], b, LT)
            /\ LE(a.val[2], b, LT)
        [] a.type = "sum" /\ b.type = "sum" ->
            Subset(a.val, b.val, LT)
        [] a.type = "sum" /\ b.type \in NonEmptyBase ->
            LE(a, Sum(MakeBag(b)), LT)
        [] a.type \in NonEmptyBase /\ b.type = "sum" ->
            Subset(MakeBag(a), b.val, LT)

(* 
    A helper for LE; takes in two bags of symbolic expressions and is true if 
    a is a subset of b.
    Note that we can't use typical bag subseteq because we need to use the LE
    relation
*)
LOCAL Subset(a, b, LT) ==
    IF a = EmptyBag THEN TRUE
    ELSE 
        LET 
            x == CHOOSE v \in DOMAIN a : TRUE
            n == CopiesIn(x, a)
        IN 
            \E y \in DOMAIN b : LET m == CopiesIn(y, b) IN
                /\ n <= m
                /\ LE(x, y, LT)
                /\ Subset(a (-) [v \in {x} |-> n], b (-) [v \in {y} |-> n], LT)


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
            /\ BagCardinality(a.val) = BagCardinality(b.val)
            /\ Cardinality(DOMAIN a.val) = Cardinality(DOMAIN b.val) 
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

(* 
    Note that the use of this SHOULD enforce that a bag never has two items
    a, b such that a and b are syntactically different but semantically the 
    same.
*)
LOCAL BagAdd(a, b) ==
    [
        e \in (DOMAIN a) \cup (DOMAIN b) |->
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

RECURSIVE Max(_, _, _)
Max(a, b, LT) ==
    IF LE(a, b, LT) /\ \lnot LE(b, a, LT) THEN b
    ELSE IF LE(b, a, LT) /\ \lnot LE(a, b, LT) THEN a
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
