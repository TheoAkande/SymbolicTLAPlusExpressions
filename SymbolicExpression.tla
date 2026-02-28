------------------------ MODULE SymbolicExpression ------------------------
(* 
    Note that this module SHOULD provide a valid TLA+ specification for SymbolicExpression behaviour, 
    but does not reflect the TLC behaviour due to TLC limitations. Ensure that the java override
    is used when running this module with TLC. Do not attempt to perform operations on the structure
    of expressions as they differ in structure in TLC (represented by their own Value types rather than
    existing TLC/TLA+ Values)

    The public API of operators/definitions exposed by this module are as follows:
    - EMPTY
    - Expr(_)     : String      -> Expr
    - Equal(_, _) : Expr x Expr -> Bool
    - LE(_, _)    : Expr x Expr -> Bool
    - Mult(_, _)  : Expr x Expr -> Expr
    - Add(_, _)   : Expr x Expr -> Expr
    - Max(_, _)   : Expr x Expr -> Expr
*)
EXTENDS Naturals, Bags, Sequences, FiniteSets, Integers

(* EXPR == EMPTY | atom | <<EXPR, EXPR>> | [EXPR -> Nat]  *)
(*                        (max of exprs)   (sum of exprs) *)
EMPTY == [type |-> "empty", val |-> {}]
LOCAL NonEmptyBase == {"atom", "max"}

LOCAL MakeBag(a) == [x \in {a} |-> 1]
LOCAL ExprToBag(a) ==
    CASE a.type = "empty" -> EmptyBag
        [] a.type \in NonEmptyBase -> MakeBag(a)
        [] a.type = "sum" -> a.val

(* String to Expression *)
Expr(a) == [type |-> "atom", val |-> a]

LOCAL Sum(expr) == [type |-> "sum", val |-> expr]

(* Note that there is no inherent evaluation order for this case statement *)
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

RECURSIVE LE(_, _), BagLE(_, _)
LE(a, b) ==
    CASE a.type = "empty" -> TRUE
        [] b.type = "empty" -> 
            a.type = "empty"
        [] a.type = "atom" /\ b.type = "atom" -> 
            a.val = b.val
        [] a.type = "max" /\ b.type = "max" -> 
            \E j \in 1..2 : \A i \in 1..2 :
                /\ LE(a.val[i], b.val[j])
        [] a.type # "max" /\ b.type = "max" ->
            \/ LE(a, b.val[1])
            \/ LE(a, b.val[2])
        [] a.type = "max" /\ b.type # "max" ->
            /\ LE(a.val[1], b)
            /\ LE(a.val[2], b)
        [] a.type = "sum" /\ b.type = "sum" ->
            BagLE(a.val, b.val)
        [] a.type = "sum" /\ b.type \in NonEmptyBase ->
            BagLE(a.val, MakeBag(b))
        [] a.type \in NonEmptyBase /\ b.type = "sum" ->
            BagLE(MakeBag(a), b.val)

LOCAL Min(a, b) == IF a < b THEN a ELSE b

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

LOCAL FilterBag(a, type) ==
    [
        v \in {x \in DOMAIN a : x.type = type} |-> a[v]
    ]

Mult(a, n) ==
    IF n = 0 \/ a.type = "empty" THEN EMPTY
    ELSE
        IF a.type \in NonEmptyBase THEN Sum([x \in {a} |-> n])
        ELSE Sum([expr \in BagToSet(a.val) |-> a[expr] * n])

RECURSIVE BagToSeq(_)
LOCAL BagToSeq(a) ==
    IF DOMAIN a = {} THEN <<>>
    ELSE LET v == CHOOSE x : x \in DOMAIN a IN 
        Append(Mult(v, a[v]), BagToSeq([
            p \in (DOMAIN a) \ v |-> a[p]
        ]))

LOCAL Bit(i, j) ==
  (i \div 2^j) % 2

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

(* This does not need to be fast (tournament) since it is a placeholder anyway *)
RECURSIVE SeqToSum(_)
LOCAL SeqToSum(seq) ==
    IF seq = <<>> THEN EMPTY
    ELSE Add(Head(seq), SeqToSum(Tail(seq)))

(* 
    A helper for LE; takes in two bags of symbolic expressions and is true if 
    bag a represents a sum le bag b
*)
LOCAL BagLE(a, b) ==
    IF a = EmptyBag THEN TRUE
    ELSE 
        LET 
            aSubB == CappedBagSub(a, b)
            bSubA == CappedBagSub(b, a)
            aAtoms == Sum(FilterBag(aSubB, "atom"))
            bAtoms == Sum(FilterBag(bSubA, "atom"))
            aMaxs == BagToSeq(FilterBag(aSubB, "max"))
            bMaxs == BagToSeq(FilterBag(bSubA, "max"))
            aAllMaxCombos == {[
                i \in 1..Len(aMaxs) |-> aMaxs[i].val[Bit(j, i) - 1]
            ] : j \in 0..(2^(Len(aMaxs)) - 1)}
            bAllMaxCombos == {[
                i \in 1..Len(bMaxs) |-> bMaxs[i].val[Bit(j, i) - 1]
            ] : j \in 0..(2^(Len(bMaxs)) - 1)}
            aExprs == {
                Add(aAtoms, SeqToSum(v)) : v \in aAllMaxCombos
            }
            bExprs == {
                Add(bAtoms, SeqToSum(v)) : v \in bAllMaxCombos
            }
        IN 
            \A less \in aExprs : 
                \E more \in bExprs :
                    LE(less, more)

(* Bag to Expression *)
LOCAL ToExpr(bag) ==
    IF bag = EmptyBag THEN EMPTY
    ELSE IF BagCardinality(bag) = 1 THEN 
        CHOOSE v \in (DOMAIN bag) : TRUE (* Since only one item *)
    ELSE Sum(bag)

LOCAL MakeMax(e1, e2) ==  [type |-> "max", val |-> <<e1, e2>>]

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
            ELSE Sum([x \in {Sum(common), maxExpr} |-> 1])

=============================================================================
