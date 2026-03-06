------------------------ MODULE SymbolicExpressionTest ------------------------
EXTENDS Naturals, Bags, Sequences, FiniteSets, Integers, SymbolicExpression

VARIABLE ghost
Init == ghost = 0
Next == UNCHANGED ghost

a == Expr("Alpha")
b == Expr("Beta")
c == Expr("Gamma")

Expressions == {
    EMPTY,
    a,
    b,
    c,
    Add(a, b),
    Add(Add(a, b), c),
    Max(a, b),
    Add(Max(a, b), Max(Add(b, c), a))
}

Ns == {
    0, 1, 5
}

Identity == \A x \in Expressions :
    /\ Equal(Add(EMPTY, x), x) 
    /\ Equal(Add(x, EMPTY), x)
    /\ \A n \in Ns : Equal(Mult(EMPTY, n), EMPTY)
    /\ Equal(Max(EMPTY, x), x)
    /\ Equal(Max(x, EMPTY), x)
ASSUME Identity

Reflexivity == \A x \in Expressions :
    /\ Equal(x, x)
    /\ LE(x, x)
ASSUME Reflexivity

Symmetry == \A x \in Expressions : \A y \in Expressions :
    Equal(x, y) <=> Equal(y, x)
ASSUME Symmetry

Transitivity == \A x \in Expressions : \A y \in Expressions : \A z \in Expressions :
    (LE(x, y) /\ LE(y, z)) => LE(x, z)
ASSUME Transitivity

Congruence == \A x \in Expressions : \A y \in Expressions : \A z \in Expressions :
    LE(x, y) => (
        /\ LE(Add(x, z), Add(y, z))
        /\ LE(Max(x, z), Max(y, z))
        /\ \A n \in Ns : LE(Mult(x, n), Mult(y, n))
    )
ASSUME Congruence

Commutativity == \A x \in Expressions : \A y \in Expressions :
    /\ Equal(Add(x, y), Add(y, x))
    /\ Equal(Max(x, y), Max(y, x))
ASSUME Commutativity

Associativity == \A x \in Expressions : \A y \in Expressions : \A z \in Expressions :
    /\ Equal(Add(Add(x, y), z), Add(x, Add(y, z)))
    \* /\ Equal(Max(Max(x, y), z), Max(x, Max(y, z)))   \* TODO: This doesn't hold; should it
ASSUME Associativity

Idempotency == \A x \in Expressions :
    Equal(Max(x, x), x)
ASSUME Idempotency

Absorption == \A x \in Expressions : \A y \in Expressions :
    Equal(Max(x, Add(x, y)), Add(x, y))
ASSUME Absorption

Antisymmetry == \A x \in Expressions : \A y \in Expressions :
    (LE(x, y) /\ LE(y, x) <=> Equal(x, y))
ASSUME Antisymmetry

MaxCharacterisation == \A x \in Expressions : \A y \in Expressions : \A z \in Expressions :
    /\ LE(x, Max(x, y))
    /\ LE(y, Max(x, y))
    /\ (LE(x, z) /\ LE(y, x)) => LE(Max(x, y), z)
ASSUME MaxCharacterisation

PreservesOrder == \A x \in Expressions : \A y \in Expressions :
    LE(x, Add(x, y))
ASSUME PreservesOrder

MaxAddInteraction == \A x \in Expressions : \A y \in Expressions : \A z \in Expressions :
    /\ Equal(Max(Add(x, y), Add(x, z)), Add(x, Max(y, z)))
ASSUME MaxAddInteraction

Lattice == \A x \in Expressions : \A y \in Expressions :
    /\ Equal(Max(x, y), y) <=> LE(x, y)
ASSUME Lattice

Positivity == \A x \in Expressions :
    /\ LE(EMPTY, x)
ASSUME Positivity

===========================================================================
