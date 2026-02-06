------------------------ MODULE Node ------------------------
EXTENDS Sequences, Naturals

CONSTANTS Atoms, LTRelation

T == INSTANCE SymbolicExpression WITH Atoms <- Atoms, LTRelation <- LTRelation

D == T!Expr("MessageDelay")
RECEIVE_TIMEOUT == T!Expr("ReceiveTimeout")
QUEUEING == T!Expr("QueueingDelay")

(* 
    Some action 'A(n, Sigma)' transitions node 'n' to state 'sigmaPrime'
    producing messages 'mOut' taking time 'a' without calling 'receive'
*)
NoReceive(Sigma, M, TauN, TauM, n, sigmaPrime, mOut, a) ==
    LET 
        mPrime == M \cup mOut
        newTauN == T!Add(TauN[n], a)
        newMessageTime == T!Add(newTauN, D)
    IN
        [
            sigma |-> [Sigma EXCEPT ![n] = sigmaPrime],
            m     |-> mPrime,
            tauN  |-> [TauN EXCEPT ![n] = newTauN],
            tauM  |-> [
                t \in mPrime |-> IF t \in M THEN TauM[t] ELSE newMessageTime
            ]
        ]

(*
    Some action 'A(n, Sigma)' transitions node 'n' to state 'sigmaPrime' 
    producing messages 'mOut' taking time 'a' calling 'receive' but timing
    out
*)
ReceiveTimeout(Sigma, M, TauN, TauM, n, sigmaPrime, mOut, a) ==
    LET
        mPrime == M \cup mOut
        newTauN == T!Add(TauN[n], T!Add(RECEIVE_TIMEOUT, a))
        newMessageTime == T!Add(newTauN, D)
    IN
        [
            sigma |-> [Sigma EXCEPT ![n] = sigmaPrime],
            m     |-> mPrime,
            tauN  |-> [TauN EXCEPT ![n] = newTauN],
            tauM  |-> [
                t \in mPrime |-> IF t \in M THEN TauM[t] ELSE newMessageTime
            ]
        ]

(*
    Some action 'A(n, Sigma, m)' transitioning node 'n' to state 'sigmaPrime'
    producing messages 'mOut' taking time 'a' calling 'receive' and not 
    timing out.

    Pre: T!LE(TauN[n], T!Add(TauM[m] + QUEUEING))
*)
ReceiveQueue(Sigma, M, TauN, TauM, n, m, sigmaPrime, mOut, a) ==
    LET
        mPrime == M \cup mOut
        newTauN == T!Add(T!Max(TauN[n], TauM[m]), a)
        newMessageTime == T!Add(newTauN, D)
    IN
        [
            sigma |-> [Sigma EXCEPT ![n] = sigmaPrime],
            m     |-> mPrime,
            tauN  |-> [TauN EXCEPT ![n] = newTauN],
            tauM  |-> [
                t \in mPrime |-> IF t \in M THEN TauM[t] ELSE newMessageTime
            ]
        ]

=============================================================