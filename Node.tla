------------------------ MODULE Node ------------------------
EXTENDS Sequences, Naturals, SymbolicExpression

CONSTANTS LTRelation


D == Expr("MessageDelay")
RECEIVE_TIMEOUT == Expr("ReceiveTimeout")
QUEUEING == Expr("QueueingDelay")

(* 
    Some action 'A(n, Sigma)' transitions node 'n' to state 'sigmaPrime'
    producing messages 'mOut' taking time 'a' without calling 'receive'
*)
NoReceive(Sigma, M, TauN, TauM, n, sigmaPrime, mOut, a) ==
    LET 
        mPrime == M \cup mOut
        newTauN == Add(TauN[n], a)
        newMessageTime == Add(newTauN, D)
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
        newTauN == Add(TauN[n], Add(RECEIVE_TIMEOUT, a))
        newMessageTime == Add(newTauN, D)
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
        newTauN == Add(Max(TauN[n], TauM[m], LTRelation), a)
        newMessageTime == Add(newTauN, D)
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