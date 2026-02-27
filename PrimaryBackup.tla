------------------------ MODULE PrimaryBackup ------------------------
EXTENDS Sequences, Naturals, Bags, SymbolicExpression

Atom == {"QueueingDelay", "MessageDelay", "ReceiveTimeout", "Alpha", "Beta", "Gamma"}
Ordering == {}
    
D == Expr("MessageDelay")
RECEIVE_TIMEOUT == Expr("ReceiveTimeout")
QUEUEING == Expr("QueueingDelay")

Nodes == INSTANCE Node WITH LTRelation <- Ordering
IDs == 0..2 (* A: 0, B: 1, L: 2 *)

A == 0
B == 1
L == 2

\* Constant stand-ins
MsgA == "MsgA" 
MsgB == "MsgB"

VARIABLES TauM, TauN, Messages, Sigma, Processed

Init ==
    /\ SetAtomLT(Ordering)
    /\ Messages = {}
    /\ Sigma = [n \in IDs |-> "Initial"]
    /\ TauN = [n \in IDs |-> EMPTY]
    /\ TauM = [m \in Messages |-> EMPTY]
    /\ Processed = {}

SendA ==
    /\ Sigma[A] = "Initial"
    /\ 
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, A, "Sent", {MsgA}, Expr("Alpha"))
        IN (
            /\ Messages' = result.m
            /\ Sigma' = result.sigma
            /\ TauN' = result.tauN
            /\ TauM' = result.tauM
        )
    /\ UNCHANGED Processed

SendB ==
    /\ Sigma[B] = "Initial"
    /\ 
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, B, "Sent", {MsgB}, Expr("Beta"))
        IN (
            /\ Messages' = result.m
            /\ Sigma' = result.sigma
            /\ TauN' = result.tauN
            /\ TauM' = result.tauM
        )
    /\ UNCHANGED Processed

StartL ==
    /\ Sigma[L] = "Initial"
    /\
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, L, "Listen", {}, EMPTY)
        IN (
            /\ Messages' = result.m
            /\ Sigma' = result.sigma
            /\ TauN' = result.tauN
            /\ TauM' = result.tauM
        )
    /\ UNCHANGED Processed

ProcessL ==
    /\ Sigma[L] = "Listen"
    /\ \E m \in Messages : m \notin Processed /\ LE(TauN[L], TauM[m])
    /\ 
        LET 
            message == CHOOSE m \in Messages : m \notin Processed /\ LE(TauN[L], TauM[m])
            result == Nodes!ReceiveQueue(Sigma, Messages, TauN, TauM, L, message, "Listen", {}, Expr("Gamma"))
        IN (
            /\ Messages' = result.m
            /\ Sigma' = result.sigma
            /\ TauN' = result.tauN
            /\ TauM' = result.tauM
            /\ Processed' = Processed \cup {message}
        )

ActiveAction ==
    \/ SendA 
    \/ SendB
    \/ StartL
    \/ ProcessL

QueueMessage ==
    /\ Sigma[L] = "Listen"
    /\ \lnot ENABLED ActiveAction
    /\ \E m \in Messages : m \notin Processed
    (* The following bound can be put in place to prevent indefinite queueing *)
    \* /\ \A m \in (Messages \ Processed) :
    \*     \E n \in 1..10 : 
    \*         T!LE(TauN[L], T!Add(TauM[m], T!Mult(QUEUEING, n)))
    /\ TauM' = [
        m \in Messages |-> 
            IF m \in Processed \/ LE(TauN[L], TauM[m]) THEN TauM[m]
            ELSE Max(TauM[m], TauN[L])
        ]
    /\ UNCHANGED << TauN, Messages, Sigma, Processed >>

Done ==
    /\ Sigma[A] = "Sent"
    /\ Sigma[B] = "Sent"
    /\ Processed = {MsgA, MsgB}
    /\ UNCHANGED << TauM, TauN, Messages, Sigma, Processed >>

Next == 
    \/ SendA 
    \/ SendB
    \/ StartL
    \/ ProcessL
    \/ QueueMessage
    \/ Done

LBound ==
    LE(Add(D, Add(Expr("Gamma"), Expr("Alpha"))), Add(Max(Expr("Alpha"), Expr("Beta")), Add(D, Mult(Expr("Gamma"), 2))))
    \* LE(TauN[L], Add(Max(Expr("Alpha"), Expr("Beta")), Add(D, Mult(Expr("Gamma"), 2))))

=====================================================================
