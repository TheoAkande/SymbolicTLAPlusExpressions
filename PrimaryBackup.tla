------------------------ MODULE PrimaryBackup ------------------------
EXTENDS Sequences, Naturals, Bags

Atom == {"QueueingDelay", "MessageDelay", "ReceiveTimeout", "Alpha", "Beta", "Gamma", "Startup"}
Ordering == ({"Startup"} \X (Atom \ {"Startup"})) \cup ((Atom \ {"Startup", "QueueingDelay"}) \X {"QueueingDelay"})

T == INSTANCE SymbolicExpression WITH Atoms <- Atom, LTRelation <- Ordering

D == T!Expr("MessageDelay")
RECEIVE_TIMEOUT == T!Expr("ReceiveTimeout")
QUEUEING == T!Expr("QueueingDelay")

Nodes == INSTANCE Node WITH Atoms <- Atom, LTRelation <- Ordering
IDs == 0..2 (* A: 0, B: 1, L: 2 *)

A == 0
B == 1
L == 2

\* Constant stand-ins
MsgA == "MsgA" 
MsgB == "MsgB"

VARIABLES TauM, TauN, Messages, Sigma, Processed

Init ==
    /\ Messages = {}
    /\ Sigma = [n \in IDs |-> "Initial"]
    /\ TauN = [n \in IDs |-> T!EMPTY]
    /\ TauM = [m \in Messages |-> T!EMPTY]
    /\ Processed = {}

SendA ==
    /\ Sigma[A] = "Initial"
    /\ 
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, A, "Sent", {MsgA}, T!Expr("Alpha"))
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
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, B, "Sent", {MsgB}, T!Expr("Beta"))
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
        LET result == Nodes!NoReceive(Sigma, Messages, TauN, TauM, L, "Listen", {}, T!Expr("Startup"))
        IN (
            /\ Messages' = result.m
            /\ Sigma' = result.sigma
            /\ TauN' = result.tauN
            /\ TauM' = result.tauM
        )
    /\ UNCHANGED Processed

ProcessL ==
    /\ Sigma[L] = "Listen"
    /\ \E m \in Messages : m \notin Processed /\ T!LE(TauN[L], TauM[m])
    /\ 
        LET 
            message == CHOOSE m \in Messages : m \notin Processed /\ T!LE(TauN[L], TauM[m])
            result == Nodes!ReceiveQueue(Sigma, Messages, TauN, TauM, L, message, "Listen", {}, T!Expr("Gamma"))
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
            IF m \in Processed \/ T!LE(TauN[L], TauM[m]) THEN TauM[m]
            ELSE T!Max(TauM[m], TauN[L])
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
    T!LE(TauN[L], T!Add(T!Max(T!Expr("Alpha"), T!Expr("Beta")), T!Add(D, T!Mult(T!Expr("Gamma"), 2))))

=====================================================================
