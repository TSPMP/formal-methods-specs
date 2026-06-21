---- MODULE NoHwReorderNoMemHier ----

EXTENDS Integers

VARIABLES x, y, pc1, pc2

PC1States == {"BeforeY", "BeforeX", "Stop"}
PC2States == {"BeforeIf", "BeforeY", "Stop"}

TypeOk ==
    /\ x \in Int
    /\ y \in Int
    /\ pc1 \in PC1States
    /\ pc2 \in PC2States

Init ==
    /\ x = 0
    /\ y = 1
    /\ pc1 = "BeforeY"
    /\ pc2 = "BeforeIf"

Thread1AssignY ==
    /\ pc1 = "BeforeY"
    /\ pc1' = "BeforeX"
    /\ y' = 3
    /\ UNCHANGED <<x, pc2>>

Thread1AssignX ==
    /\ pc1 = "BeforeX"
    /\ pc1' = "Stop"
    /\ x' = 1
    /\ UNCHANGED <<y, pc2>>

Thread2If ==
    /\ pc2 = "BeforeIf"
    /\ IF x = 1 THEN pc2' = "BeforeY" ELSE pc2' = "Stop"
    /\ UNCHANGED <<x, y, pc1>>

Thread2AssignY ==
    /\ pc2 = "BeforeY"
    /\ pc2' = "Stop"
    /\ y' = 2 * y
    /\ UNCHANGED <<x, pc1>>

Next ==
    \/ Thread1AssignY
    \/ Thread1AssignX
    \/ Thread2If
    \/ Thread2AssignY

Spec == Init /\ [][Next]_<<x, y, pc1, pc2>>

----

Correctness ==
    /\ pc1 = "Stop"
    /\ pc2 = "Stop"
    =>
    y \in {3, 6}

=================================
