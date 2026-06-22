---- MODULE HwReorderNoMemHier ----

(*******************************************************************************
This was my attempt at modeling hardware reordering with no memory hierarchy to
see if I can find the execution that ends in the state x=1, y=2 as described in
https://doc.rust-lang.org/nomicon/atomics.html#hardware-reordering

It turns out that this is not enough :), i.e. you need the combination of a
memory hierarchy together with different observable execution orderings on
different cores to get the x=1, y=2 state.
*******************************************************************************)

EXTENDS Integers

VARIABLES x, y, t1_outstanding_ops, pc2

T1Operations == {"AssignX", "AssignY"}
PC2States == {"BeforeIf", "BeforeY", "Stop"}

TypeOk ==
    /\ x \in Int
    /\ y \in Int
    /\ t1_outstanding_ops \in SUBSET T1Operations
    /\ pc2 \in PC2States

Init ==
    /\ x = 0
    /\ y = 1
    /\ t1_outstanding_ops = T1Operations
    /\ pc2 = "BeforeIf"

Thread1AssignY ==
    /\ "AssignY" \in t1_outstanding_ops
    /\ t1_outstanding_ops' = t1_outstanding_ops \ {"AssignY"}
    /\ y' = 3
    /\ UNCHANGED <<x, pc2>>

Thread1AssignX ==
    /\ "AssignX" \in t1_outstanding_ops
    /\ t1_outstanding_ops' = t1_outstanding_ops \ {"AssignX"}
    /\ x' = 1
    /\ UNCHANGED <<y, pc2>>

Thread2If ==
    /\ pc2 = "BeforeIf"
    /\ IF x = 1 THEN pc2' = "BeforeY" ELSE pc2' = "Stop"
    /\ UNCHANGED <<x, y, t1_outstanding_ops>>

Thread2AssignY ==
    /\ pc2 = "BeforeY"
    /\ pc2' = "Stop"
    /\ y' = 2 * y
    /\ UNCHANGED <<x, t1_outstanding_ops>>

Next ==
    \/ Thread1AssignY
    \/ Thread1AssignX
    \/ Thread2If
    \/ Thread2AssignY

Spec == Init /\ [][Next]_<<x, y, t1_outstanding_ops, pc2>>

----

Correctness ==
    /\ t1_outstanding_ops = {}
    /\ pc2 = "Stop"
    =>
    y \in {3, 6}

=================================

