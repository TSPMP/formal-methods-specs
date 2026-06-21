---- MODULE HwReorderMemHier ----

(*
init x_ram = 0, y_ram = 1, x_t1 = 0, y_t1 = 0, x_t2 = 0, y_t2 = 0

Thread 1
========

Note, that we require StoreYT1 to follow SetYT1 and StoreXT1 follow SetXT1 but
these two sets of instructions can execute independent of each other. This
should be the "read your own writes" guarantee.

SetYT1: y_t1 = 3
StoreYT1: y_ram = y_t1
SetXT1: x_t1 = 1
StoreXT1: x_ram = x_t1

Thread 2
========

LoadXT2: x_t2 = x_ram
T2If: if x_t2 == 1 {
    LoadYT2: y_t2 = y_ram
    SetYT2: y_t2 = y_t2 * 2
    StoreYT2: y_ram = y_t2
}
*)

EXTENDS Integers

VARIABLES state_ram, state_t1, state_t2

StateType == [x: Int, y: Int]
PcT1Type == [x: {"SetXT1", "StoreXT1", "Stop"}, y: {"SetYT1", "StoreYT1", "Stop"}]
T1Type == [local: StateType, pc: PcT1Type]
PcT2Type == {"LoadXT2", "T2If", "LoadYT2", "SetYT2", "StoreYT2", "Stop"}
T2Type == [local: StateType, pc: PcT2Type]

TypeOk ==
    /\ state_ram \in StateType
    /\ state_t1 \in T1Type
    /\ state_t2 \in T2Type

Init ==
    /\ state_ram = [x |-> 0, y |-> 1]
    /\ state_t1 =
        [
            local |-> [x |-> 0, y |-> 0],
            pc |-> [x |-> "SetXT1", y |-> "SetYT1"]
        ]
    /\ state_t2 =
        [
            local |-> [x |-> 0, y |-> 0],
            pc |-> "LoadXT2"
        ]

SetYT1 ==
    /\ state_t1.pc.y = "SetYT1"
    /\ state_t1' = [state_t1 EXCEPT
        !.local = [state_t1.local EXCEPT
            !.y = 3],
        !.pc = [state_t1.pc EXCEPT
            !.y = "StoreYT1"]]
    /\ UNCHANGED <<state_ram, state_t2>>

StoreYT1 ==
    /\ state_t1.pc.y = "StoreYT1"
    /\ state_t1' = [state_t1 EXCEPT
        !.pc = [state_t1.pc EXCEPT
            !.y = "Stop"]]
    /\ state_ram' = [state_ram EXCEPT
        !.y = state_t1.local.y]
    /\ UNCHANGED <<state_t2>>

SetXT1 ==
    /\ state_t1.pc.x = "SetXT1"
    /\ state_t1' = [state_t1 EXCEPT
        !.local = [state_t1.local EXCEPT
            !.x = 1],
        !.pc = [state_t1.pc EXCEPT
            !.x = "StoreXT1"]]
    /\ UNCHANGED <<state_ram, state_t2>>

StoreXT1 ==
    /\ state_t1.pc.x = "StoreXT1"
    /\ state_t1' = [state_t1 EXCEPT
        !.pc = [state_t1.pc EXCEPT
            !.x = "Stop"]]
    /\ state_ram' = [state_ram EXCEPT
        !.x = state_t1.local.x]
    /\ UNCHANGED <<state_t2>>

LoadXT2 ==
    /\ state_t2.pc = "LoadXT2"
    /\ state_t2' = [state_t2 EXCEPT
        !.local = [state_t2.local EXCEPT
            !.x = state_ram.x],
        !.pc = "T2If"]
    /\ UNCHANGED <<state_ram, state_t1>>

T2If ==
    /\ state_t2.pc = "T2If"
    /\ IF state_t2.local.x = 1
        THEN
            state_t2' = [state_t2 EXCEPT !.pc = "LoadYT2"]
        ELSE
            state_t2' = [state_t2 EXCEPT !.pc = "Stop"]
    /\ UNCHANGED <<state_ram, state_t1>> 

LoadYT2 ==
    /\ state_t2.pc = "LoadYT2"
    /\ state_t2' = [state_t2 EXCEPT
        !.local = [state_t2.local EXCEPT
            !.y = state_ram.y],
        !.pc = "SetYT2"]
    /\ UNCHANGED <<state_ram, state_t1>> 

SetYT2 ==
    /\ state_t2.pc = "SetYT2"
    /\ state_t2' = [state_t2 EXCEPT
        !.local = [state_t2.local EXCEPT
            !.y = state_t2.local.y * 2],
        !.pc = "StoreYT2"]
    /\ UNCHANGED <<state_ram, state_t1>> 

StoreYT2 ==
    /\ state_t2.pc = "StoreYT2"
    /\ state_t2' = [state_t2 EXCEPT
        !.pc = "Stop"]
    /\ state_ram' = [state_ram EXCEPT
        !.y = state_t2.local.y]
    /\ UNCHANGED <<state_t1>>

Next ==
    \/ SetYT1
    \/ StoreYT1
    \/ SetXT1
    \/ StoreXT1
    \/ LoadXT2
    \/ T2If
    \/ LoadYT2
    \/ SetYT2
    \/ StoreYT2

Spec == Init /\ [][Next]_<<state_ram, state_t1, state_t2>>

----

Correctness ==
    /\ state_t1.pc.x = "Stop"
    /\ state_t1.pc.y = "Stop"
    /\ state_t2.pc = "Stop"
    =>
    \* Note, that
    \* state_ram.y \in {3, 6}
    \* fails here
    state_ram.y \in {2, 3, 6}

==============================================
