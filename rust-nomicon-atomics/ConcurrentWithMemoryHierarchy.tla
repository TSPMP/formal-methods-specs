---- MODULE ConcurrentWithMemoryHierarchy ----

(*
init x_ram = 0, y_ram = 1, x_t1 = 0, y_t1 = 0, x_t2 = 0, y_t2 = 0

Thread 1
========

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
PcT1Type == {"SetYT1", "StoreYT1", "SetXT1", "StoreXT1", "Stop"}
T1Type == [local: StateType, pc: PcT1Type]
PcT2Type == {"LoadXT2", "T2If", "LoadYT2", "SetYT2", "StoreYT2", "Stop"}
T2Type == [local: StateType, pc: PcT2Type]

TypeOk ==
    /\ state_ram \in StateType
    /\ state_t1 \in T1Type
    /\ state_t2 \in T2Type

Init ==
    /\ state_ram = [x |-> 0, y |-> 1]

Next == UNCHANGED <<state_ram, state_t1, state_t2>>

Spec == Init /\ [][Next]_<<state_ram, state_t1, state_t2>>

==============================================
