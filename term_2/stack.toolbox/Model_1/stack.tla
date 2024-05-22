--------------------------------- MODULE stack ---------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

elements_num == 6
Status == {"in_stack", "deleted"}

num == 1..elements_num
Prev_v == 0..elements_num
Next_v == 0..elements_num

Elems == [i: num, p: Prev_v, n: Next_v, st: Status]
IsInstack(elem) == "in_stack" \in Status /\ elem.st = "in_stack"
IsDeleted(elem) == "deleted" \in Status /\ elem.st = "deleted"
Initialstack == [i \in num |-> CHOOSE e \in Elems: e.i = i /\ e.p = i - 1 /\ (e.n = i + 1 \/ (e.n = 0 /\ e.i = elements_num))]

(*
--fair algorithm stack
variables
    elems = Initialstack,
    first = 1,
    last = elements_num
define

    ForEach(op(_,_), acc) ==
        LET getelem[i \in num] ==
            IF i = elements_num THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.i + 1])
        IN getelem[1]
    
    ForEach2(op(_,_), acc) ==
        LET getelem[i \in num] ==
            IF i = last THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.n])
        IN getelem[first]
    
    AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
    AllstackElems == ForEach(LAMBDA b, acc: IF IsInstack(b) THEN {b} \union acc ELSE acc, {})
    AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})
    AllInnerstackElems == ForEach(LAMBDA b, acc: IF IsInstack(b) /\ ~(b.i = first) /\ ~(b.i = last) THEN {b} \union acc ELSE acc, {})

    \* invariants
    \*    no n:Node | n in State.deleted and n in State.s.root.*next
        no_deleted == AllDeleted /\ AllstackElems = {}
    \*    no n:Node | n = n.next
        nextNotSelf == \A e \in AllstackElems: ~(e.p = e.n)
    \*    all n:Node | one s:Stack | n in s.root.*next -- by design
    \*    no n:Node | n in n.^next
        nextNotCyclic == \A e \in AllstackElems: (~(e.n = e.i)) /\ (~(e.p = e.i))
        check ==  /\ nextNotSelf /\ nextNotCyclic
end define


macro pop() 
begin
    elems[first].st := "deleted" || elems[elems[first].n].p := 0 || first := elems[first].n || elems[first].n := 0;
end macro;

macro push(e) 
begin
    elems[e.i].st := "in_stack" || elems[last].n := e.i || last := e.i || elems[e.i].p := last;
end macro;

macro push_front(e) 
begin
    elems[e.i].st := "in_stack" || elems[first].p := e.i || first := e.i || elems[e.i].n := first;
end macro;

procedure clear() 
begin
    clear: while Cardinality(AllstackElems) > 2 do
        with e \in AllInnerstackElems do
            elems[e.i].st := "deleted" || elems[e.i].n := 0 || elems[e.i].p := 0 || elems[elems[e.i].p].n := elems[elems[e.i].n].i || elems[elems[e.i].n].p := elems[elems[e.i].p].i;
        end with
    end while
end procedure;

fair process Main \in 1..2 begin
    main_loop:
    either
        pop: if Cardinality(AllstackElems) > 2 then
            pop();
        end if;
    or
        push: if Cardinality(AllDeleted) > 0 then
            with e \in AllDeleted do
                push(e);
            end with;
        end if;
    or
        call clear();
    end either;
    end_main_loop: goto main_loop;
end process;

end algorithm;*)



\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "34c024a4")
\* Label clear of procedure clear at line 74 col 12 changed to clear_
VARIABLES elems, first, last, pc, stack

(* define statement *)
ForEach(op(_,_), acc) ==
    LET getelem[i \in num] ==
        IF i = elements_num THEN op(elems[i], acc)
        ELSE
            LET elem == elems[i]
            IN op(elem, getelem[elem.i + 1])
    IN getelem[1]

ForEach2(op(_,_), acc) ==
    LET getelem[i \in num] ==
        IF i = last THEN op(elems[i], acc)
        ELSE
            LET elem == elems[i]
            IN op(elem, getelem[elem.n])
    IN getelem[first]

AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
AllstackElems == ForEach(LAMBDA b, acc: IF IsInstack(b) THEN {b} \union acc ELSE acc, {})
AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})
AllInnerstackElems == ForEach(LAMBDA b, acc: IF IsInstack(b) /\ ~(b.i = first) /\ ~(b.i = last) THEN {b} \union acc ELSE acc, {})



    no_deleted == AllDeleted /\ AllstackElems = {}

    nextNotSelf == \A e \in AllstackElems: ~(e.p = e.n)


    nextNotCyclic == \A e \in AllstackElems: (~(e.n = e.i)) /\ (~(e.p = e.i))
    check ==  /\ nextNotSelf /\ nextNotCyclic


vars == << elems, first, last, pc, stack >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ elems = Initialstack
        /\ first = 1
        /\ last = elements_num
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "main_loop"]

clear_(self) == /\ pc[self] = "clear_"
                /\ IF Cardinality(AllstackElems) > 2
                      THEN /\ \E e \in AllInnerstackElems:
                                elems' = [elems EXCEPT ![e.i].st = "deleted",
                                                       ![e.i].n = 0,
                                                       ![e.i].p = 0,
                                                       ![elems[e.i].p].n = elems[elems[e.i].n].i,
                                                       ![elems[e.i].n].p = elems[elems[e.i].p].i]
                           /\ pc' = [pc EXCEPT ![self] = "clear_"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                           /\ elems' = elems
                /\ UNCHANGED << first, last, stack >>

clear(self) == clear_(self)

main_loop(self) == /\ pc[self] = "main_loop"
                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "pop"]
                         /\ stack' = stack
                      \/ /\ pc' = [pc EXCEPT ![self] = "push"]
                         /\ stack' = stack
                      \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "clear",
                                                                  pc        |->  "end_main_loop" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "clear_"]
                   /\ UNCHANGED << elems, first, last >>

pop(self) == /\ pc[self] = "pop"
             /\ IF Cardinality(AllstackElems) > 2
                   THEN /\ /\ elems' = [elems EXCEPT ![first].st = "deleted",
                                                     ![elems[first].n].p = 0,
                                                     ![first].n = 0]
                           /\ first' = elems[first].n
                   ELSE /\ TRUE
                        /\ UNCHANGED << elems, first >>
             /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
             /\ UNCHANGED << last, stack >>

push(self) == /\ pc[self] = "push"
              /\ IF Cardinality(AllDeleted) > 0
                    THEN /\ \E e \in AllDeleted:
                              /\ elems' = [elems EXCEPT ![e.i].st = "in_stack",
                                                        ![last].n = e.i,
                                                        ![e.i].p = last]
                              /\ last' = e.i
                    ELSE /\ TRUE
                         /\ UNCHANGED << elems, last >>
              /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
              /\ UNCHANGED << first, stack >>

end_main_loop(self) == /\ pc[self] = "end_main_loop"
                       /\ pc' = [pc EXCEPT ![self] = "main_loop"]
                       /\ UNCHANGED << elems, first, last, stack >>

Main(self) == main_loop(self) \/ pop(self) \/ push(self)
                 \/ end_main_loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: clear(self))
           \/ (\E self \in 1..2: Main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in 1..2 : WF_vars(Main(self)) /\ WF_vars(clear(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
