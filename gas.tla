-------------------------------- MODULE gas --------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT states, actions
ASSUME states = [gas: {0}, ign: 0..1, flm: 0..1]
ASSUME actions = [pressed: 0..1, turned: 0..1, couple_hot: 0..1]

(********

--algorithm boilerplate {
    variables state \in states, gas \in 0..1, ign \in 0..1, flm \in 0..1;
    {
        while (TRUE) {
            with (action \in actions){
                flm:=action.couple_hot;
                if (action.pressed = 1)
                    ign:=1;
                else
                    ign:=0;
                    
                if (action.pressed = 1 \/ action.couple_hot = 1){
                    if (action.turned = 1) {
                        gas:=1;   
                    }
                    else {
                        gas := 0;
                    }
                }
                else {
                    gas := 0;
                };
                state:=[gas |-> gas, ign |-> ign, flm |-> flm];
            };
        }
    }
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "7b7a9ddf" /\ chksum(tla) = "532c0b0a")
VARIABLES state, gas, ign, flm

vars == << state, gas, ign, flm >>

Init == (* Global variables *)
        /\ state \in states
        /\ gas \in 0..1
        /\ ign \in 0..1
        /\ flm \in 0..1

Next == \E action \in actions:
          /\ flm' = action.couple_hot
          /\ IF action.pressed = 1
                THEN /\ ign' = 1
                ELSE /\ ign' = 0
          /\ IF action.pressed = 1 \/ action.couple_hot = 1
                THEN /\ IF action.turned = 1
                           THEN /\ gas' = 1
                           ELSE /\ gas' = 0
                ELSE /\ gas' = 0
          /\ state' = [gas |-> gas', ign |-> ign', flm |-> flm']

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Nov 18 00:10:25 MSK 2023 by ivans
\* Created Fri Nov 17 21:40:25 MSK 2023 by ivans
