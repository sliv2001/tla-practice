-------------------------------- MODULE gas --------------------------------

EXTENDS Integers, Sequences, TLC

(** NB: These Constants might be defined in model;               **)
(**     Though I decided to place them here for readability sake **)
states == [gas: {0}, ign: 0..1, flm: 0..1]
actions == [pressed: 0..1, turned: 0..1, couple_hot: 0..1]

(********

--algorithm boilerplate {
    variables state \in states, 
    gas \in 0..1, 
    ign \in 0..1, 
    flm \in 0..1, 
    prev_state \in states,
    coupleMalfunct = 0,
    coupleJitter = 0,
    gasLeak = 0,
    acts = 0;
    
    fair process (burner \in {1})
    {
        l1: while (TRUE) {
            with (action \in actions){
\*                acts := action;
                prev_state := state;
            
                flm:=action.couple_hot;
                if (action.pressed = 1)
                    ign:=1;
                else
                    ign:=0;
                    
                if (action.pressed = 1 \/ action.couple_hot = 1){
                    if (action.turned = 1 /\ coupleMalfunct = 0 /\ coupleJitter = 0) {
                        gas:=1;   
                    }
                    else {
                        gas := 0;
                    }
                }
                else {
                    gas := 0;
                };
                
                
                if (coupleMalfunct  = 1){
                    if (flm = 0) coupleMalfunct := 0;
                }
                else {
                    if (prev_state.gas = 0 /\ prev_state.flm = 0 /\ gas = 0 /\ flm = 1) coupleMalfunct := 1;
                };
                
                if (coupleJitter = 1){
                    if (flm = 0)  coupleJitter := 0;
                }
                else {
                    if (flm = 1 /\ gas = 0)  coupleJitter := 1;
                };
                
                if (gasLeak = 1){
                    if (gas = 0)  gasLeak := 0;
                }
                else {
                    if (flm = 0 /\ gas = 1 /\ ign = 0)  gasLeak := 1;
                };

                state:=[gas |-> gas, ign |-> ign, flm |-> flm];
        };
    }
    };
    
    
    
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "64048dd9" /\ chksum(tla) = "d334382f")
VARIABLES state, gas, ign, flm, prev_state, coupleMalfunct, coupleJitter, 
          gasLeak, acts

vars == << state, gas, ign, flm, prev_state, coupleMalfunct, coupleJitter, 
           gasLeak, acts >>

ProcSet == ({1})

Init == (* Global variables *)
        /\ state \in states
        /\ gas \in 0..1
        /\ ign \in 0..1
        /\ flm \in 0..1
        /\ prev_state \in states
        /\ coupleMalfunct = 0
        /\ coupleJitter = 0
        /\ gasLeak = 0
        /\ acts = 0

burner(self) == /\ \E action \in actions:
                     /\ prev_state' = state
                     /\ flm' = action.couple_hot
                     /\ IF action.pressed = 1
                           THEN /\ ign' = 1
                           ELSE /\ ign' = 0
                     /\ IF action.pressed = 1 \/ action.couple_hot = 1
                           THEN /\ IF action.turned = 1 /\ coupleMalfunct = 0 /\ coupleJitter = 0
                                      THEN /\ gas' = 1
                                      ELSE /\ gas' = 0
                           ELSE /\ gas' = 0
                     /\ IF coupleMalfunct  = 1
                           THEN /\ IF flm' = 0
                                      THEN /\ coupleMalfunct' = 0
                                      ELSE /\ TRUE
                                           /\ UNCHANGED coupleMalfunct
                           ELSE /\ IF prev_state'.gas = 0 /\ prev_state'.flm = 0 /\ gas' = 0 /\ flm' = 1
                                      THEN /\ coupleMalfunct' = 1
                                      ELSE /\ TRUE
                                           /\ UNCHANGED coupleMalfunct
                     /\ IF coupleJitter = 1
                           THEN /\ IF flm' = 0
                                      THEN /\ coupleJitter' = 0
                                      ELSE /\ TRUE
                                           /\ UNCHANGED coupleJitter
                           ELSE /\ IF flm' = 1 /\ gas' = 0
                                      THEN /\ coupleJitter' = 1
                                      ELSE /\ TRUE
                                           /\ UNCHANGED coupleJitter
                     /\ IF gasLeak = 1
                           THEN /\ IF gas' = 0
                                      THEN /\ gasLeak' = 0
                                      ELSE /\ TRUE
                                           /\ UNCHANGED gasLeak
                           ELSE /\ IF flm' = 0 /\ gas' = 1 /\ ign' = 0
                                      THEN /\ gasLeak' = 1
                                      ELSE /\ TRUE
                                           /\ UNCHANGED gasLeak
                     /\ state' = [gas |-> gas', ign |-> ign', flm |-> flm']
                /\ acts' = acts

Next == (\E self \in {1}: burner(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1} : WF_vars(burner(self))

\* END TRANSLATION 

safety_noLeak_ign == (state.gas = 1 => state.ign = 1)
safety_noLeak_flm == (prev_state.gas = 1 => state.flm = 1)
safety_noLeak == safety_noLeak_ign \/ safety_noLeak_flm
safety_coupleMalfunct == (coupleJitter = 1 => state.gas = 0)
safety_coupleJitter == (coupleJitter = 1 => state.gas = 0)
satefy_noIgnAtLeak == (gasLeak = 1 => state.ign = 0)

liveness_converge == <>(state.gas = 1 /\ state.ign = 0 /\ state.flm = 1)
liveness_reach == [](state.ign = 1 /\ coupleJitter = 0 /\ coupleMalfunct = 0 => <>(state.gas = 1))

=============================================================================
\* Modification History
\* Last modified Sun Nov 19 18:25:18 MSK 2023 by ivans
\* Created Fri Nov 17 21:40:25 MSK 2023 by ivans
