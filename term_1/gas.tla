-------------------------------- MODULE gas --------------------------------

EXTENDS Integers, Sequences, TLC

(** NB: This is introduced for support of multiple burners      **)
(**     in a single biolerplate, though not implemented yet.    **)
burners == {1}
users == {1}

(** NB: These Constants might be defined in model;               **)
(**     Though I decided to place them here for readability sake **)
states == [gas: {0}, ign: 0..1, flm: 0..1]
actions == [pressed: 0..1, turned: 0..1, couple_hot: 0..1]

(********

--algorithm boilerplate {
    variables state \in states,
    prev_state = state,
    coupleMalfunct = 0,
    coupleJitter = 0,
    gasLeak = 0,
    flm = 0,
    gas = 0,
    ign = 0,
    action \in actions;
    
    fair process (user \in users) {
        user_l1:
        while (TRUE){
            with (current_action \in actions){
                action := current_action;
            };
        };
    };
    
\* ASK how to specify liveness properties with pattern matching?
\* In SVA I would write sth like `pressed ##1 turned ##1 ~pressed |-> s_eventually gas & flame & ~ignition
\* Is there a mean to do the same in TLA+?

    fair process (burner \in burners) 
    {
        burner_l1:
        while (TRUE) {
        
            if (coupleMalfunct = 1){
                if (flm = 0) coupleMalfunct := 0;
            };
            else {
                if (prev_state.gas = 0 /\ prev_state.flm = 0 /\ gas = 0 /\ flm = 1) coupleMalfunct := 1;
            };
            
            if (coupleJitter = 1){
                if (flm = 0)  coupleJitter := 0;
            };
            else {
                if (flm = 1 /\ gas = 0)  coupleJitter := 1;
            };
            
            if (gasLeak = 1){
                if (gas = 0)  gasLeak := 0;
            };
            else {
                if (flm = 0 /\ gas = 1 /\ ign = 0)  gasLeak := 1;
            };

            flm := action.couple_hot;
            
            if (action.pressed = 1)
                ign:=1;
            else
                ign:=0;
                
            if (action.pressed = 1 \/ action.couple_hot = 1){
                if (action.turned = 1 /\ coupleMalfunct = 0 /\ coupleJitter = 0) {
                    gas:=1;   
                };
                else {
                    gas := 0;
                };
            }
            else {
                gas := 0;
            };
            
            prev_state  :=  state;
            state       :=  [gas |-> gas, ign |-> ign, flm |-> flm];
        };
    };
}

********)
\* BEGIN TRANSLATION (chksum(pcal) = "293a9" /\ chksum(tla) = "5631f367")
VARIABLES state, prev_state, coupleMalfunct, coupleJitter, gasLeak, flm, gas, 
          ign, action

vars == << state, prev_state, coupleMalfunct, coupleJitter, gasLeak, flm, gas, 
           ign, action >>

ProcSet == (users) \cup (burners)

Init == (* Global variables *)
        /\ state \in states
        /\ prev_state = state
        /\ coupleMalfunct = 0
        /\ coupleJitter = 0
        /\ gasLeak = 0
        /\ flm = 0
        /\ gas = 0
        /\ ign = 0
        /\ action \in actions

user(self) == /\ \E current_action \in actions:
                   action' = current_action
              /\ UNCHANGED << state, prev_state, coupleMalfunct, coupleJitter, 
                              gasLeak, flm, gas, ign >>

burner(self) == /\ IF coupleMalfunct = 1
                      THEN /\ IF flm = 0
                                 THEN /\ coupleMalfunct' = 0
                                 ELSE /\ TRUE
                                      /\ UNCHANGED coupleMalfunct
                      ELSE /\ IF prev_state.gas = 0 /\ prev_state.flm = 0 /\ gas = 0 /\ flm = 1
                                 THEN /\ coupleMalfunct' = 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED coupleMalfunct
                /\ IF coupleJitter = 1
                      THEN /\ IF flm = 0
                                 THEN /\ coupleJitter' = 0
                                 ELSE /\ TRUE
                                      /\ UNCHANGED coupleJitter
                      ELSE /\ IF flm = 1 /\ gas = 0
                                 THEN /\ coupleJitter' = 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED coupleJitter
                /\ IF gasLeak = 1
                      THEN /\ IF gas = 0
                                 THEN /\ gasLeak' = 0
                                 ELSE /\ TRUE
                                      /\ UNCHANGED gasLeak
                      ELSE /\ IF flm = 0 /\ gas = 1 /\ ign = 0
                                 THEN /\ gasLeak' = 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED gasLeak
                /\ flm' = action.couple_hot
                /\ IF action.pressed = 1
                      THEN /\ ign' = 1
                      ELSE /\ ign' = 0
                /\ IF action.pressed = 1 \/ action.couple_hot = 1
                      THEN /\ IF action.turned = 1 /\ coupleMalfunct' = 0 /\ coupleJitter' = 0
                                 THEN /\ gas' = 1
                                 ELSE /\ gas' = 0
                      ELSE /\ gas' = 0
                /\ prev_state' = state
                /\ state' = [gas |-> gas', ign |-> ign', flm |-> flm']
                /\ UNCHANGED action

Next == (\E self \in users: user(self))
           \/ (\E self \in burners: burner(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in users : WF_vars(user(self))
        /\ \A self \in burners : WF_vars(burner(self))

\* END TRANSLATION 

safety_noLeak_ign == (state.gas = 1 => state.ign = 1)
safety_noLeak_flm == <>[][state.gas = 1 => state'.flm = 1]_state
safety_noLeak == safety_noLeak_ign \/ safety_noLeak_flm
safety_coupleMalfunct == (coupleJitter = 1 => state.gas = 0)
safety_coupleJitter == (coupleJitter = 1 => state.gas = 0)
satefy_noIgnAtLeak == (gasLeak = 1 => state.ign = 0)

=================================================================
