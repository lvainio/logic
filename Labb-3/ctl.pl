/* Load model, initial state and formula from file */
verify(Input) :- see(Input),
                    read(T), 
                    read(L),
                    read(S),
                    read(F),
                    seen,
                    check(T, L, S, [], F).


/* ----- HELPERS ----- */

/* Receive neighbours to a state */
get_transition(_, [], _) :- fail.
get_transition(S, [[S, X]|_ ], X).
get_transition(S, [_|T], L) :- get_transition(S, T, L).

/* Receive formulas in a state */
get_labeling(_, [], _) :- fail.
get_labeling(S, [[S, X]|_ ], X).
get_labeling(S, [_|T], L) :- get_labeling(S, T, L).

/* Helper for AX */
check_AX(_, _, [], _).
check_AX(T, L, [S|States], F) :- 
    check(T, L, S, [], F), 
    check_AX(T, L, States, F).

/* Helper for EX */
check_EX(_, _, [], _) :- fail.
check_EX(T, L, [S|_], F) :- check(T, L, S, [], F).
check_EX(T, L, [_|States], F) :- check_EX(T, L, States, F).

/* Helper for EF */
check_EF(T, L, [S|_], Visited, F) :- 
    check(T, L, S, Visited, ef(F)).
check_EF(T, L, [_|States], Visited, F) :- 
    check_EF(T, L, States, Visited, F).

/* Helper for AF */
check_AF(T, L, [S|[]], Visited, F) :- 
    check(T, L, S, Visited, af(F)).
check_AF(T, L, [S|States], Visited,  F) :- 
    check(T, L, S, Visited, af(F)),
    check_AF(T, L, States, [S|Visited],  F).

/* Helper for EG. If eg(F) is true in any of s neighbors. */
check_EG(T, L, [S|_], Visited,  F) :- 
    check(T, L, S, Visited, eg(F)).
check_EG(T, L, [S|States], Visited,  F) :- 
    check_EG(T, L, States, [S|Visited], F).

/* Helper for AG. Checks if ag(F) is true in all of S neighbors. */
check_AG(T, L, [S|[]], Visited,  F) :- 
    check(T, L, S, Visited, ag(F)).
check_AG(T, L, [S|States], Visited,  F) :- 
    check(T, L, S, Visited, ag(F)),
    check_AG(T, L, States, [S|Visited],  F).



/* ----- CHECK CTL ----- */

/* Rule p */
check(_, L, S, [], P) :-    
    get_labeling(S, L, Label), 
    memberchk(P, Label).

/* Rule neg(p) */
check(_, L, S, [], neg(P)) :-   
    get_labeling(S, L, Label), 
    \+ memberchk(P, Label).

/* Rule and */
check(T, L, S, [], and(X,Y)) :- 
    check(T, L, S, [], X),
    check(T, L, S, [], Y).

/* Rule or */
check(T, L, S, [], or(X,Y)) :- 
    check(T, L, S, [], X);
    check(T, L, S, [], Y).

/* Rule AX */
check(T, L, S, [], ax(F)) :- 
    get_transition(S, T, Transition),
    check_AX(T, L, Transition, F).

/* Rule EX*/
check(T, L, S, [], ex(F)) :-
    get_transition(S, T, Transition),
    check_EX(T, L, Transition, F).

/* Rule EF1 */
check(T, L, S, Visited, ef(F)) :-
    \+ memberchk(S, Visited),
    check(T, L, S, [], F).

/* Rule EF2 */
check(T, L, S, Visited, ef(F)) :-
    \+ memberchk(S, Visited),
    get_transition(S, T, Neighbors),
    check_EF(T, L, Neighbors, [S|Visited], F).

/* Rule AF1 */
check(T, L, S, Visited, af(F)) :-
    \+ memberchk(S, Visited),
    check(T, L, S, [], F).

/* Rule AF2 */
check(T, L, S, Visited, af(F)) :-
    \+ memberchk(S, Visited),
    get_transition(S, T, Neighbors),
    check_AF(T, L, Neighbors, [S|Visited], F).

/* AG1. */
check(_, _, S, Visited, ag(_)) :-
    memberchk(S, Visited).

/* AG2. */
check(T, L, S, Visited, ag(F)) :- 
    \+  memberchk(S, Visited),
    check(T, L, S,[], F),    
    get_transition(S, T, Neighbors),
    check_AG(T, L, Neighbors, [S|Visited], F).

/* Rule EG1 */
check(_, _, S, Visited, eg(_)) :-
    memberchk(S, Visited).

/* Rule EG2 */
check(T, L, S, Visited, eg(F)) :-
    \+ memberchk(S, Visited),
    check(T, L, S, [], F),    
    get_transition(S, T, Neighbors),
    check_EG(T, L, Neighbors, [S|Visited], F).