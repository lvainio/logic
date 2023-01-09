
/* ----- Program to validate a proof in natural deduction ----- */

/* Read an input file. (example call: verify('valid01.txt').) */
verify(InputFileName) :- see(InputFileName),
                         read(Prems), read(Goal), read(Proof),
                         seen,
                         valid_goal(Proof, Goal),
                         valid_proof(Prems, Proof, []).

/* Check if last line in proof is equal to goal */
valid_goal([Last|[]], Goal) :- memberchk(Goal, Last).
valid_goal([_|T], Goal) :- valid_goal(T, Goal).



/* ----- Boxes ----- */

/* Returns a specified proof box */
get_box( _ , [] , _ ) :- fail.
get_box([Line, Formula, _], [[[Line, Formula, _] | Box_Tail] | _], [[Line, Formula, _] | Box_Tail] ).
get_box([Line, Formula, _],[ _  | Tail ], Box):-
    get_box([Line, Formula, _], Tail , Box).

/* Compare the last element in a box with a line */
get_last([Head | []], Head).
get_last([_ | Tail], Head) :- get_last(Tail, Head).



/* ----- Rules ----- */

/* Base case (no more lines) */
valid_proof(_, [], _).

/* Premise */
valid_proof(Prems, [[Line, Formula, premise]|T], Scope) :-
    memberchk(Formula, Prems),
    valid_proof(Prems, T, [[Line, Formula, premise]|Scope]).

/* Assumption (BOX) */
valid_proof(Prems, [[[Line, Formula,  assumption] | Box_Tail] | T], Scope) :-
    valid_proof(Prems, Box_Tail, [[Line, Formula,  assumption] | Scope]),    
    valid_proof(Prems, T, [[[Line, Formula,  assumption]  | Box_Tail]  | Scope ]).

/* Copy */
valid_proof(Prems, [[Line, Formula, copy(L)]|T], Scope) :-
    memberchk([L, Formula, _], Scope),
    valid_proof(Prems, T, [[Line, Formula, copy]|Scope]). 

/* And introduction */
valid_proof(Prems, [[Line, and(F1, F2), andint(L1, L2)]|T], Scope) :-
    memberchk([L1, F1, _], Scope),
    memberchk([L2, F2, _], Scope),
    valid_proof(Prems, T, [[Line, and(F1, F2), andint(L1, L2)]|Scope]).

/* And elimination 1 */
valid_proof(Prems, [[Line, Formula, andel1(L)]|T], Scope) :-
    memberchk([L, and(Formula, _), _], Scope),
    valid_proof(Prems, T, [[Line, Formula, andel1(L)]|Scope]).

/* And elimination 2 */
valid_proof(Prems, [[Line, Formula, andel2(L)]|T], Scope) :-
    memberchk([L, and(_, Formula), _], Scope),
    valid_proof(Prems, T, [[Line, Formula, andel2(L)]|Scope]).

/* Or introduction 1 */
valid_proof(Prems, [[Line, or(F1, F2), orint1(L)]|T], Scope) :-
    memberchk([L, F1, _], Scope),
    valid_proof(Prems,  T, [[Line, or(F1, F2), orint1(L)] | Scope]).

/* Or introduction 2 */
valid_proof(Prems, [[Line, or(F1, F2), orint2(L)]|T], Scope) :-
    memberchk([L, F2, _], Scope),
    valid_proof(Prems,  T, [[Line, or(F1, F2), orint2(L)] | Scope]).

/* Or elimination */
valid_proof(Prems,  [[Line, Formula,  orel(R, Y, Z, V, W)] | T], Scope) :-
    memberchk([R, or(F1,F2),_], Scope),

    get_box([Y, F1, _], Scope, Box1),
    get_last(Box1, [Z, Formula, _]),

    get_box([V, F2, _], Scope, Box2),
    get_last(Box2, [W, Formula, _]),

    valid_proof(Prems, T, [[Line, Formula,  orel(R,Y, Z, V, W)] | Scope]). 

/* Implication introduction */
valid_proof(Prems, [[Line, imp(F1,F2),  impint(L1,L2)] | Tail], Scope) :-
    get_box([L1, F1, _], Scope, Box),
    get_last(Box, [L2, F2, _] ),
    valid_proof(Prems, Tail, [[Line, imp(F1, F2),  impint(L1,L2)] | Scope]). 

/* Implication elimination  */
valid_proof(Prems, [[Line, Formula,  impel(L1,L2)]|T], Scope) :-
    memberchk([L1, F, _], Scope),
    memberchk([L2, imp(F, Formula), _], Scope),
    valid_proof(Prems, T, [[Line, Formula,  impel(L1,L2)]|Scope]).

/* Not introduction */
valid_proof(Prems,  [[Line, neg(Formula),  negint(L1,L2)] | Tail], Scope) :-
    get_box([L1, Formula, _], Scope, Box),
    get_last(Box, [L2, cont, _]),
    valid_proof(Prems, Tail, [[Line, Formula,  negint(L1,L2)] | Scope]). 

/* Not elimination */
valid_proof(Prems, [[Line, cont,  negel(L1,L2)]|T], Scope) :-
    memberchk([L1, Formula, _], Scope),
    memberchk([L2, neg(Formula), _], Scope),
    valid_proof(Prems, T, [[Line, cont, negel(L1,L2)]|Scope]). 

/* Contradiction elimination */
valid_proof(Prems, [[Line, Formula, contel(L)]|T], Scope) :-
    memberchk([L, cont, _], Scope),
    valid_proof(Prems, T, [[Line, Formula, contel(L)]|Scope]). 

/* NotNot introduction */
valid_proof(Prems, [[Line, neg(neg(Formula)), negnegint(L)]|T], Scope) :-
    memberchk([L, Formula, _], Scope),
    valid_proof(Prems, T, [[Line, neg(neg(Formula)), negnegint(L)]|Scope]). 

/* NotNot elimination */
valid_proof(Prems, [[Line, Formula, negnegel(L)]|T], Scope) :-
    memberchk([L, neg(neg(Formula)), _], Scope),
    valid_proof(Prems, T, [[Line, Formula, negnegel(L)]|Scope]). 

/* MT rule */
valid_proof(Prems, [[Line, neg(F1),  mt(L1,L2)]|T], Scope) :-
    memberchk([L1, imp(F1, F2), _], Scope),
    memberchk([L2, neg(F2), _], Scope),
    valid_proof(Prems, T, [[Line, neg(F1), mt(L1,L2)]|Scope]). 

/* PBC */
valid_proof(Prems, [[Line, Formula,  pbc(L1,L2)] | Tail], Scope) :-
    get_box([L1, neg(Formula), _], Scope, Box),
    get_last(Box, [L2, cont, _]),
    valid_proof(Prems, Tail, [[Line, Formula,  pbc(L1,L2)] | Scope]). 

/* LEM */
valid_proof(Prems, [[Line, or(Formula, neg(Formula)), lem]|T], Scope) :-
    valid_proof(Prems, T, [[Line, or(Formula, neg(Formula)), lem]|Scope]). 


