% Quoted names that look like variables or internal names stay distinct (regression for TPTP NLP263+1, constant 'T').
fof(names, axiom, (p('X') & p('T') & ~p(c))).
fof(capture, conjecture, ![X]: (p(X) => X = 'X')).
