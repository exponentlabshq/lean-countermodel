% Propositional symbols (zero-arity predicates) mixed with first-order ones, as in TPTP NLP165-1.
% Two places; rain or snow; a place is wet iff it rains or it is the river. Does it rain? Not necessarily.
fof(two_places, axiom, river != town).
fof(weather, axiom, rain | snow).
fof(wet, axiom, ![X]: (wet(X) <=> (rain | X = river))).
fof(it_rains, conjecture, rain).
