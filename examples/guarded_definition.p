% A guarded definition, the shape of TPTP SWB017+3: ∀Z S (list(S) → (member(Z,S) ↔ good(Z))).
% Miniscoping binds Z after the guard; the consequent must stay parenthesized. Not everything is good.
fof(members_are_good, axiom, ![Z,S]: (list(S) => (member(Z,S) <=> good(Z)))).
fof(a_list, axiom, list(l1)).
fof(all_good, conjecture, ![Z]: good(Z)).
