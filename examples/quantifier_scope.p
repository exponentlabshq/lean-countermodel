% A quantifier whose scope ends before a connective (regression for TPTP SWW883+1).
% TPTP reads `! [X] : A => B` as (∀X A) → B. Extensionality does not make every function equal to c.
fof(extensional, axiom, ![F,G]: (![X]: app(F,X) = app(G,X) => F = G)).
fof(all_c, conjecture, ![F]: F = c).
