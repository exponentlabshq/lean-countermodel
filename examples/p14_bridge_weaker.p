% P14 bridge H (every substance shares an attribute with each god) + A14 + god uniqueness (A26) do not give A15.
% Nakamura's spinoza-ethica-lean @ 6d4c046: definitions (Definitions.lean) and StatedAxioms (Axioms.lean:280).
fof(substance, axiom, ![X]: (substance(X) <=> (inItself(X) & perSeConceived(X)))).
fof(attribute, axiom, ![A,S]: (attribute(A,S) <=> (substance(S) & intellectPerceivesAsEssence(S,A)))).
fof(isGod, axiom, ![G]: (isGod(G) <=> (substance(G) & absolutelyInfinite(G) & (?[A]: attribute(A,G)) & (![A]: (attribute(A,G) => expressesEternalEssence(A)))))).
fof(ax1, axiom, ![X]: (inItself(X) | inAnother(X))).
fof(ax1_exclusive, axiom, ![X]: ~(inItself(X) & inAnother(X))).
fof(ax2, axiom, ![X]: (perSeConceived(X) | conceivedThroughAnother(X))).
fof(ax7, axiom, ![X]: (~natureRequiresExistence(X) => ~involvesExistence(X))).
fof(inItself_iff, axiom, ![X]: (inItself(X) <=> perSeConceived(X))).
fof(inAnother_iff, axiom, ![X]: (inAnother(X) <=> conceivedThroughAnother(X))).
fof(attribute_perSe, axiom, ![A,S]: (attribute(A,S) => perSeConceived(A))).
fof(causaSui_iff, axiom, ![X]: (involvesExistence(X) <=> natureRequiresExistence(X))).
fof(h, axiom, ![G,S]: ((isGod(G) & substance(S)) => (?[A]: (attribute(A,S) & attribute(A,G))))).
fof(a14, axiom, ![S]: (substance(S) => (?[A]: attribute(A,S)))).
fof(a26, axiom, ![G1,G2]: ((isGod(G1) & isGod(G2)) => G1 = G2)).
fof(some_god, axiom, ?[G]: isGod(G)).
fof(a15, conjecture, ![G,S,A]: ((isGod(G) & substance(S) & attribute(A,S)) => attribute(A,G))).
