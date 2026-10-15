% Nakamura (2026) S-A12: A12 is not provable from StatedAxioms + PSRSubstance (A22). His hand-built model: 4 elements.
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
fof(a22, axiom, ![S1,S2]: ((substance(S1) & substance(S2) & S1 != S2) => (?[A]: ((attribute(A,S1) & ~attribute(A,S2)) | (attribute(A,S2) & ~attribute(A,S1)))))).
fof(a12, conjecture, ![S1,S2,A]: ((attribute(A,S1) & attribute(A,S2)) => S1 = S2)).
