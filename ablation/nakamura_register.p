% Nakamura's register for Spinoza's Ethics I (spinoza-ethica-lean @ 6d4c046), first-order layer.
% Definitions (Definitions.lean) are role `definition`: they fix what the words mean and are never ablated.
% Axioms: the 8 substantive StatedAxioms fields (Axioms.lean; the 4 `True` placeholders are omitted) and his
% sufficient-reason principles A22 (PSRSubstance), A25 and A26 (PSRPlenitude). Targets are conjectures.
fof(def_substance, definition, ![X]: (substance(X) <=> (inItself(X) & perSeConceived(X)))).
fof(def_attribute, definition, ![A,S]: (attribute(A,S) <=> (substance(S) & intellectPerceivesAsEssence(S,A)))).
fof(def_isGod, definition, ![G]: (isGod(G) <=> (substance(G) & absolutelyInfinite(G) & (?[A]: attribute(A,G)) & (![A]: (attribute(A,G) => expressesEternalEssence(A)))))).
fof(ax1_inItselfOrInAnother, axiom, ![X]: (inItself(X) | inAnother(X))).
fof(ax1_exclusive, axiom, ![X]: ~(inItself(X) & inAnother(X))).
fof(ax2_perSeOrThroughAnother, axiom, ![X]: (perSeConceived(X) | conceivedThroughAnother(X))).
fof(ax7_conceivableAsNonExistent, axiom, ![X]: (~natureRequiresExistence(X) => ~involvesExistence(X))).
fof(ax_inItself_iff_perSeConceived, axiom, ![X]: (inItself(X) <=> perSeConceived(X))).
fof(ax_inAnother_iff_conceivedThroughAnother, axiom, ![X]: (inAnother(X) <=> conceivedThroughAnother(X))).
fof(ax_attribute_perSe, axiom, ![A,S]: (attribute(A,S) => perSeConceived(A))).
fof(ax_causaSui_iff, axiom, ![X]: (involvesExistence(X) <=> natureRequiresExistence(X))).
fof(a22_PSRSubstance, axiom, ![S1,S2]: ((substance(S1) & substance(S2) & S1 != S2) => (?[A]: ((attribute(A,S1) & ~attribute(A,S2)) | (attribute(A,S2) & ~attribute(A,S1)))))).
fof(a25_plenitude, axiom, ![A,S]: ((substance(S) & attribute(A,S)) => (?[G]: (isGod(G) & attribute(A,G))))).
fof(a26_uniqueGod, axiom, ![G1,G2]: ((isGod(G1) & isGod(G2)) => G1 = G2)).
fof(p5_weak, conjecture, ![S1,S2]: ((substance(S1) & substance(S2) & (![A]: (attribute(A,S1) <=> attribute(A,S2)))) => S1 = S2)).
fof(a12_oneSubstancePerAttribute, conjecture, ![S1,S2,A]: ((attribute(A,S1) & attribute(A,S2)) => S1 = S2)).
fof(a15_attributesBelongToGod, conjecture, ![G,S,A]: ((isGod(G) & substance(S) & attribute(A,S)) => attribute(A,G))).
