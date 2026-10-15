% Ethics II P7: without b1 (every other bridge granted), the parallelism fails.
fof(a4, axiom, ![C,E]: (cause(C,E) => conceivedThrough(E,C))).
fof(a4c, axiom, ![C,E]: (conceivedThrough(E,C) => cause(C,E))).
fof(b1c, axiom, ![E,C,IE,IC]: ((conceivedThrough(IE,IC) & ideaOf(IE,E) & ideaOf(IC,C)) => conceivedThrough(E,C))).
fof(b2, axiom, ![I,J]: ((isIdea(I) & isIdea(J) & conceivedThrough(I,J)) => cause(J,I))).
fof(b2c, axiom, ![I,J]: ((isIdea(I) & isIdea(J) & cause(J,I)) => conceivedThrough(I,J))).
fof(ideas, axiom, ![I,X]: (ideaOf(I,X) => isIdea(I))).
fof(p7_things_to_ideas, conjecture, ![I,J,X,Y]: ((ideaOf(I,X) & ideaOf(J,Y) & cause(X,Y)) => cause(I,J))).
