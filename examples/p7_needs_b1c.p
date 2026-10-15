% Ethics II P7: without b1c (every other bridge granted), the parallelism fails.
fof(a4, axiom, ![C,E]: (cause(C,E) => conceivedThrough(E,C))).
fof(a4c, axiom, ![C,E]: (conceivedThrough(E,C) => cause(C,E))).
fof(b1, axiom, ![E,C,IE,IC]: ((conceivedThrough(E,C) & ideaOf(IE,E) & ideaOf(IC,C)) => conceivedThrough(IE,IC))).
fof(b2, axiom, ![I,J]: ((isIdea(I) & isIdea(J) & conceivedThrough(I,J)) => cause(J,I))).
fof(b2c, axiom, ![I,J]: ((isIdea(I) & isIdea(J) & cause(J,I)) => conceivedThrough(I,J))).
fof(ideas, axiom, ![I,X]: (ideaOf(I,X) => isIdea(I))).
fof(p7_ideas_to_things, conjecture, ![I,J,X,Y]: ((ideaOf(I,X) & ideaOf(J,Y) & cause(I,J)) => cause(X,Y))).
