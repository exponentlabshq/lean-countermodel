% Tonal harmony, minimality: the circle-of-fifths axioms (a 12-cycle generator, compatible with transposition)
% don't make f the fifth. f = s^7 is a definition, not a consequence: s itself, s^5 and s^11 also qualify.
fof(octave, axiom, ![X]: s(s(s(s(s(s(s(s(s(s(s(s(X)))))))))))) = X).
fof(twelve_notes, axiom, (s(s(s(s(c)))) != c & s(s(s(s(s(s(c)))))) != c)).
fof(f_cycles, axiom, ![X]: f(f(f(f(f(f(f(f(f(f(f(f(X)))))))))))) = X).
fof(f_twelve, axiom, (f(f(f(f(c)))) != c & f(f(f(f(f(f(c)))))) != c)).
fof(f_transposes, axiom, ![X]: f(s(X)) = s(f(X))).
fof(f_is_the_fifth, conjecture, ![X]: f(X) = s(s(s(s(s(s(s(X)))))))).
