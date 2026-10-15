% Circle of fifths. f: up a fifth; g: up a fourth. Twelve fifths return home (equal temperament),
% and from C the circle doesn't close after 4 or 6 fifths, so C's orbit has all 12 notes.
% Claim refuted: a fifth up is the same as a fourth up. Known answer: the 12-note cycle, f(x) = x+7 mod 12.
fof(twelve_fifths, axiom, ![X]: f(f(f(f(f(f(f(f(f(f(f(f(X)))))))))))) = X).
fof(not_four, axiom, f(f(f(f(c)))) != c).
fof(not_six, axiom, f(f(f(f(f(f(c)))))) != c).
fof(fourth_undoes_fifth, axiom, ![X]: g(f(X)) = X).
fof(fifth_is_fourth, conjecture, ![X]: f(X) = g(X)).
