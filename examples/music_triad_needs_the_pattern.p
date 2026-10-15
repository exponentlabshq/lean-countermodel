% Tonal harmony, minimality: a scale with a tonic, a fifth and some third doesn't make chord I major.
% The major quality comes from the specific offset 4 in the scale pattern (the counter-model is a minor scale).
fof(octave, axiom, ![X]: s(s(s(s(s(s(s(s(s(s(s(s(X)))))))))))) = X).
fof(twelve_notes, axiom, (s(s(s(s(c)))) != c & s(s(s(s(s(s(c)))))) != c)).
fof(tonic, axiom, in(c)).
fof(fifth, axiom, in(s(s(s(s(s(s(s(c))))))))).
fof(some_third, axiom, (in(s(s(s(c)))) | in(s(s(s(s(c))))))).
fof(one_third, axiom, ~(in(s(s(s(c)))) & in(s(s(s(s(c))))))).
fof(chord_I_is_major, conjecture, in(s(s(s(s(c)))))).
