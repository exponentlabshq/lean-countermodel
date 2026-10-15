% Tonal harmony, underdetermination: one pitch-class collection, read as C major and as a natural minor on t,
% does not force t = C. The counter-model puts t a major sixth above C: A minor, the relative minor.
fof(octave, axiom, ![X]: s(s(s(s(s(s(s(s(s(s(s(s(X)))))))))))) = X).
fof(twelve_notes, axiom, (s(s(s(s(c)))) != c & s(s(s(s(s(s(c)))))) != c)).
fof(c_major, axiom, ![X]: (in(X) <=> (X = c | X = s(s(c)) | X = s(s(s(s(c)))) | X = s(s(s(s(s(c))))) | X = s(s(s(s(s(s(s(c))))))) | X = s(s(s(s(s(s(s(s(s(c))))))))) | X = s(s(s(s(s(s(s(s(s(s(s(c)))))))))))))).
fof(t_minor, axiom, ![X]: (in(X) <=> (X = t | X = s(s(t)) | X = s(s(s(t))) | X = s(s(s(s(s(t))))) | X = s(s(s(s(s(s(s(t))))))) | X = s(s(s(s(s(s(s(s(t)))))))) | X = s(s(s(s(s(s(s(s(s(s(t))))))))))))).
fof(tonic_is_c, conjecture, t = c).
