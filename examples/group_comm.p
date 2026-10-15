% Group axioms do not imply commutativity (smallest counter-model: S3, 6 elements).
fof(assoc, axiom, ![X,Y,Z]: mul(mul(X,Y),Z) = mul(X,mul(Y,Z))).
fof(left_id, axiom, ![X]: mul(e,X) = X).
fof(left_inv, axiom, ![X]: mul(inv(X),X) = e).
fof(comm, conjecture, ![X,Y]: mul(X,Y) = mul(Y,X)).
