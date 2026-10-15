% Quoted names may contain %, escaped quotes and capitals; % inside quotes is not a comment,
% and a quoted name is never a variable (regression for TPTP NLP263+1).
fof(sale, axiom, (on_sale('50% off') & said('don\'t') & in('Alps', 'Switzerland'))).
fof(all_on_sale, conjecture, ![X]: on_sale(X)).
