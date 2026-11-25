From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem simple_large_solution :
  forall (sigma beta : R),
    sigma <> 0 ->
    beta <> 0 ->
    forall (L e' I I' : R),
      L <> 0 ->
      e' >= 0 ->
      I = 0 ->
      I' = 0 ->
      forall (s s' m m' : R),
        s > 0 ->
        s = m * sigma ->
        s' > 0 ->
        s' = m' * sigma ->
        (exists (M M' S S' F F' G G' O O' Od Qd : R),
             Qd = beta
          /\ S' = e'*S
          /\ M' = e'*M
          /\ F = M
          /\ F' = M'
          /\ G = F + S + I
          /\ G' = F' + S' + I'
          /\ s * S + s' * S' = L + F + G
          /\ m * M + m' * M' = L
          /\ O = F + G
          /\ O' = F' + G'
          /\ Od = O + O'
          /\ Qd = Od / L
        )
        <-> s + e'*s' = 1+(2*sigma+1)/beta + e'*(2*sigma+1)/beta
.
Proof.
Qed.
