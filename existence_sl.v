From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem simple_large_solution :
  forall (sigma beta : R),
    sigma <> 0 ->
    beta <> 0 ->
    forall (L I : R),
      I = 0 ->
      forall (s m : R),
      s <> 0 ->
      s = sigma * m ->
      (exists (F G M O Q S : R),
           Q = beta
        /\ F = M
        /\ G = F + S + I
        /\ s * S = L + F + G
        /\ m * M = L
        /\ O = F + G
        /\ Q = O / L
      )
      <=>
      (s = 1 + (2 * sigma + 1) / beta) /\ m = s / sigma
Proof.
Qed.
