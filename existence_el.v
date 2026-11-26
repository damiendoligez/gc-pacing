From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem ephe_large_solution :
  forall (beta beta'' sigma gamma : R),
    beta > 0 ->
    beta'' >= 0 ->
    sigma > 0 ->
    gamma > 0 ->
    forall (s s' m m' w w' : R),
      s = 1 + (2 * sigma + 1) / beta ->
      s' = (2 * sigma + 1) / beta ->
      m = s / sigma ->
      m' = s' / sigma ->
      w = 2 * s / gamma ->
      w' = 2 * s' / gamma ->
      forall (L L'' e' e'' : R),
        L <> 0 ->
        e' >= 0 ->
        e'' >= 0 ->
        exists (I I' I'' M M' M'' S S' S'' W W' W''
                F F' F'' G G' O O' Od Qd : R),
           S' = e' * S
        /\ S'' = e'' * S
        /\ I = 0
        /\ I' = 0
        /\ I'' = 0
        /\ M' = e' * M
        /\ M'' = e'' * M
        /\ W' = e' * W
        /\ W'' = e'' * W
        /\ F = M + W
        /\ F' = M' + W'
        /\ F'' = M'' + W''
        /\ G = F + S + I
        /\ G' = F' + S' + I'
        /\ s * S + s' * S' = L + F + G
        /\ m * M + m' * M' = L
        /\ w * W + w' * W' = L'' + M''
        /\ O = F + G
        /\ O' = F' + G'
        /\ Od = O + O'
        /\ Qd = Od / L
        /\ beta <= Qd /\ Qd <= beta + beta''
.
Proof.
Qed.
