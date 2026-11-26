From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem simple_large_solution :
  forall (sigma beta : R),
    sigma <> 0 ->
    beta <> 0 ->
    forall (L I : R),
      I = 0 ->
      L <> 0 ->
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
      <-> (s = 1 + (2 * sigma + 1) / beta) /\ m = s / sigma.
Proof.
  intros sigma beta Hsigma Hbeta L I HI HL s m Hs H.
  split.
  - (* Forward direction: the same calculation as simple_large in equations.v. *)
    intros Hx.
    destruct Hx as [F Hf].
    destruct Hf as [G Hg].
    destruct Hg as [M Hm].
    destruct Hm as [O Ho].
    destruct Ho as [Q Hq].
    destruct Hq as [S Hp].
    destruct Hp as [Hqb [H4 [H3 [H5 [H6 [H2 H1]]]]]].
    subst Q I G F.
    replace (L + M + (M+S+0)) with (L + 2*M + S) in H5 by ring.
    assert (m * M * sigma = L * sigma) by congruence.
    clear H6.
    replace (m * M * sigma) with (sigma * m * M) in H0 by field.
    replace (M + (M + S + 0)) with (2*M + S) in H2 by field.
    assert (s * S - S = L + 2*M + S - S) by congruence.
    clear H5.
    replace (s * S - S) with (S * (s-1)) in H3 by field.
    replace (L + 2*M + S - S) with (L + 2*M) in H3 by field.
    rewrite <- H in H0.
    subst O.
    assert (beta * (s-1) * s = (2 * M + S) / L * (s-1) * s) by congruence.
    clear H1.
    replace ((2 * M + S) / L * (s-1) * s) with ((2 * M * (s-1) + S * (s-1)) / L * s) in H2 by now field.
    replace (1+(s-1)) with s in H0 by field.
    rewrite H3 in H2.
    clear H3.
    replace (2 * M * (s - 1) + (L + 2 * M)) with (2*(s*M) + L) in H2 by field.
    rewrite H0 in H2.
    clear H0.
    replace ((2 * (L * sigma) + L)/L) with (2*sigma + 1) in H2 by now field.
    assert (beta * (s-1) = 2 * sigma + 1) by (apply (Rmult_eq_reg_r s); auto).
    clear H2.
    assert (beta * (s - 1) / beta = (2 * sigma + 1) / beta) by congruence.
    clear H0.
    replace (beta * (s - 1) / beta) with (s-1) in H1 by now field.
    assert (1 + (s - 1) = 1 + (2 * sigma + 1) / beta) by congruence.
    clear H1.
    split; [nra | rewrite H; now field].
  - (* Backward direction: give explicit witnesses. *)
    intros Hb.
    destruct Hb as [Hs1 Hm1].
    assert (m <> 0) as Hm0.
    { intros Hc. apply Hs. rewrite H. rewrite Hc. ring. }
    exists (L / m).
    exists (L / m + (beta * L - 2 * L / m) + I).
    exists (L / m).
    exists ((L / m) + (L / m + (beta * L - 2 * L / m) + I)).
    exists beta.
    exists (beta * L - 2 * L / m).
    repeat split.
    + (* s * S = L + F + G *)
      subst I.
      replace (L + L / m + (L / m + (beta * L - 2 * L / m) + 0)) with (L + beta * L) by (now field).
      assert (s * beta = beta + 2 * sigma + 1) as Hs1b.
      { rewrite Hs1. now field. }
      replace (s * (beta * L - 2 * L / m)) with (sigma * m * (beta * L - 2 * L / m)) by (rewrite H; nra).
      replace (sigma * m * (beta * L - 2 * L / m)) with (sigma * beta * L * m - 2 * sigma * L) by (now field).
      replace (sigma * beta * L * m) with (s * beta * L) by (rewrite H; ring).
      rewrite Hs1b.
      ring.
    + (* m * M = L *)
      now field.
    + (* Q = O / L *)
      subst I.
      now field.
Qed.

Theorem simple_large_solution_2 :
  forall (sigma beta : R),
    sigma <> 0 ->
    beta <> 0 ->
    forall (s m : R),
      (   s = 1 + 2 * (sigma + 1) / beta
       /\ m = s / sigma )
      <->
      forall (L : R),
        L <> 0 ->
        (exists (F G M O Q S I : R),
             Q = beta
          /\ I = 0
          /\ F = M
          /\ G = F + S + I
          /\ s * S = L + F + G
          /\ m * M = L
          /\ O = F + G
          /\ Q = O / L
        )
.
Proof.
Qed.
