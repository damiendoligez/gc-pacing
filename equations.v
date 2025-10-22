From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem simple_large :
  forall (F G I L M O Q S m s sigma : R) ,
    s = m * sigma ->
    I = 0 ->
    Q = O / L ->
    O = F + G ->
    G = F + S + I ->
    F = M ->
    s * S = L + F + G ->
    m * M = L ->
    L <> 0 ->
    s <> 0 ->
    Q <> 0 ->
  s = 1 + (2 * sigma + 1) / Q.
Proof.
intros.
subst I G F.
replace (L + M + (M+S+0)) with (L + 2*M + S) in H5 by ring.
assert (m * M * sigma = L * sigma) by congruence. clear H6.
replace (m * M * sigma) with (m * sigma * M) in H0 by field.
replace (M + (M + S + 0)) with (2*M + S) in H2 by field.
assert (s * S - S = L + 2*M + S - S) by congruence. clear H5.
replace (s * S - S) with (S * (s-1)) in H3 by field.
replace (L + 2*M + S - S) with (L + 2*M) in H3 by field.
rewrite <- H in H0.
subst O.
assert (Q * (s-1) * s = (2 * M + S) / L * (s-1) * s) by congruence. clear H1.
replace ((2 * M + S) / L * (s-1) * s) with ((2 * M * (s-1) + S * (s-1)) / L * s) in H2 by now field.
replace (1+(s-1)) with s in H0 by field.
rewrite H3 in H2. clear H3.
replace (2 * M * (s - 1) + (L + 2 * M)) with (2*(s*M) + L) in H2 by field.
rewrite H0 in H2. clear H0.
replace ((2 * (L * sigma) + L)/L) with (2*sigma + 1) in H2 by now field.
assert (Q * (s-1) = 2 * sigma + 1) by (apply (Rmult_eq_reg_r s); auto). clear H2.
assert (Q * (s - 1) / Q = (2 * sigma + 1) / Q) by congruence. clear H0.
replace (Q * (s - 1) / Q) with (s-1) in H1 by now field.
assert (1 + (s - 1) = 1 + (2 * sigma + 1) / Q) by congruence. clear H1.
exact H0.
Qed.

Theorem simple_small :
  forall (F G I J A L M O Q S m s sigma : R) ,
    s = m * sigma ->
    J = S + I ->
    Q = O / L ->
    O = F + G ->
    A = L + O ->
    G = F + J ->
    F = M ->
    s * S = L + F + G ->
    m * M = L ->
    I >= 0 ->
    s > 0 ->
  A <= s * J.
Proof.
intros.
replace (L + F + G) with (L + (F+G)) in H6 by field.
rewrite <- H2 in H6. clear H2.
rewrite <- H3 in H6. clear H3.
assert (J - I = S + I - I) by congruence. clear H0.
field_simplify in H2.
rewrite <- H2 in H6.
assert (s * I >= 0).
replace 0 with (0 * I) by field.
apply (Rmult_ge_compat_r I s 0); auto.
apply Rgt_ge; auto.
rewrite <- H6; clear H6.
replace (s*(J-I)) with (s*J - s*I) by field.
apply (Rplus_le_reg_pos_r (s*J - s*I) (s*I)); apply Rge_le; auto.
replace (s * J - s * I + s * I) with (s*J) by field.
apply Rge_refl.
Qed.

Theorem custom_large :
  forall (s m s' m' sigma e' I I' M M' S S' F F' G G' L O O' Od Qd sd md : R),
    s = m * sigma ->
    s' = m' * sigma ->
    I = 0 ->
    I' = 0 ->
    M' = e'*M ->
    S' = e'*S ->
    F = M ->
    F' = M' ->
    G = F + S + I ->
    G' = F' + S' + I' ->
    s * S + s' * S' = L + F + G ->
    m * M + m' * M' = L ->
    O = F + G ->
    O' = F' + G' ->
    Od = O + O' ->
    Qd = Od / L ->
    sd = s + e' * s' ->
    md = m + e' * m' ->
    L <> 0 ->
    e' >= 0 ->
    s > 0 ->
    s' > 0 ->
    Qd <> 0 ->
  s + e' * s' = 1 + (1+e')*(2*sigma+1)/Qd.
Proof.
intros.
rewrite <- H15.
assert (sd * Qd = Qd + (1+e')*(2*sigma+1)).
  2:{
    assert (sd * Qd / Qd = (Qd + (1+e')*(2*sigma+1)) / Qd) by congruence.
    field_simplify in H23. rewrite H23. field. auto. auto. auto.
  }
subst I I' F F' G G' M' S' O O' Od Qd.
field_simplify; auto.
apply Rdiv_eq_compat_r.
replace (2 * sd * M * e' + 2 * sd * M + sd * S * e' + sd * S) with ((e'+1)*(2*sd*M+sd*S)) by field.
replace (2 * M * e' + 2 * M + S * e' + S + 2 * e' * L * sigma + e' * L + 2 * L * sigma + L) with
        ((e'+1)*(2*M+S+L*(2*sigma+1))) by field.

assert (e'+1 <> 0).
  assert (e'+1 >= 0+1).
  apply Rplus_ge_compat_r. auto.
  replace (0+1) with 1 in H1 by field.
  assert (e'+1 > 0).
  apply (Rge_gt_trans (e'+1) 1). auto.
    apply Rlt_gt. auto.
    apply Rlt_0_1.
  apply Rgt_not_eq. auto.

apply Rmult_eq_compat_l.

assert (sd = md * sigma).
  subst sd md.
  replace ((m + e' * m') * sigma) with (m * sigma + e' * (m' * sigma)) by field.
  subst s s'.
  auto.
replace (2*sd*M) with (2*(md*M)*sigma) by (rewrite H2; field).

replace (s * S + s' * (e' * S)) with ((s + e' * s') * S) in H9 by field.
rewrite <- H15 in H9.
field_simplify in H9.
replace (m * M + m' * (e' * M)) with ((m + e' * m') * M) in H10 by field.
rewrite <- H16 in H10.

rewrite H10.
rewrite H9.
field_simplify. auto.
Qed.

Theorem custom_small_1 :
  forall (s m s' m' sigma e' I I' M M' S S' F F' G G' L Jd O O' Od beta : R),
    s = m * sigma ->
    s' = m' * sigma ->
    G = F + S + I ->
    G' = F' + S' + I' ->
    F' = M' ->
    F = M ->
    S' = e'*S ->
    I' = e'*I ->
    M' = e'*M ->
    m * M + m' * M' = L ->
    s * S + s' * S' = L + F + G ->
    Jd = S + S' + I + I' ->
    O = F + G ->
    O' = F' + G' ->
    Od = O + O' ->
    s = 1 + (2*sigma+1)/beta ->
    s' = (2*sigma+1)/beta ->
    m' > 0 ->
    sigma > 0 ->
    beta > 0 ->
    e' >= 0 ->
    M >= 0 ->
    L >= 0 ->
    S >= 0 ->
    I >= 0 ->
     Od <= Jd + 2*L/m' <= Jd + beta * L
  /\ Od <= Jd * (2 + 2 * sigma + beta)
  .
Proof.
intros.
assert (Od <= Jd + 2*L/m' <= Jd + beta * L).
{
  subst Od O O' F G F' G'.
  split. {
    replace (M + (M + S + I) + (M' + (M' + S' + I'))) with ((S+S'+I+I')+(2*M+2*M')) by field.
    rewrite <- H10.
    apply Rplus_le_compat_l.
    rewrite <- H8.
    replace (2 * (m * M + m' * M') / m') with (2*M*(m/m') + 2*M').
    2:{
      field. nra.
    }
    assert (2 * M <= 2 * M * (m / m')). 2:{ nra. }
    assert (m/m' > 1). 2:{ nra. }
    assert (m/m' = s/s'). {
      subst s s'.
      replace (m*sigma/(m'*sigma)) with (m/m'). auto.
      field.
      split; nra.
    }
    rewrite H1. clear H1.
    rewrite H14.
    rewrite <- H15.
    assert (s' > 0). nra.
    assert (s' <> 0). nra.
    assert (1+s' > s') by nra.
    assert ((1+s')/s' > s'/s'). apply Rmult_gt_compat_r.
      apply Rinv_pos. auto.
      auto.
      field_simplify in H4; nra; auto.
  }
  {
    assert (2/m' <= beta). 2:{ nra. }
    apply (Rmult_le_reg_r (/ sigma)).
    {
      apply Rinv_0_lt_compat. nra.
    }
    field_simplify; try nra.
    rewrite <- H0.
    rewrite H15.
    replace (2 / ((2 * sigma + 1) / beta)) with (beta / (sigma+1/2)) by (field_simplify; auto; nra).
    apply Rmult_le_compat_l. nra.
    apply Rinv_le_contravar. nra.
    nra.
  }
}
{
  split; auto.
  elim H24; intros; clear H24.
  assert (Od <= Jd + beta * L). { apply (Rle_trans _ (Jd + 2 * L / m')); auto. }
  assert (L <= s * S + s' * S'). { subst F G. nra. }
  assert (s * S + s' * S' <= s * (S + S')). { rewrite H14. rewrite H15. nra. }
  assert (L <= s * (S + S')) by nra.
  assert (I + I' >= 0) by nra.
  assert (s >= 0) by nra.
  assert (L <= s * Jd). { rewrite H10. nra. }
  assert (Od <= Jd + beta * s * Jd) by nra.
  rewrite H14 in H33.
  field_simplify in H33. 2:{ nra. }
  nra.
}
Qed.

Theorem ephe_normal :
  forall (s s' s'' m m' m'' w w' w''
          I I' I'' M M' M'' S S' S'' W W' W''
          F F' F'' G G' O O' Od Qd L L''
          sdd mdd wdd sb wb sigma gamma e' e'' : R),
  s = sigma * m ->
  s' = sigma * m' ->
  I = 0 ->
  I' = 0 ->
  I'' = 0 ->
  M' = e' * M ->
  M'' = e'' * M ->
  S' = e' * S ->
  S'' = e'' * S ->
  W' = e' * W ->
  W'' = e'' * W ->
  F = M + W ->
  F' = M' + W' ->
  F'' = M'' + W'' ->
  G = F + S + I ->
  G' = F' + S' + I' ->
  O = F + G ->
  O' = F' + G' ->
  Od = O + O' ->
  Qd = Od / L ->
  s * S + s' * S' + s'' * S'' = L + F + G ->
  m * M + m' * M' + m'' * M'' = L ->
  w * W + w' * W' + w'' * W'' = L'' + F'' ->
  sdd = s + e' * s' + e'' * s'' ->
  mdd = m + e' * m' + e'' * m'' ->
  wdd = w + e' * w' + e'' * w'' ->
  sb = sdd - 1 ->
  wb = wdd - e'' ->
  mdd = sdd / sigma ->
  wb = 2 * sdd / gamma ->
  gamma <> 0 ->
  sigma <> 0 ->
  e' >= 0 ->
  e'' >= 0 ->
  L <> 0 ->
  s > 0 ->
  s' >= 0 ->
  s'' >= 0 ->
  Qd * sb = (e' + 1) * (1 + 2*sigma + gamma*(L''/L + e'' / mdd)).
Proof.
intros.
subst I I' I'' F F' F'' G G'.
replace (s * S + s' * S' + s'' * S'') with (sdd * S) in H19 by nra.
replace (m * M + m' * M' + m'' * M'') with (mdd * M) in H20 by nra.
replace (w * W + w' * W' + w'' * W'') with (wdd * W) in H21 by nra.
field_simplify in H19.
assert (sb * S = L + 2*M + 2*W) by nra. clear H19.
assert (wb * W = L'' + e'' * M) by nra. clear H21.
field_simplify in H15.
field_simplify in H16.
subst Qd Od O O' M' W' S'.
replace ((2 * M + 2 * W + S + (2 * (e' * M) + 2 * (e' * W) + e' * S)))
  with ((e'+1) * (2*M + 2*W + S)) by nra.
enough ((2 * M + 2 * W + S) / L * sb = (1 + 2 * sigma + gamma * (L''/L + e''/mdd))) by nra.
replace ((2 * M + 2 * W + S) / L * sb)
  with ((2 * sb*M + 2 * sb*W + sb*S) / L) by nra.
rewrite H1.
replace (2 * sb * M + 2 * sb * W + (L + 2 * M + 2 * W))
  with (2 * (sb+1) * M + 2 * (sb+1) * W + L) by nra.
replace (sb+1) with sdd by nra.
assert (sdd = mdd*sigma) by (rewrite H27; field_simplify; auto).
replace (2*sdd*M) with (2*sigma*(mdd*M)) by nra.
assert (2*sdd = wb*gamma) by (rewrite H28; field_simplify; auto).
replace (2*sdd*W) with (gamma*(wb*W)) by nra.

replace ((2 * M + 2 * W + S) / L * sb * (wb*mdd))
  with ((2*(mdd*M)*wb + 2*(wb*W)*mdd + S*wb*mdd)/L*sb) by nra.
rewrite H2.
replace (2 * (L'' + e'' * M) * mdd) with (2 * (L''*mdd + e'' * (mdd*M))) by nra.
assert (mdd <> 0).
{
  rewrite H27.
  assert (/sigma <> 0) by now apply Rinv_neq_0_compat.
  assert (sdd <> 0) by nra.
  nra.
}
replace (e''*M) with (e''*(mdd*M)/mdd) by now field.
rewrite H20.
replace (1 + 2 * sigma + gamma * (L'' / L + e''/mdd))
  with ((L + 2 * sigma * L + gamma * (L'' + e''*L/mdd))/L) by now field.
apply Rmult_eq_compat_r.
nra.
Qed.


Theorem ephe_small :
  forall (S S' S'' I I' I'' M M' M''  W W' W'' J J' e' e'' s s' s'' m m' m'' w w' w''
          sigma gamma F F' F'' G G' O O' Od Qd Jd L L'' beta beta'' sdd mdd wdd x : R),
  S+I = J ->
  S'+I' = J' ->
  M' = e'*M  ->
  M'' = e''*M ->
  I' = e'*I ->
  W' = e'*W ->
  W'' = e''*W ->
  S' = e'*S ->
  S'' = e''*S ->
  s = sigma * m ->
  s' = sigma * m' ->
  s'' = sigma * m'' ->
  w = 2*s/gamma ->
  w' = 2*s'/gamma ->
  w'' = 2*s''/gamma + 1 ->
  F = M + W  ->
  F' = M' + W' ->
  F'' = M'' + W'' ->
  G = F + S + I ->
  G' = F' + S' + I' ->
  O = F + G ->
  O' = F' + G' ->
  Od = O + O' ->
  Jd = S + S' + I + I' ->
  s*S + s'*S' + s''*S'' = L + F + G ->
  m*M + m'*M' + m''*M'' = L ->
  w*W + w'*W' + w''*W'' = L'' + F'' ->
  s = 1 + (2*sigma +1)/beta ->
  s' = (2*sigma+1)/beta ->
  s'' = sigma+1 ->
  gamma = beta'' * (sigma + 1) / beta ->
  sdd = s + e' * s' + e'' * s'' ->
  mdd = m + e' * m' + e'' * m'' ->
  wdd = w + e' * w' + e'' * w'' ->
  sigma > 0 ->
  beta > 0 ->
  beta'' > 0 ->
  e'' >= 0 ->
  e' >= 0 ->
  M >= 0 ->
  L'' >= 0 ->
  L'' <= L ->
  Od <= Jd + (beta + beta'') * L.
Proof.
intros.
assert (sdd * M = sigma * L) as HsddM.
{
  subst sdd s s' s'' M' M''.
  nra.
}

assert (0 < /beta).
{
  assert ( beta * 0 < beta / beta). field_simplify. nra. nra.
  apply (Rmult_lt_reg_l beta); nra.
}

assert (gamma > 0).
{
  subst gamma.
  enough (beta'' * (sigma + 1) / beta * beta > 0 * beta) by nra.
  field_simplify; nra.
}

assert (Od * sdd = Jd * sdd + (e' + 1) * 2 * sigma * L + (e' + 1) * gamma * L'' + (e' + 1) * gamma * e'' * M).
{
  subst Od O O'.
  replace (F + S + I) with (F + (S + I)) in H17 by nra.
  rewrite H in H17.
  replace (F' + S' + I') with (F' + (S'+I')) in H18 by nra.
  rewrite H0 in H18.
  subst M' M'' I' W' W''.
  clear H23.
  replace (m * M + m' * (e' * M) + m'' * (e'' * M)) with ((m + e' * m' + e'' * m'') * M) in H24 by nra.
  rewrite <- H31 in H24.
  replace (w * W + w' * (e' * W) + w'' * (e'' * W)) with ((w + e' * w' + e'' * w'') * W) in H25 by nra.
  rewrite <- H32 in H25.
  subst F G F' G'.
  replace (M + W + (M + W + J) + (e' * M + e' * W + (e' * M + e' * W + J')))
    with ((e' + 1) * (2*M + 2*W + J)) by nra.
  subst F''.
  assert ((wdd - e'')*W = L'' + e''*M) by nra.
  replace (wdd - e'') with (2*sdd/gamma) in H1 by nra.
  replace (2 * sdd / gamma * W) with (2*sdd*W/gamma) in H1 by nra.
  assert (2 * sdd * W /gamma * gamma = (L'' + e'' * M) * gamma) by nra.
  field_simplify in H2. 2: { nra. }
  replace ((e' + 1) * (2 * M + 2 * W + J) * sdd) with ((e' + 1) * 2 * (sdd*M) + (e'+1) * (2 * sdd * W) + (e'+1) *J * sdd) by nra.
  rewrite H2.
  rewrite HsddM.
  nra.
}

clear H4 H5 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H25.

assert (Od * sdd * s'' * (2*sigma+1) = Jd * sdd * s'' * (2*sigma + 1) + (e' + 1) * 2 * sigma * L * s'' * (2*sigma + 1) + (e' + 1) * gamma * L'' * s'' * (2*sigma + 1) + (e' + 1) * gamma * e'' * M * s'' * (2*sigma + 1)) by nra.

replace (s * S + s' * S' + s'' * S'') with (sdd * S) in H23 by nra.
replace (m * M + m' * M' + m'' * M'') with (mdd * M) in H24 by nra.

assert (s'' > 0) by nra.

assert (sdd > 0).
{
  subst sdd.
  enough (s + e' * s' + e'' * s'' > 0) by nra.
  assert (s' >= 0). { rewrite H27. nra. }
  assert (s > 0) by nra.
  nra.
}

assert (s' > 0) by nra.
assert (s > 0) by nra.

assert (e'' * s'' <= sigma *mdd) by nra.

assert ((e'+1)*gamma*(e''*M*s'') <= (e'+1)*gamma*(sigma*L)).
{
  assert (M*e''*s'' <= M*mdd*sigma). nra.
  apply (Rmult_le_compat_l ((e'+1)*gamma)). nra.
  nra.
}

assert (Od * sdd * s'' * (2*sigma+1) <= Jd * sdd *s'' * (2*sigma+1) + (e' + 1) * 2 * sigma * L *s''*(2*sigma+1)+ (e' + 1) * gamma * L''*s''*(2*sigma+1) + (e' + 1) * gamma * sigma * L *(2*sigma+1)) by nra.
replace ((e' + 1) * gamma * sigma * L / s'') with ((e'+1) * L * sigma * beta''/beta) in H16.
2: {
  subst gamma.
  rewrite H28.
  field_simplify; nra.
}

assert ((e'+1) * (2*sigma+1) <= beta * sdd).
{
  subst sdd.
  assert (2 * sigma + 1 > 0) by nra.
  assert (e'' * s'' >= 0) by nra.
  enough ((e'+1) * (2*sigma+1) <= beta * (s + e'*s')) by nra.
  rewrite H26. rewrite H27.
  field_simplify; nra.
}

assert (Od * sdd * s'' * (2 * sigma + 1) <=
        Jd * sdd * s'' * (2 * sigma + 1) +
        2 * sigma * L * s'' * beta * sdd +
        gamma * L'' * s'' * beta * sdd +
        gamma * sigma * L * beta * sdd).
{
  assert ((e' + 1) * 2 * sigma * L * s'' * (2 * sigma + 1) <= 2 * sigma * L * s'' * (beta * sdd)).
  {
    replace ((e' + 1) * 2 * sigma * L * s'' * (2 * sigma + 1))
       with (2 * sigma * L * s'' * ((e'+1)*(2*sigma+1))) by nra.
    assert (2*sigma*L*s'' >= 0 * sigma * L * s'').
    apply (Rmult_ge_compat_r); nra.
    nra.
  }
  assert ((e' + 1) * gamma * L'' * s'' * (2 * sigma + 1) <= gamma * L'' * s'' * (beta * sdd)).
  {
    replace ((e' + 1) * gamma * L'' * s'' * (2 * sigma + 1))
      with (gamma * L'' * s'' * ((e'+1)*(2*sigma+1))) by nra.
    assert (gamma * L'' * s'' >= 0 * gamma * L'' * s'').
    apply (Rmult_ge_compat_r); nra.
    nra.
  }
  nra.
}

assert (gamma * beta = beta'' * s'').
{
  assert (gamma * beta = beta'' * s'' / beta * beta) by nra.
  field_simplify in H19; nra.
}

replace (gamma * sigma * L * beta * sdd)
   with (gamma * beta * sigma * L * sdd) in H18 by nra.
rewrite H19 in H18.

replace (gamma * L'' * s'' * beta * sdd)
  with (beta'' * (sigma + 1) * L'' * s'' * sdd) in H18.
  2:{
    replace (gamma * L'' * s'' * beta * sdd)
       with (gamma * beta * L'' * s'' * sdd) by nra.
    rewrite H19.
    nra.
  }

assert (beta'' * (sigma + 1) * s'' * sdd >= 0).
{
  assert (beta'' * (sigma + 1) * s'' * sdd >= 0 * (sigma +1) * s'' * sdd).
  {
    apply (Rmult_ge_compat_r sdd). nra.
    apply (Rmult_ge_compat_r s''). nra.
    apply (Rmult_ge_compat_r (sigma + 1)). nra.
    nra.
  }
  field_simplify in H20.
  field_simplify.
  auto.
}

assert (beta'' * (sigma + 1) * L'' * s'' * sdd <= beta'' * sdd * s'' * (sigma + 1) * L) by nra.

assert (Od * sdd * s'' * (2 * sigma + 1) <=
  Jd * sdd * s'' * (2 * sigma + 1) +
  2 * sigma * L * s'' * beta * sdd +
  beta'' * sdd * s'' * (sigma + 1) * L +
  beta'' * s'' * sigma * L * sdd) by nra.
clear H18.

assert (Od * sdd * s'' * (2 * sigma + 1) <=
  Jd * sdd * s'' * (2 * sigma + 1) +
  2 * sigma * L * s'' * beta * sdd +
  beta'' * L * sdd * s'' * (2*sigma + 1)) by nra.
clear H25.

assert (2 * sigma * L * s'' * beta * sdd <= (2 * sigma + 1) * L * s'' * beta * sdd).
{
  apply (Rmult_le_compat_r). nra.
  apply (Rmult_le_compat_r). nra.
  apply (Rmult_le_compat_r). nra.
  apply (Rmult_le_compat_r). nra.
  nra.
}

replace ((2 * sigma + 1) * L * s'' * beta * sdd)
   with (beta * L * sdd * s'' * (2 * sigma + 1)) in H25 by nra.

assert (Od * sdd * s'' * (2 * sigma + 1) <=
  Jd * sdd * s'' * (2 * sigma + 1) +
  beta * L * sdd * s'' * (2 * sigma + 1) +
  beta'' * L * sdd * s'' * (2*sigma + 1)) by nra.
clear H18.

replace (Jd * sdd * s'' * (2 * sigma + 1) +
         beta * L * sdd * s'' * (2 * sigma + 1) +
         beta'' * L * sdd * s'' * (2 * sigma + 1))
   with ((Jd + (beta + beta'') * L) * sdd * s'' * (2*sigma+1)) in H44 by nra.

apply (Rmult_le_reg_r sdd). nra.
apply (Rmult_le_reg_r s''). nra.
apply (Rmult_le_reg_r (2*sigma+1)). nra.
auto.
Qed.
