From Stdlib Require Import Reals.
From Stdlib Require Import Psatz.
Open Scope R_scope.

Theorem simple_large :
  forall (F G I L M O Q S m s sigma beta : R) ,
    Q = beta ->
    s = sigma * m ->
    I = 0 ->
    F = M ->
    G = F + S + I ->
    s * S = L + F + G ->
    m * M = L ->
    O = F + G ->
    Q = O / L ->
    L <> 0 ->
    s <> 0 ->
    beta <> 0 ->
    sigma <> 0 ->
  s = 1 + (2 * sigma + 1) / beta
  /\ m = s / sigma.
Proof.
intros F G I L M O Q S m s sigma beta Hqb H H0 H4 H3 H5 H6 H2 H1.
intros.
subst Q I G F.
replace (L + M + (M+S+0)) with (L + 2*M + S) in H5 by ring.
assert (m * M * sigma = L * sigma) by congruence. clear H6.
replace (m * M * sigma) with (sigma * m * M) in H0 by field.
replace (M + (M + S + 0)) with (2*M + S) in H2 by field.
assert (s * S - S = L + 2*M + S - S) by congruence. clear H5.
replace (s * S - S) with (S * (s-1)) in H3 by field.
replace (L + 2*M + S - S) with (L + 2*M) in H3 by field.
rewrite <- H in H0.
subst O.
assert (beta * (s-1) * s = (2 * M + S) / L * (s-1) * s) by congruence. clear H1.
replace ((2 * M + S) / L * (s-1) * s) with ((2 * M * (s-1) + S * (s-1)) / L * s) in H2 by now field.
replace (1+(s-1)) with s in H0 by field.
rewrite H3 in H2. clear H3.
replace (2 * M * (s - 1) + (L + 2 * M)) with (2*(s*M) + L) in H2 by field.
rewrite H0 in H2. clear H0.
replace ((2 * (L * sigma) + L)/L) with (2*sigma + 1) in H2 by now field.
assert (beta * (s-1) = 2 * sigma + 1) by (apply (Rmult_eq_reg_r s); auto). clear H2.
assert (beta * (s - 1) / beta = (2 * sigma + 1) / beta) by congruence. clear H0.
replace (beta * (s - 1) / beta) with (s-1) in H1 by now field.
assert (1 + (s - 1) = 1 + (2 * sigma + 1) / beta) by congruence. clear H1.
split; [nra | rewrite H; now field].
Qed.

Theorem simple_small :
  forall (F G I J A L M O Q S m s sigma beta : R) ,
    Q = beta ->
    s = m * sigma ->
    J = S + I ->
    F = M ->
    G = F + J ->
    s * S = L + F + G ->
    m * M = L ->
    O = F + G ->
    Q = O / L ->
    A = L + O ->
    I >= 0 ->
    s > 0 ->
     A = s * J - s * I
  /\ A <= s * J.
Proof.
intros F G I J A L M O Q S m s sigma beta Hqb H H0 H5 H4 H6 H7 H2 H1 H3.
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
split. auto.
apply (Rplus_le_reg_pos_r (s*J - s*I) (s*I)); apply Rge_le; auto.
replace (s * J - s * I + s * I) with (s*J) by field.
apply Rge_refl.
Qed.

Theorem custom_large :
  forall (s m s' m' sigma e' I I' M M' S S' F F' G G' L O O' Od Qd sd md beta : R),
    Qd = beta ->
    s = m * sigma ->
    s' = m' * sigma ->
    S' = e'*S ->
    I = 0 ->
    I' = 0 ->
    M' = e'*M ->
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
  s + e' * s' = 1 + (e'+1)*(2*sigma+1)/beta.
Proof.
intros s m s' m' sigma e' I I' M M' S S' F F' G G' L O O' Od Qd sd md beta Hbeta H H0 H4 H1 H2 H3.
intros.
subst beta.
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

Theorem custom_small :
  forall (s m s' m' sigma e' I I' M M' S S' F F' G G' L Jd O O' Od beta : R),
    s = m * sigma ->
    s' = m' * sigma ->
    S' = e'*S ->
    Jd = S + S' + I + I' ->
    I' = e'*I ->
    M' = e'*M ->
    F = M ->
    F' = M' ->
    G = F + S + I ->
    G' = F' + S' + I' ->
    s * S + s' * S' = L + F + G ->
    m * M + m' * M' = L ->
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
intros s m s' m' sigma e' I I' M M' S S' F F' G G' L Jd O O' Od beta H H0 H5 H10 H6 H7 H4 H3 H1 H2 H9 H8.
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

Theorem ephe_large :
  forall (s s' s'' m m' m'' w w' w''
          I I' I'' M M' M'' S S' S'' W W' W''
          F F' F'' G G' O O' Od Qd L L''
          sdd mdd wdd sb sigma gamma e' e'' : R),
  s = sigma * m ->
  s' = sigma * m' ->
  s'' = sigma * m'' ->
  S' = e' * S ->
  S'' = e'' * S ->
  I = 0 ->
  I' = 0 ->
  I'' = 0 ->
  M' = e' * M ->
  M'' = e'' * M ->
  W' = e' * W ->
  W'' = e'' * W ->
  F = M + W ->
  F' = M' + W' ->
  F'' = M'' + W'' ->
  G = F + S + I ->
  G' = F' + S' + I' ->
  s * S + s' * S' + s'' * S'' = L + F + G ->
  m * M + m' * M' + m'' * M'' = L ->
  w * W + w' * W' + w'' * W'' = L'' + M'' ->
  O = F + G ->
  O' = F' + G' ->
  Od = O + O' ->
  Qd = Od / L ->
  sdd = s + e' * s' + e'' * s'' ->
  mdd = m + e' * m' + e'' * m'' ->
  wdd = w + e' * w' + e'' * w'' ->
  sb = sdd - 1 ->
  mdd = sdd / sigma ->
  wdd = 2 * sdd / gamma ->
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
intros s s' s'' m m' m'' w w' w''
          I I' I'' M M' M'' S S' S'' W W' W''
          F F' F'' G G' O O' Od Qd L L''
          sdd mdd wdd sb sigma gamma e' e''
       H H0 Hx H6 H7 H1 H2 H3 H4 H5 H8 H9 H10 H11 H12 H13 H14
       H19 H20 H21 H15 H16 H17 H18.
intros.
subst I I' I'' F F' F'' G G'.
replace (s * S + s' * S' + s'' * S'') with (sdd * S) in H19 by nra.
replace (m * M + m' * M' + m'' * M'') with (mdd * M) in H20 by nra.
replace (w * W + w' * W' + w'' * W'') with (wdd * W) in H21 by nra.
field_simplify in H19.
assert (sb * S = L + 2*M + 2*W) by nra. clear H19.
assert (wdd * W = L'' + e'' * M) by nra. clear H21.
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
assert (sdd = mdd*sigma) by (rewrite H26; field_simplify; auto).
replace (2*sdd*M) with (2*sigma*(mdd*M)) by nra.
assert (2*sdd = wdd*gamma) by (rewrite H27; field_simplify; auto).
replace (2*sdd*W) with (gamma*(wdd*W)) by nra.

replace ((2 * M + 2 * W + S) / L * sb * (wdd*mdd))
  with ((2*(mdd*M)*wdd + 2*(wdd*W)*mdd + S*wdd*mdd)/L*sb) by nra.
rewrite H2.
replace (2 * (L'' + e'' * M) * mdd) with (2 * (L''*mdd + e'' * (mdd*M))) by nra.
assert (mdd <> 0).
{
  rewrite H26.
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
  forall (S S' S'' I I' I'' M M' M''  W W' W'' J J' e' e'' s s' m m'
          w w' sigma gamma
          F F' F'' G G' O O' Od Qd Jd L L'' beta beta'' : R),
  s = sigma * m ->
  s' = sigma * m' ->
  w = 2*s/gamma ->
  w' = 2*s'/gamma ->
  S' = e'*S ->
  S'' = e''*S ->
  I' = e'*I ->
  J = S+I ->
  J' = S'+I' ->
  Jd = S + S' + I + I' ->
  M' = e'*M  ->
  M'' = e''*M ->
  W' = e'*W ->
  W'' = e''*W ->
  F = M + W  ->
  F' = M' + W' ->
  F'' = M'' + W'' ->
  G = F + S + I ->
  G' = F' + S' + I' ->
  O = F + G ->
  O' = F' + G' ->
  Od = O + O' ->
  s*S + s'*S' = L + F + G ->
  m*M + m'*M' = L ->
  w*W + w'*W' = L'' + M'' ->
  s = 1 + (2*sigma +1)/beta ->
  s' = (2*sigma+1)/beta ->
  gamma = beta'' * (sigma + 1) * m / beta / (m+1) ->
  sigma > 0 ->
  beta > 0 ->
  beta'' > 0 ->
  e'' >= 0 ->
  e'' <= 1 ->
  e' >= 0 ->
  M >= 0 ->
  L'' >= 0 ->
  L'' <= L ->
  Od <= Jd + (beta + beta'') * L.
Proof.
intros S S' S'' I I' I'' M M' M'' W W' W'' J J' e' e'' s s' m m'
       w w' sigma gamma F F' F'' G G' O O' Od Qd Jd L L'' beta beta''
       Hs Hsp Hw Hwp HSp HSp2 HIp HJ HJp HJd HMp HMp2 HWp HWp2
       HF HFp HFp2 HG HGp HO HOp HHOd HsS HmM HwW Hs2 Hsp2 Hgamma
       Hsig Hbeta Hb2a Hep2 He2l Hep HM HLp2 HLp2leL.
intros.

(* s + e'*s' > 0, L >= 0, m > 0 *)
assert ((2*sigma + 1)/beta > 0) as Hpos1.
{ apply (Rdiv_pos_pos (2*sigma+1) beta); [nra | nra]. }
assert (s > 0) as Hspos.
{ rewrite Hs2. nra. }
assert (s' > 0) as Hsp2pos.
{ rewrite Hsp2. nra. }
assert (s + e' * s' > 0) as Hsd.
{ nra. }
assert (L >= 0) as HL.
{ nra. }
assert (m > 0) as Hmpos.
{
  assert (m = s/sigma) as Hmeq.
  { rewrite Hs. field_simplify; nra. }
  replace (m) with (s/sigma) by (now symmetry).
  apply (Rdiv_pos_pos s sigma); [nra | nra].
}
assert (gamma > 0) as Hgpos.
{
  rewrite Hgamma.
  apply (Rdiv_pos_pos (beta''*(sigma+1)*m/beta) (m+1)).
  { apply (Rdiv_pos_pos (beta''*(sigma+1)*m) beta); [nra | nra]. }
  nra.
}
assert (m' > 0) as Hmppos.
{
  assert (m' = s'/sigma) as Hmpeq.
  { rewrite Hsp. field_simplify; nra. }
  replace (m') with (s'/sigma) by (now symmetry).
  apply (Rdiv_pos_pos s' sigma); [nra | nra].
}

(* Core identity: Od*(s+e's') = Jd*(s+e's') + (e'+1)*(2σL + γL'' + γe''M) *)
assert (Od * (s + e' * s') = Jd * (s + e' * s') + (e' + 1) * 2 * sigma * L + (e' + 1) * gamma * L'' + (e' + 1) * gamma * e'' * M) as Hkey.
{
  assert (Od = (e' + 1) * (2*M + 2*W + S + I)) as HOd.
  { subst Od O O' F F' G G'. rewrite HMp. rewrite HWp. rewrite HSp. rewrite HIp. nra. }
  assert (Jd = (e' + 1) * (S + I)) as HJd2.
  { rewrite HJd; rewrite HSp; rewrite HIp; nra. }
  assert ((m + e' * m') * M = L) as HmM2.
  { rewrite <- HmM; rewrite HMp; nra. }
  assert ((m + e' * m') * sigma = s + e' * s') as Hsds.
  { rewrite Hs; rewrite Hsp; nra. }
  assert ((w + e' * w') * W = L'' + e'' * M) as HwW2.
  { rewrite <- HMp2; rewrite <- HwW; rewrite HWp; nra. }
  assert (w * gamma = 2 * s) as Hwg.
  { rewrite Hw; field; nra. }
  assert (w' * gamma = 2 * s') as Hwpg.
  { rewrite Hwp; field; nra. }
  assert (2 * M * (s + e' * s') = 2 * sigma * L) as H2M.
  { rewrite <- Hsds; nra. }
  assert (2 * W * (s + e' * s') = gamma * (L'' + e'' * M)) as H2W.
  { nra. }
  nra.
}

(* (e'+1)*2σL <= βL(s+e's')  -- since (e'+1)*2σ <= β + (e'+1)(2σ+1) *)
assert ((e' + 1) * 2 * sigma * L <= beta * L * (s + e' * s')) as HA.
{
  assert ((e' + 1) * 2 * sigma <= beta * (s + e' * s')) as HHA.
  { rewrite Hs2; rewrite Hsp2; field_simplify; nra. }
  nra.
}

(* (e'+1)*γ(L''+e''M) <= β''L(s+e's')  -- using L''<=L, e''<=1, M*m<=L,
   and (e'+1)(σ+1) <= β(s+e's') *)
assert ((e' + 1) * gamma * (L'' + e'' * M) <= beta'' * L * (s + e' * s')) as HBC.
{
  (* (e'+1)*γ(L''+e''M) <= (e'+1)*γ(L+M)  [L''<=L, e''<=1, M>=0] *)
  assert ((e' + 1) * gamma * (L'' + e'' * M) <= (e' + 1) * gamma * (L + M)) as Ht.
  {
    apply (Rmult_le_compat_l ((e' + 1) * gamma)). 2: { nra. }
    nra.
  }
  (* M*m <= L  [from M(m+e'm')=L and m <= m+e'm'] *)
  assert (M * (m + e' * m') = L) as HmM3.
  { nra. }
  assert (M * m <= M * (m + e' * m')) as HmLa.
  { apply (Rmult_le_compat_l M). 2: { nra. } nra. }
  assert (M * m <= L) as HmL.
  { rewrite HmM3 in HmLa. exact HmLa. }
  (* (e'+1)*γ(L+M) <= (e'+1)*β''(σ+1)L/β  [γ=β''(σ+1)m/(β(m+1)), M*m<=L] *)
  assert ((e' + 1) * gamma * (L + M) <= (e' + 1) * beta'' * (sigma + 1) * L / beta) as Ht2b.
  {
    assert (m * (L + M) <= L * (m + 1)) as Hcore.
    { nra. }
    assert ((e' + 1) * gamma * (L + M) = (e' + 1) * beta'' * (sigma + 1) / beta / (m + 1) * (m * (L + M))) as HL2.
    { rewrite Hgamma. field. nra. }
    assert ((e' + 1) * beta'' * (sigma + 1) / beta / (m + 1) * (L * (m + 1)) = (e' + 1) * beta'' * (sigma + 1) * L / beta) as HR2.
    { field. nra. }
    assert ((e' + 1) * beta'' * (sigma + 1) / beta / (m + 1) * (m * (L + M)) <= (e' + 1) * beta'' * (sigma + 1) / beta / (m + 1) * (L * (m + 1))) as Hmid.
    { apply (Rmult_le_compat_l ((e' + 1) * beta'' * (sigma + 1) / beta / (m + 1))). 1: { nra. } exact Hcore. }
    rewrite HL2; rewrite <- HR2; exact Hmid.
  }
  (* (e'+1)*β''(σ+1)L/β <= β''L(s+e's')  [(e'+1)(σ+1) <= β(s+e's')] *)
  assert ((e' + 1) * beta'' * (sigma + 1) * L / beta <= beta'' * L * (s + e' * s')) as Ht3.
  {
    assert ((e' + 1) * (sigma + 1) <= beta * (s + e' * s')) as Hineq.
    { rewrite Hs2; rewrite Hsp2; field_simplify; nra. }
    (* Hx: Hineq scaled by (β''L) >= 0, i.e. A <= β*B *)
    assert ((e' + 1) * (sigma + 1) * (beta'' * L) <= beta * (s + e' * s') * (beta'' * L)) as Hx.
    { apply (Rmult_le_compat_r (beta'' * L)). 1: { nra. } exact Hineq. }
    (* goal A/β <= B: turn /β into */β so Rmult_le_compat_r unifies *)
    assert ((e' + 1) * beta'' * (sigma + 1) * L / beta = (e' + 1) * beta'' * (sigma + 1) * L * / beta) as Hrd.
    { field. nra. }
    rewrite Hrd.
    assert ((e' + 1) * beta'' * (sigma + 1) * L * / beta <= beta * (beta'' * L * (s + e' * s')) * / beta) as Hpre.
    { apply (Rmult_le_compat_r (/ beta)). 1: { nra. } nra. }
    assert (beta * (beta'' * L * (s + e' * s')) * / beta = beta'' * L * (s + e' * s')) as Hbeta1.
    { field. nra. }
    rewrite Hbeta1 in Hpre.
    exact Hpre.
  }
  nra.
}

(* Od <= Jd + (β+β'')L:  from Od*(s+e's') <= (Jd+(β+β'')L)*(s+e's') with s+e's'>0 *)
apply (Rmult_le_reg_r (s + e' * s')).
- nra.
- rewrite Hkey. nra.
Qed.
