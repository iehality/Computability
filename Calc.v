Require Import Lambda.
Require Import Reduction.
Require Import SetoidL.

Opaque equiv.

Definition FALSE := \ \ '0. (* λx. λy. y *)
Definition TRUE  := \ \ '1. (* λx. λy. x *)
Definition AND := \ \ '0 @ '1 @ FALSE.
Definition OR := \ \ '1 @ TRUE @ '0.
Definition NEG := \ '0 @ FALSE @ TRUE.

Fixpoint NAT0 (n0 : nat) :=
  match n0 with
  | 0   => '0
  | S n => '1 @ (NAT0 n)
  end.

Definition NAT n := \ \ (NAT0 n).
Notation "[ n ]" := (NAT n) (at level 0).

Lemma NAT0Normal: forall n, isNormal (NAT0 n).
Proof.
  unfold isNormal.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma NATNormal: forall n, isNormal [n].
Proof.
  intros.
  unfold isNormal, NAT.
  simpl.
  apply NAT0Normal.
Qed.
Hint Resolve NATNormal : core.

Lemma nat_uniqueness : forall l k n,
  (l -->> k) ->
  (l -->> [n]) ->
  (k -->> [n]).
Proof.
  intros.
  apply (uniqueness l _ _ (NATNormal _)).
  auto.
  auto.
Qed.

Lemma NAT0_fv : forall n, fv (NAT0 (S n)) = 2.
Proof.
  induction n.
  simpl. lia.
  change (fv (NAT0 (S (S n)))) 
    with (max (fv '1) (fv (NAT0 (S n)))).
  rewrite IHn.
  simpl. auto.
Qed.

Lemma NAT_fv : forall n, fv [n] = 0.
Proof.
  unfold NAT.
  destruct n.
  simpl. auto.
  change (fv (\ \ NAT0 (S n))) with (pred (pred (fv (NAT0 (S n))))).
  rewrite NAT0_fv.
  simpl. auto.
Qed.

Definition SUCC := \ \ \ '1 @ ('2 @ '1 @ '0).

Lemma NAT_SUCC : forall n, SUCC @ [n] -->> [S n].
Proof.
  unfold SUCC, NAT.
  intros.
  betas.
  reducts.
  beta.
  beta.
  induction n.
  simpl. auto.
  simpl.
  auto.
Qed.

Lemma NAT_SUCC_eq : forall n, SUCC @ [n] == [S n].
Proof.
  intros.
  apply reduct_equiv.
  apply NAT_SUCC.
Qed.

Lemma succ_iterate : forall n l k, [S n] @ l @ k == l @ ([n] @ l @ k).
Proof.
  intros.
  rewrite <- NAT_SUCC_eq.
  unfold SUCC.
  Opaque NAT.
  betaes.
  Transparent NAT.
Qed.

Definition PAIR := \ \ \ '0 @ '2 @ '1.

Lemma PAIR_TRUE : forall l k, PAIR @ l @ k @ TRUE -->> l.
Proof.
  unfold TRUE, PAIR.
  intros.
  betas.
Qed.

Lemma PAIR_TRUE_eq : forall l k, PAIR @ l @ k @ TRUE == l.
Proof.
  intros.
  apply reduct_equiv.
  apply PAIR_TRUE.
Qed.

Lemma PAIR_FALSE : forall l k, PAIR @ l @ k @ FALSE -->> k.
Proof.
  unfold FALSE, PAIR.
  intros.
  betas.
Qed.

Lemma PAIR_FALSE_eq : forall l k, PAIR @ l @ k @ FALSE == k.
Proof.
  intros.
  apply reduct_equiv.
  apply PAIR_FALSE.
Qed.

Lemma PAIR_equiv : forall x y v w,
  (PAIR @ x @ y == PAIR @ v @ w) -> (x == v /\ y == w).
Proof.
  intros.
  split.
  rewrite <- (PAIR_TRUE_eq _ y).
  symmetry.
  rewrite <- (PAIR_TRUE_eq _ w).
  rewrite H.
  reflexivity.
  rewrite <- (PAIR_FALSE_eq x).
  symmetry.
  rewrite <- (PAIR_FALSE_eq v).
  rewrite H.
  reflexivity.
Qed.


Definition ISZERO := \ '0 @ (\ FALSE) @ TRUE.

Lemma ISZERO_0_eq: ISZERO @ [0] == TRUE.
Proof.
  unfold ISZERO, TRUE, FALSE.
  betaes.
Qed.

Lemma ISZERO_Sn_eq : forall n, ISZERO @ [S n] == FALSE.
Proof.
  unfold ISZERO, FALSE.
  intros.
  rewrite <- NAT_SUCC_eq.
  unfold SUCC, TRUE.
  betaes.
Qed.

Definition PRED := \\\ '2 @ (\\ '0 @ ('1 @ '3)) @ (\ '1) @ (\ '0).

Lemma PRED_0_eq : PRED @ [0] == [0].
Proof.
  unfold PRED.
  simpl.
  change [0] with (\ \ '0).
  betaes.
Qed.

Lemma PRED_Sn_eq : forall n, PRED @ [S n] == [n].
Proof.
  induction n.
  unfold PRED.
  change [0] with (\ \ '0).
  change [1] with (\ \ '1 @ '0).
  betaes.
  rewrite <- NAT_SUCC_eq.
  rewrite <- NAT_SUCC_eq at 2.
  rewrite <- NAT_SUCC_eq.
  rewrite <- IHn at 2.
  rewrite <- NAT_SUCC_eq.
  unfold PRED, SUCC.
  Opaque NAT.
  betaes.
  symmetry.
  betaes_all.
Qed.

Definition LE : Lambda := \\ ^^ISZERO @ ('0 @ ^^PRED @ '1).
Definition EQ : Lambda := \\ ^^AND @ (^^LE @ '0 @ '1) @ (^^LE @ '1 @ '0).

Lemma pred_plus_E : forall n m, [n] @ PRED @ [n + m] == [m].
Proof.
    induction n.
    intros.
    change [0] with (\ \ '0).
    betaes.
    intros.
    rewrite succ_iterate.
    assert (S n + m = n + S m). lia.
    rewrite H.
    rewrite IHn.
    apply PRED_Sn_eq.
Qed.

Lemma nle_I_le_E_false : forall n m,
  m < n -> LE @ [n] @ [m] == FALSE.
Proof.
  assert (forall m n, LE @ [n + S m] @ [n] == FALSE).
  {
    unfold LE.
    Opaque PRED.
    Opaque ISZERO.
    intros.
    betae.
    betae.
    rewrite pred_plus_E.
    apply ISZERO_Sn_eq.
  }
  intros.
  assert (n = m + S (n - m - 1)). lia.
  rewrite H1.
  auto.
Qed.

Lemma le_I_le_E_true : forall n m,
  n <= m -> LE @ [n] @ [m] == TRUE.
Proof.
  assert (forall n m, [n + m] @ PRED @ [m] == [0]).
  {
    induction n.
    intros. simpl.
    assert (H := pred_plus_E m 0).
    rewrite Nat.add_0_r in H. auto.
    intros.
    assert (S n + m = S (n + m)). lia.
    rewrite H.
    rewrite succ_iterate.
    rewrite IHn.
    apply PRED_0_eq.
  }
  assert (forall m n, LE @ [n] @ [m + n] == TRUE).
  {
    unfold LE.
    Opaque PRED.
    Opaque ISZERO.
    intros.
    betae.
    betae.
    rewrite H.
    apply ISZERO_0_eq.
    Transparent PRED.
    Transparent ISZERO.
  }
  intros.
  assert (m = (m - n) + n). lia.
  rewrite H2.
  auto.
Qed.

Lemma eq_I_eq_E_true : forall n,
  EQ @ [n] @ [n] == TRUE.
Proof.
  unfold EQ, AND.
  intros.
  Opaque LE.
  betae. betae. betae. betae.
  assert (LE @ [n] @ [n] == TRUE).
  apply le_I_le_E_true. lia.
  rewrite H.
  unfold TRUE.
  betaes.
Qed.

Lemma neq_I_eq_E_true : forall n m,
  n < m -> EQ @ [n] @ [m] == FALSE.
Proof.
  unfold EQ, AND.
  intros.
  Opaque LE.
  betae. betae. betae. betae.
  assert (LE @ [m] @ [n] == FALSE).
  apply nle_I_le_E_false. lia.
  assert (LE @ [n] @ [m] == TRUE).
  apply le_I_le_E_true. lia.
  rewrite H0.
  rewrite H1.
  unfold TRUE, FALSE.
  betaes.
Qed.

Definition CASE := \ \ \ ^^^ISZERO @ '0 @ '2 @ ('1 @ (^^^PRED @ '0)).

Lemma CASE_0_eq : forall x y,
  CASE @ x @ y @ [0] == x.
Proof.
  unfold CASE.
  intros.
  Opaque ISZERO.
  Opaque PRED.
  Opaque NAT.
  betae. betae. betae.
  rewrite ISZERO_0_eq.
  betaes.
  Transparent ISZERO.
  Transparent PRED.
  Transparent NAT.
Qed.

Lemma CASE_Sn_eq : forall x y n,
  CASE @ x @ y @ [S n] == y @ [n].
Proof.
  unfold CASE.
  intros.
  Opaque ISZERO.
  Opaque PRED.
  Opaque NAT.
  betae. betae. betae.
  rewrite ISZERO_Sn_eq.
  rewrite PRED_Sn_eq.
  betaes.
  Transparent ISZERO.
  Transparent PRED.
  Transparent NAT.
Qed.

Definition YC := \ (\ '1 @ ('0 @ '0)) @ (\ '1 @ ('0 @ '0)).

Lemma Yfixpoint : forall x, YC @ x -->> x @ (reduct_l (YC @ x)).
Proof.
  unfold YC.
  simpl.
  intros.
  beta.
  beta.
  auto.
Qed.

Lemma Yfixpoint_eq : forall x, YC @ x == x @ (YC @ x).
Proof.
  intros.
  unfold YC.
  Opaque equiv.
  betae.
  betae.
  reducte.
  symmetry.
  betae.
  reflexivity.
Qed.

Definition mu := \ (YC @ (\ \ ('2 @ '0) @ '0 @ ('1 @ (SUCC @ '0)))) @ [0].

Lemma inductioninv : forall x p, 
  p x -> 
  (forall y, y < x -> p (S y) -> p y) ->
  p 0.
Proof.
  induction x.
  intros. auto.
  intros.
  apply IHx.
  apply X0.
  lia. auto.
  intros.
  apply X0.
  lia. auto.
Qed.

Lemma mu_p : forall n A, 
  (A @ [n] -->> TRUE) -> 
  (forall m, m < n -> (A @ [m] -->> FALSE)) ->
  (mu @ A -->> [n]).
Proof.
  assert(fv YC = 0). simpl. auto.
  assert(fv SUCC = 0). simpl. auto.
  Opaque YC.
  Opaque SUCC.
  Opaque NAT.
  pose(Y A := YC @ (\ \ sf 0 2 A @ ' 0 @ ' 0 @ (' 1 @ (SUCC @ ' 0)))).
  pose (P A n m := (Y A @ [m] -->> [n])).
  assert(forall A n, 
    (A @ [n] -->> TRUE) -> 
    (forall m, m < n -> (A @ [m] -->> FALSE)) ->
    P A n 0).
  - intros.
    apply inductioninv with (x:=n).
    + unfold P, Y.
      apply (reductions_trans _ _ _ (reductions_app0 _ _ _ (Yfixpoint _))).
      fold (Y A).
      beta.
      beta.
      apply (reductions_trans _ _ (TRUE @ [n] @ (reduct_l (Y A) @ (SUCC @ [n])))).
      reducts. auto.
      unfold TRUE.
      betas.
    + unfold P.
      intros.
      unfold Y.
      apply (reductions_trans _ _ _ (reductions_app0 _ _ _ (Yfixpoint _))).
      fold (Y A).
      beta.
      beta.
      apply (reductions_trans _ _ (FALSE @ [y] @ (reduct_l (Y A) @ (SUCC @ [y])))).
      reducts. auto.
      unfold FALSE.
      beta.
      beta.
      apply (reductions_trans _ _ (reduct_l (Y A) @ [S y])).
      reducts. apply NAT_SUCC.
      apply (nat_uniqueness (Y A @ [S y])).
      reducts.
      apply l_reductl.
      auto.
  - intros.
    unfold mu.
    beta.
    fold (Y A).
    apply H1.
    auto.
    auto.
Qed.

Lemma mu_eq : forall n A, 
  (A @ [n] == TRUE) -> 
  (forall m, m < n -> (A @ [m] == FALSE)) ->
  (mu @ A == [n]).
Proof.
  intros.
  apply reduct_equiv.
  apply mu_p.
  apply normal_equiv_reduct.
  unfold TRUE, isNormal. simpl. auto.
  auto.
  intros.
  apply normal_equiv_reduct.
  unfold TRUE, isNormal. simpl. auto.
  auto.
Qed.

Definition DIVERGENT := (\ '0 @ '0) @ (\ '0 @ '0).

Lemma DIVERGENT_reduct : forall l, (DIVERGENT -->> l) -> l = DIVERGENT.
Proof.
  assert (forall l k, (l -->> k) -> l = DIVERGENT -> k = DIVERGENT).
  unfold DIVERGENT.
  intros l k H.
  induction H.
  - inversion H.
    + intros.
      injection H4. intros.
      assert (l0 = k0).
      apply normal_reductions.
      rewrite H6. unfold isNormal. simpl. auto.
      auto.
      assert (m = n).
      apply normal_reductions.
      rewrite H5. unfold isNormal. simpl. auto.
      auto.
      rewrite <- H7. rewrite H6.
      rewrite <- H8. rewrite H5.
      simpl.
      auto.
    + intros.
      discriminate H3.
    + intros.
      injection H4. intros.
      assert (\ '0 @ '0 = k0).
      apply normal_reductions.
      unfold isNormal. simpl. auto.
      rewrite <- H6. auto.
      assert (\ '0 @ '0 = n).
      apply normal_reductions.
      unfold isNormal. simpl. auto.
      rewrite <- H5. auto.
      rewrite <- H7.
      rewrite <- H8.
      auto.
    + auto.
  - auto.
  - intros.
    apply (H DIVERGENT).
    auto.
    auto.
Qed.

Lemma DIVERGENT_divergent : ~ Convergent DIVERGENT.
Proof.
  intro.
  inversion H.
  assert (k = DIVERGENT).
  apply DIVERGENT_reduct. auto.
  rewrite H2 in H0.
  unfold isNormal, DIVERGENT in H0.
  simpl in H0.
  discriminate H0.
Qed.
