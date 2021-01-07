Require Import Recursion.Lambda.
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

Lemma isNormal_nat0: forall n, isNormal (NAT0 n).
Proof.
  unfold isNormal.
  intros.
  induction n.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma isNormal_NAT : forall n, isNormal [n].
Proof.
  intros.
  unfold isNormal, NAT.
  simpl.
  apply isNormal_nat0.
Qed.
Hint Resolve isNormal_NAT : core.

Lemma nat_uniqueness : forall l k n,
  (l -->> k) ->
  (l -->> [n]) ->
  (k -->> [n]).
Proof.
  intros.
  apply (uniqueness l _ _ (isNormal_NAT _)).
  auto.
  auto.
Qed.

Lemma fv_NAT0_Sn_E_2 : forall n, fv (NAT0 (S n)) = 2.
Proof.
  induction n.
  simpl. lia.
  change (fv (NAT0 (S (S n)))) 
    with (max (fv '1) (fv (NAT0 (S n)))).
  rewrite IHn.
  simpl. auto.
Qed.

Lemma fv_NAT_E_0 : forall n, fv [n] = 0.
Proof.
  unfold NAT.
  destruct n.
  simpl. auto.
  change (fv (\ \ NAT0 (S n))) with (pred (pred (fv (NAT0 (S n))))).
  rewrite fv_NAT0_Sn_E_2.
  simpl. auto.
Qed.

Definition SUCC := \ \ \ '1 @ ('2 @ '1 @ '0).

Lemma SUCC_R_S : forall n, SUCC @ [n] -->> [S n].
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

Lemma SUCC_E_S : forall n, SUCC @ [n] == [S n].
Proof.
  intros.
  apply reduct_equiv.
  apply SUCC_R_S.
Qed.

Lemma succ_iterate : forall n l k, [S n] @ l @ k == l @ ([n] @ l @ k).
Proof.
  intros.
  rewrite <- SUCC_E_S.
  unfold SUCC.
  Opaque NAT.
  betaes.
  Transparent NAT.
Qed.

Definition PAIR := \ \ \ '0 @ '2 @ '1.

Lemma PAIR_TRUE_R : forall l k, PAIR @ l @ k @ TRUE -->> l.
Proof.
  unfold TRUE, PAIR.
  intros.
  betas.
Qed.

Lemma PAIR_TRUE_E : forall l k, PAIR @ l @ k @ TRUE == l.
Proof.
  intros.
  apply reduct_equiv.
  apply PAIR_TRUE_R.
Qed.

Lemma PAIR_FALSE_R : forall l k, PAIR @ l @ k @ FALSE -->> k.
Proof.
  unfold FALSE, PAIR.
  intros.
  betas.
Qed.

Lemma PAIR_FALSE_E : forall l k, PAIR @ l @ k @ FALSE == k.
Proof.
  intros.
  apply reduct_equiv.
  apply PAIR_FALSE_R.
Qed.

Lemma PAIR_injection : forall x y v w,
  (PAIR @ x @ y == PAIR @ v @ w) -> (x == v /\ y == w).
Proof.
  intros.
  split.
  rewrite <- (PAIR_TRUE_E _ y).
  symmetry.
  rewrite <- (PAIR_TRUE_E _ w).
  rewrite H.
  reflexivity.
  rewrite <- (PAIR_FALSE_E x).
  symmetry.
  rewrite <- (PAIR_FALSE_E v).
  rewrite H.
  reflexivity.
Qed.


Definition ISZERO := \ '0 @ (\ FALSE) @ TRUE.

Lemma ISZERO_0_E_TRUE : ISZERO @ [0] == TRUE.
Proof.
  unfold ISZERO, TRUE, FALSE.
  betaes.
Qed.

Lemma ISZERO_Sn_E_FALSE : forall n, ISZERO @ [S n] == FALSE.
Proof.
  unfold ISZERO, FALSE.
  intros.
  rewrite <- SUCC_E_S.
  unfold SUCC, TRUE.
  betaes.
Qed.

Definition PRED := \\\ '2 @ (\\ '0 @ ('1 @ '3)) @ (\ '1) @ (\ '0).

Lemma PRED_0_E_0 : PRED @ [0] == [0].
Proof.
  unfold PRED.
  simpl.
  change [0] with (\ \ '0).
  betaes.
Qed.

Lemma PRED_Sn_E_n : forall n, PRED @ [S n] == [n].
Proof.
  induction n.
  unfold PRED.
  change [0] with (\ \ '0).
  change [1] with (\ \ '1 @ '0).
  betaes.
  rewrite <- SUCC_E_S.
  rewrite <- SUCC_E_S at 2.
  rewrite <- SUCC_E_S.
  rewrite <- IHn at 2.
  rewrite <- SUCC_E_S.
  unfold PRED, SUCC.
  Opaque NAT.
  betaes.
  symmetry.
  betaes_all.
Qed.

Definition LE : Lambda := \\ ^^ISZERO @ ('0 @ ^^PRED @ '1).
Definition EQ : Lambda := \\ ^^AND @ (^^LE @ '0 @ '1) @ (^^LE @ '1 @ '0).

Lemma n_PRED_plus_n_m_E_m : forall n m, [n] @ PRED @ [n + m] == [m].
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
    apply PRED_Sn_E_n.
Qed.

Lemma Nle_I_LE_E_FALSE : forall n m,
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
    rewrite n_PRED_plus_n_m_E_m.
    apply ISZERO_Sn_E_FALSE.
  }
  intros.
  assert (n = m + S (n - m - 1)). lia.
  rewrite H1.
  auto.
Qed.

Lemma le_I_LE_E_TRUE : forall n m,
  n <= m -> LE @ [n] @ [m] == TRUE.
Proof.
  assert (forall n m, [n + m] @ PRED @ [m] == [0]).
  {
    induction n.
    intros. simpl.
    assert (H := n_PRED_plus_n_m_E_m m 0).
    rewrite Nat.add_0_r in H. auto.
    intros.
    assert (S n + m = S (n + m)). lia.
    rewrite H.
    rewrite succ_iterate.
    rewrite IHn.
    apply PRED_0_E_0.
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
    apply ISZERO_0_E_TRUE.
    Transparent PRED.
    Transparent ISZERO.
  }
  intros.
  assert (m = (m - n) + n). lia.
  rewrite H2.
  auto.
Qed.

Lemma EQ_n_n_E_TRUE : forall n,
  EQ @ [n] @ [n] == TRUE.
Proof.
  unfold EQ, AND.
  intros.
  Opaque LE.
  betae. betae. betae. betae.
  assert (LE @ [n] @ [n] == TRUE).
  apply le_I_LE_E_TRUE. lia.
  rewrite H.
  unfold TRUE.
  betaes.
Qed.

Lemma lt_I_EQ_E_FALSE : forall n m,
  n < m -> EQ @ [n] @ [m] == FALSE.
Proof.
  unfold EQ, AND.
  intros.
  Opaque LE.
  betae. betae. betae. betae.
  assert (LE @ [m] @ [n] == FALSE).
  apply Nle_I_LE_E_FALSE. lia.
  assert (LE @ [n] @ [m] == TRUE).
  apply le_I_LE_E_TRUE. lia.
  rewrite H0.
  rewrite H1.
  unfold TRUE, FALSE.
  betaes.
Qed.

Definition CASE := \ \ \ ^^^ISZERO @ '0 @ '2 @ ('1 @ (^^^PRED @ '0)).

Lemma CASE_x_y_0_E_x : forall x y,
  CASE @ x @ y @ [0] == x.
Proof.
  unfold CASE.
  intros.
  Opaque ISZERO.
  Opaque PRED.
  Opaque NAT.
  betae. betae. betae.
  rewrite ISZERO_0_E_TRUE.
  betaes.
  Transparent ISZERO.
  Transparent PRED.
  Transparent NAT.
Qed.

Lemma CASE_x_y_Sn_E_y_n : forall x y n,
  CASE @ x @ y @ [S n] == y @ [n].
Proof.
  unfold CASE.
  intros.
  Opaque ISZERO.
  Opaque PRED.
  Opaque NAT.
  betae. betae. betae.
  rewrite ISZERO_Sn_E_FALSE.
  rewrite PRED_Sn_E_n.
  betaes.
  Transparent ISZERO.
  Transparent PRED.
  Transparent NAT.
Qed.

Definition YC := \ (\ '1 @ ('0 @ '0)) @ (\ '1 @ ('0 @ '0)).

Lemma YC_x_R_x_YC_x : forall x, YC @ x -->> x @ (reduct_l (YC @ x)).
Proof.
  unfold YC.
  simpl.
  intros.
  beta.
  beta.
  auto.
Qed.

Lemma YC_x_E_x_YC_x : forall x, YC @ x == x @ (YC @ x).
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

Definition MU := \ (^YC @ (\ \ ('2 @ '0) @ '0 @ ('1 @ (^^^SUCC @ '0)))) @ ^[0].

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

Lemma MU_R_minimum : forall n A, 
  (A @ [n] -->> TRUE) -> 
  (forall m, m < n -> (A @ [m] -->> FALSE)) ->
  (MU @ A -->> [n]).
Proof.
  Opaque YC.
  Opaque SUCC.
  Opaque NAT.
  pose(Y A := YC @ (\ \ ^^A @ ' 0 @ ' 0 @ (' 1 @ (^^SUCC @ ' 0)))).
  pose (P A n m := (Y A @ [m] -->> [n])).
  assert(forall A n, 
    (A @ [n] -->> TRUE) -> 
    (forall m, m < n -> (A @ [m] -->> FALSE)) ->
    P A n 0).
  - intros.
    apply inductioninv with (x:=n).
    + unfold P, Y.
      apply (reductions_trans _ _ _ (reductions_app0 _ _ _ (YC_x_R_x_YC_x _))).
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
      apply (reductions_trans _ _ _ (reductions_app0 _ _ _ (YC_x_R_x_YC_x _))).
      fold (Y A).
      beta.
      beta.
      apply (reductions_trans _ _ (FALSE @ [y] @ (reduct_l (Y A) @ (SUCC @ [y])))).
      reducts. auto.
      unfold FALSE.
      beta.
      beta.
      apply (reductions_trans _ _ (reduct_l (Y A) @ [S y])).
      reducts. apply SUCC_R_S.
      apply (nat_uniqueness (Y A @ [S y])).
      reducts.
      apply l_reductl.
      auto.
  - intros.
    unfold MU.
    beta.
    fold (Y A).
    apply H.
    auto.
    auto.
Qed.

Lemma MU_E_minimum : forall n A, 
  (A @ [n] == TRUE) -> 
  (forall m, m < n -> (A @ [m] == FALSE)) ->
  (MU @ A == [n]).
Proof.
  intros.
  apply reduct_equiv.
  apply MU_R_minimum.
  apply normal_equiv_reduct.
  unfold TRUE, isNormal. simpl. auto.
  auto.
  intros.
  apply normal_equiv_reduct.
  unfold TRUE, isNormal. simpl. auto.
  auto.
Qed.

Definition DIVERGENT := (\ '0 @ '0) @ (\ '0 @ '0).

Lemma DIVERGENT_R_DIVERGENT : forall l, (DIVERGENT -->> l) -> l = DIVERGENT.
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
  apply DIVERGENT_R_DIVERGENT. auto.
  rewrite H2 in H0.
  unfold isNormal, DIVERGENT in H0.
  simpl in H0.
  discriminate H0.
Qed.

Lemma N_DIVERGENT_E_nat : forall n, [n] == DIVERGENT -> False.
Proof.
  intros.
  assert (D := DIVERGENT_divergent).
  rewrite <- H in D.
  contradict D.
  apply (Convergent_intro _ [n]).
  apply isNormal_NAT.
  auto.
Qed.
