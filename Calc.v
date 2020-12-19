Require Import Lambda.
Require Import Reduction.
Require Import SetoidL.

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

Definition pair := \ \ \ '0 @ '2 @ '1.

Lemma pair_TRUE : forall l k, pair @ l @ k @ TRUE -->> l.
Proof.
  unfold TRUE, pair.
  intros.
  betas.
Qed.

Lemma pair_TRUE_eq : forall l k, pair @ l @ k @ TRUE == l.
Proof.
  intros.
  apply reduct_equiv.
  apply pair_TRUE.
Qed.

Lemma pair_FALSE : forall l k, pair @ l @ k @ FALSE -->> k.
Proof.
  unfold FALSE, pair.
  intros.
  betas.
Qed.

Lemma pair_FALSE_eq : forall l k, pair @ l @ k @ FALSE == k.
Proof.
  intros.
  apply reduct_equiv.
  apply pair_FALSE.
Qed.

Lemma pair_equiv : forall x y v w,
  (pair @ x @ y == pair @ v @ w) -> (x == v /\ y == w).
Proof.
  intros.
  split.
  rewrite <- (pair_TRUE_eq _ y).
  symmetry.
  rewrite <- (pair_TRUE_eq _ w).
  rewrite H.
  reflexivity.
  rewrite <- (pair_FALSE_eq x).
  symmetry.
  rewrite <- (pair_FALSE_eq v).
  rewrite H.
  reflexivity.
Qed.


Definition ISZERO := \ '0 @ (\ FALSE) @ TRUE.
Lemma ISZERO_0_eq: ISZERO @ [0] == TRUE.
Proof.
  unfold ISZERO, TRUE, FALSE.
  Opaque equiv.
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

Definition PRED := \ \ \ '2 @ (\ \ '0 @ ('1 @ '3)) @ (\ '1) @ (\ '0).
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

Definition CASE := \ \ \ ISZERO @ '0 @ '2 @ ('1 @ (PRED @ '0)).

Lemma CASE_0_eq : forall x y,
  CASE @ x @ y @ [0] == x.
Proof.
  unfold CASE.
  intros.
  assert (fv ISZERO = 0). simpl. auto.
  assert (fv PRED = 0). simpl. auto.
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
  assert(fv ISZERO = 0). simpl. auto.
  assert(fv PRED = 0). simpl. auto.
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

Definition Omega := (\ '0 @ '0) @ (\ '0 @ '0).

Lemma Omega_reduct : forall l, (Omega -->> l) -> l = Omega.
Proof.
  assert (forall l k, (l -->> k) -> l = Omega -> k = Omega).
  unfold Omega.
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
    apply (H Omega).
    auto.
    auto.
Qed.

Lemma Divergent_Omega : ~ Convergent Omega.
Proof.
  intro.
  inversion H.
  assert (k = Omega).
  apply Omega_reduct. auto.
  rewrite H2 in H0.
  unfold isNormal, Omega in H0.
  simpl in H0.
  discriminate H0.
Qed.
