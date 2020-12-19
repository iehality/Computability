Require Export Lambda.

Inductive Reduction : Lambda -> Lambda -> Prop :=
| beta_reduction : forall l k m n, Reduction l k -> Reduction m n -> Reduction ((\ l) @ m) (k.|n)
| reduction_lam  : forall l k, Reduction l k -> Reduction (\ l) (\ k)
| reduction_app  : forall l k m n, Reduction l k -> Reduction m n -> Reduction (l @ m) (k @ n)
| reduction_refl : forall l, Reduction l l.
Hint Constructors Reduction : core.
Notation "l ---> k" := (Reduction l k) (at level 100).

Lemma reduction_app0 : forall l k m, (l ---> k) -> (l @ m ---> k @ m).
Proof.
  auto.
Qed.

Lemma reduction_app1 : forall l k m,(l ---> k) -> (m @ l ---> m @ k).
Proof.
  auto.
Qed.
Ltac reduct := repeat (apply reduction_lam || apply reduction_app0 || apply reduction_app1).

Lemma sfSij_rew_sfij_rew : forall l k i j, 
  (sf (S i) j l).| (sf i j k) = sf i j (l .| k).
Proof.
  intros.
  rewrite (sf__rew l).
  rewrite (nested_rew_g).
  symmetry.
  rewrite (sf__rew (l.[0 # slide k \0])).
  rewrite (nested_rew_g l).
  apply rew_rew.
  intros.
  simpl.
  destruct i0.
  simpl.
  repeat rewrite sfn0.
  rewrite (sf__rew k).
  symmetry.
  rewrite (rew_i0 k).
  simpl.
  auto.
  simpl.
  repeat rewrite sfn0.
  rewrite <- minus_n_O.
  destruct (le_lt_dec i i0).
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma rewSisubs0_subs0rewi : forall l k i s, 
  l.[S i # s] .| k.[i# s] = (l .| k).[i# s].
Proof.
  intros.
  rewrite (nested_rew_g).
  symmetry.
  rewrite (nested_rew_g l).
  apply rew_rew.
  intros.
  destruct i0.
  simpl.
  repeat rewrite sfn0.
  symmetry.
  rewrite rew_i0.
  auto.
  repeat rewrite sfn0.
  rewrite <- minus_n_O.
  destruct(le_lt_dec 0 (S i0)).
  destruct(le_lt_dec (S i) (S i0)).
  simpl.
  repeat rewrite sfn0.
  rewrite <- minus_n_O.
  destruct(le_lt_dec i i0).
  rewrite (sf__rew (s (i0 - i))).
  symmetry.
  rewrite (sf__rew).
  rewrite (nested_rew).
  apply rew_rew.
  simpl.
  auto.
  lia.
  simpl.
  repeat rewrite sfn0.
  rewrite <- minus_n_O.
  destruct(le_lt_dec i i0).
  lia.
  auto.
  lia.
Qed.

Lemma lamRedlam_red : forall l k, (\ l ---> \ k) -> (l ---> k).
Proof.
  intros.
  inversion H.
  auto.
  auto.
Qed.
Hint Resolve lamRedlam_red : core.

Lemma reduct_sf : forall l k i j, 
  (l ---> k) -> (sf i j l ---> sf i j k).
Proof.
  induction l.
  - simpl.
    intros.
    inversion H.
    simpl.
    destruct (le_lt_dec i n).
    auto. auto.
  - simpl.
    intros.
    inversion H.
    simpl. reduct.
    auto.
    simpl. reduct.
    auto.
  - simpl.
    intros.
    inversion H.
    simpl.
    rewrite <- sfSij_rew_sfij_rew.
    assert(sf (S i) j l ---> sf (S i) j k0).
    apply lamRedlam_red.
    rewrite <- H0 in IHl1. 
    specialize(IHl1 (\ k0) i j).
    simpl in IHl1.
    apply IHl1. auto.
    auto.
    simpl.
    auto.
    auto.
Qed.

Lemma lamRed_lamRedlam : forall l k, (\ l ---> k) -> exists k0, k = \ k0.
Proof.
  intros.
  inversion H.
  exists k0.
  auto.
  exists l.
  auto.
Qed.

Lemma reduct_rew0 : forall l0 l1 s0 s1 i, 
  (l0 ---> l1) -> 
  (forall n, s0 n ---> s1 n) -> 
  (l0.[i# s0] ---> l1.[i# s1]).
Proof.
  induction l0.
  - simpl.
    intros.
    inversion H.
    simpl.
    destruct(le_lt_dec i n).
    apply reduct_sf.
    auto.
    auto.
  - simpl.
    intros.
    assert(H1 := lamRed_lamRedlam l0 l1 H).
    destruct H1 as [k0].
    rewrite H1.
    simpl.
    reduct.
    apply IHl0.
    rewrite H1 in H.
    inversion H.
    auto.
    auto.
    auto.
  - simpl.
    intros.
    inversion H.
    simpl.
    rewrite <- rewSisubs0_subs0rewi.
    assert(l.[S i # s0] ---> k.[S i # s1]).
    apply lamRedlam_red.
    rewrite <- H1 in IHl0_1.
    specialize(IHl0_1 (\ k) s0 s1 i). simpl in IHl0_1.
    auto.
    auto.
    simpl.
    auto.
    simpl.
    auto.
Qed.

Lemma reduct_subst : forall l0 l1 k0 k1, 
  (l0 ---> l1) -> 
  (k0 ---> k1) -> 
  (l0 .| k0 ---> l1 .| k1).
Proof.
  intros.
  apply reduct_rew0.
  auto.
  destruct n.
  simpl. auto.
  simpl. auto.
Qed.
Hint Resolve reduct_subst : core.

Lemma diamond0 : forall l k0 k1, 
  (l ---> k0) -> 
  (l ---> k1) -> 
  exists m,
  (k0 ---> m) /\ 
  (k1 ---> m).
Proof.
  assert(Hlam :
  forall l, 
  (forall k0 k1, (\ l ---> k0) -> (\ l ---> k1) -> exists m, (k0 ---> m) /\ (k1 ---> m)) ->
  (forall k0 k1, (l ---> k0) -> (l ---> k1) -> exists m, (k0 ---> m) /\ (k1 ---> m))
  ). 
  {
    intros.
    apply reduction_lam in H0.
    apply reduction_lam in H1.
    specialize(H (\ k0) (\ k1) H0 H1).
    destruct H. 
    assert(exists m, x = \ m).
    apply lamRed_lamRedlam with (l:=k0). apply H.
    destruct H2 as [m].
    rewrite H2 in H.
    destruct H.
    exists m.
    auto.
  }
  induction l.
  - simpl.
    intros.
    inversion H.
    inversion H0.
    exists ('n).
    auto.
  - intros.
    inversion H.
    inversion H0.
    {
      specialize (IHl k k2 H2 H5).
      destruct IHl as [m].
      destruct H7.
      exists (\ m).
      auto.
      (*
      \ l  ---> \ k
       |         |
       ↓         ↓
      \ k2 ---> \ m
      *)
    }
    {
      exists k0.
      split.
      rewrite H3. auto.
      auto.
      (*
      \ l ---> \ k
       |        |
       ↓        ↓
      \ l ---> \ k
      *)
    }
    {
      exists k1.
      split.
      auto.
      auto.
      (*
      \ l ---> \ l
       |        |
       ↓        ↓
      \ k ---> \ k
      *)
    }
  - intros.
    inversion H.
    inversion H0.
    {
      rewrite <- H1 in IHl1.
      rewrite <- H1 in H6.
      injection H6. intros.
      assert(IHlam1 := Hlam l IHl1).
      assert(exists m1, (k ---> m1) /\ (k2 ---> m1)).
      apply IHlam1.
      auto.
      rewrite <- H11. auto.
      assert(exists m1, (n ---> m1) /\ (n0 ---> m1)).
      apply IHl2. auto. auto.
      destruct H12 as [m1]. destruct H12.
      destruct H13 as [m2]. destruct H13.
      exists(m1 .| m2).
      auto. 
      (*
      (\ l) @ l2 ---> k2 .| n0
           |             |
           ↓             ↓
        k .| n   ---> m1 .| m2
      *)
    }
    {
      rewrite <- H1 in H8.
      assert(exists k2', k2 = \ k2').
      apply lamRed_lamRedlam with (l:=l). auto. destruct H11 as [k2'].
      rewrite H11.
      rewrite H11 in H8.
      rewrite <- H1 in IHl1.
      assert(IHlam1 := Hlam l IHl1).
      assert(exists m1, (k ---> m1) /\ (k2' ---> m1)).
      apply IHlam1.
      auto.
      apply lamRedlam_red. auto.
      assert(exists m1, (n ---> m1) /\ (n0 ---> m1)).
      apply IHl2.
      auto. auto.
      destruct H12 as [m1]. destruct H12.
      destruct H13 as [m2]. destruct H13.
      exists (m1 .| m2).
      auto.
      (*
      (\ l) @ l2 --->  k .| n
          |              |
          ↓              ↓
        k2 @ n0  ---> m1 .| m2
      *)
    }
    {
      exists(k .| n).
      rewrite H4.
      auto.
      (*
      (\ l) @ l2 ---> k .| n
           |            |
           ↓            ↓
      (\ l) @ l2 ---> k .| n
      *)
    }
    inversion H0.
    {
      rewrite <- H6 in H3.
      assert(exists k', k = \ k').
      apply lamRed_lamRedlam with (l:=l0). auto. destruct H11 as [k'].
      rewrite H11.
      rewrite H11 in H3.
      rewrite <- H6 in IHl1.
      assert(IHlam1 := Hlam l0 IHl1).
      assert(exists m1, (k2 ---> m1) /\ (k' ---> m1)).
      apply IHlam1.
      auto.
      apply lamRedlam_red. auto.
      assert(exists m1, (n ---> m1) /\ (n0 ---> m1)).
      apply IHl2.
      auto. auto.
      destruct H12 as [m1]. destruct H12.
      destruct H13 as [m2]. destruct H13.
      exists (m1 .| m2).
      auto.
      (*
      (\ l0) @ l2 --->  k @ n
           |              |
           ↓              ↓
        k2 .| n0  ---> m1 .| m2
      *)
    }
    {
      assert(exists m1, (k ---> m1) /\ (k2 ---> m1)).
      apply IHl1.
      auto. auto.
      assert(exists m1, (n ---> m1) /\ (n0 ---> m1)).
      apply IHl2.
      auto. auto.
      destruct H11 as [m1]. destruct H11.
      destruct H12 as [m2]. destruct H12.
      exists (m1 @ m2).
      auto.
      (*
      l1 @ l2 --->  k @ n
         |            |
         ↓            ↓
      k2 @ n0 ---> m1 @ m2
      *)
    }
    {
      exists(k @ n).
      auto.
      (*
      l1 @ l2 ---> k @ n
         |           |
         ↓           ↓
      l1 @ l2 ---> k @ n
      *)
    }
    {
      exists k1.
      auto.
      (*
      l1 @ l2 ---> l1 @ l2
         |           |
         ↓           ↓
         k    --->   k
      *)
    }
Qed.

Inductive Reductions (l k : Lambda) : Prop :=
| reductions_intro : Reduction l k -> Reductions l k
| reductions_trans : forall m, Reductions l m -> Reductions m k -> Reductions l k.
Hint Resolve reductions_intro : core.
Notation "l -->> k" := (Reductions l k) (at level 100).

Lemma diamond_red_reds : forall l k0 k1, 
  (l ---> k0) -> 
  (l -->> k1) -> 
  exists m,
  (k0 -->> m) /\ 
  (k1 ---> m).
Proof.
  assert(
    forall l k0, 
    (l -->> k0) ->
    forall k1, 
    (l ---> k1) -> 
    exists m,
    (k0 ---> m) /\ 
    (k1 -->> m)
  ).
  - intros l k0 H.
    induction H.
    intros.
    {
      assert(D := diamond0 _ _ _ H H0).
      destruct D as [m]. destruct H1.
      exists m.
      auto.
    }
    {
      intros.
      specialize(IHReductions1 k1 H1).
      destruct IHReductions1 as [m0]. destruct H2.
      specialize(IHReductions2 m0 H2).
      destruct IHReductions2 as [m1]. destruct H4.
      exists m1.
      split.
      auto.
      apply (reductions_trans _ _ m0).
      auto.
      auto.
    }
  - intros.
    specialize(H l k1 H1 k0 H0).
    destruct H as [m]. destruct H.
    exists m.
    auto.
Qed. 

Theorem Church_Rosser : forall l k0 k1, 
  (l -->> k0) -> 
  (l -->> k1) -> 
  exists m,
  (k0 -->> m) /\ 
  (k1 -->> m).
Proof.
  assert(
    forall l k0, 
    (l -->> k0) ->
    forall k1, 
    (l -->> k1) -> 
    exists m,
    (k0 -->> m) /\ 
    (k1 -->> m)
  ).
  - intros l k0 H.
    induction H.
    + intros.
      assert(D0 := diamond_red_reds l k k1 H H0).
      destruct D0 as [m]. destruct H1.
      exists m.
      auto.
    + intros.
      specialize(IHReductions1 k1 H1).
      destruct IHReductions1 as [m0]. destruct H2.
      specialize(IHReductions2 m0 H2).
      destruct IHReductions2 as [m1]. destruct H4.
      exists m1.
      split.
      auto.
      apply (reductions_trans _ _ m0).
      auto.
      auto.
  - intros.
    apply (H l).
    auto.
    auto.
Qed.

Lemma reductions_trans0 : forall l k m,
  (k -->> m) -> (l -->> k) -> (l -->> m).
Proof.
  intros.
  apply (reductions_trans _ _ k).
  auto.
  auto.
Qed.

Lemma reductions_lam : forall l k,
  (l -->> k) -> (\ l -->> \ k).
Proof.
  intros.
  induction H.
  auto.
  apply (reductions_trans _ _ (\ m)).
  auto. auto.
Qed.

Lemma reductions_app0 : forall l k m,
  (l -->> k) -> (l @ m -->> k @ m).
Proof.
  intros.
  induction H.
  auto.
  apply (reductions_trans _ _ (m0 @ m)).
  auto. auto.
Qed.

Lemma reductions_app1 : forall l k m,
  (l -->> k) -> (m @ l -->> m @ k).
Proof.
  intros.
  induction H.
  auto.
  apply (reductions_trans _ _ (m @ m0)).
  auto. auto.
Qed.

Lemma reductions_app : forall l k m n,
  (l -->> k) -> (m -->> n) -> (l @ m -->> k @ n).
Proof.
  intros.
  induction H.
  induction H0.
  auto.
  apply (reductions_trans _ _ _ IHReductions1).
  apply reductions_app1.
  auto.
  apply (reductions_trans _ _ _ IHReductions1).
  apply reductions_app0.
  auto.
Qed.

Hint Resolve reductions_lam reductions_app0 reductions_app1 reductions_app : core.

Ltac reducts := repeat (apply reductions_lam || apply reductions_app0 || apply reductions_app1).

Fixpoint reduct_l l0 : Lambda :=
  match l0 with
  | (\ l) @ k => l.| k
  | \ l       => \ (reduct_l l)
  | l @ k     => reduct_l l @ k
  | x         => x
  end.

Fixpoint reduct_all l0 : Lambda :=
  match l0 with
  | (\ l) @ k => l.| k
  | \ l       => \ (reduct_all l)
  | l @ k     => reduct_all l @ reduct_all k
  | x         => x
  end.

Lemma l_reductl : forall l, l -->> reduct_l l.
Proof.
  induction l.
  - simpl. auto.
  - simpl. auto.
  - destruct l1.
    + simpl. auto.
    + simpl. auto.  
    + apply (reductions_trans _ _ (reduct_l (l1_1 @ l1_2) @ l2)). auto.
      simpl. auto.
Qed.

Lemma l_reductall : forall l, l -->> reduct_all l.
Proof.
  induction l.
  - simpl. auto.
  - simpl. auto.
  - destruct l1.
    + simpl. auto.
    + simpl. auto.  
    + apply (reductions_trans _ _ (reduct_all (l1_1 @ l1_2) @ l2)). auto.
      apply (reductions_trans _ _ (reduct_all (l1_1 @ l1_2) @ reduct_all l2)). auto.
      simpl. auto.
Qed.

Fixpoint normal (l0 : Lambda) : bool :=
  match l0 with
  | (\ l) @ k => false
  | 'n        => true
  | \ l       => normal l
  | l @ k     => normal l && normal k
  end.

Definition isNormal l := is_true (normal l).

Lemma norm_app_norm: forall l k,
    isNormal (l @ k) -> (isNormal l /\ isNormal k).
Proof.
  intros.
  inversion H.
  destruct l.
  rewrite Bool.andb_true_iff in H1. destruct H1.
  unfold isNormal.
  auto.
  discriminate H1.
  rewrite Bool.andb_true_iff in H1. destruct H1.
  unfold isNormal.
  auto.  
Qed.

Lemma normal_reduction : forall l k,
  isNormal l -> (l ---> k) -> l = k.
Proof.
  unfold isNormal.
  induction l.
  - simpl.
    intros.
    inversion H0.
    auto.
  - simpl.
    intros.
    inversion H0.
    apply f_equal.
    apply IHl.
    auto. auto.
    auto.
  - intros.
    assert(N := norm_app_norm l1 l2 H). destruct N.
    inversion H0.
    rewrite <- H3 in H.
    discriminate H.
    apply f_equal2.
    auto.
    auto.
    auto.
Qed.

Lemma normal_reductions l : isNormal l -> forall k, (l -->> k) -> l = k.
Proof.
  intros.
  induction H0.
  apply normal_reduction. auto. auto.
  rewrite IHReductions1.
  rewrite <- IHReductions2.
  auto.
  rewrite <- IHReductions1.
  auto. auto. auto.
Qed.

Lemma uniqueness : forall l k m,
  isNormal m ->
  (l -->> k) ->
  (l -->> m) ->
  (k -->> m).
Proof.
  intros.
  assert (CR := Church_Rosser _ _ _ H0 H1).
  destruct CR as [m0].
  destruct H2.
  apply (normal_reductions _ H) in H3.
  rewrite H3.
  auto.
Qed.

Inductive Convergent (l : Lambda) : Prop :=
| Convergent_intro : forall k, isNormal k -> (l -->> k) -> Convergent l.

Lemma normal_Convergent : forall l, normal l = true -> Convergent l.
Proof.
  intros.
  apply (Convergent_intro _ l).
  auto.
  auto.
Qed.
Hint Resolve normal_Convergent : core.
 
Lemma reduct_convergent : forall l k,
    (l -->> k) ->
    Convergent l ->
    Convergent k.
Proof.
  intros.
  inversion H0.
  assert (k -->> k0).
  apply (uniqueness l).
  auto.
  auto.
  auto.
  apply (Convergent_intro _ k0).
  auto.
  auto.
Qed.


Ltac lclean :=
  repeat(
      rewrite sfn0
  || rewrite rew_sf
  || match goal with
    | Hy : fv _ = 0 |- _ => (rewrite (fv0_sf _ Hy) || rewrite (fv0_rew _ Hy))
    end
  ).

Ltac lclean_in H :=
  repeat(
      rewrite sfn0 in H
  || rewrite rew_sf in H
  || match goal with
    | Hy : fv _ = 0 |- _ => (rewrite (fv0_sf _ Hy) in H || rewrite (fv0_rew _ Hy) in H)
    end
    ).

Ltac beta := apply (reductions_trans _ _ _ (l_reductl _)); simpl; lclean.
Ltac beta_all := apply (reductions_trans _ _ _ (l_reductall _)); simpl; lclean.

Ltac betas :=
  repeat
  match goal with
  | |- ?l -->> ?l => auto
  | _            => beta
  end.

Ltac betas_all :=
  repeat
  match goal with
  | |- ?l -->> ?l => auto
  | _            => beta_all
  end.
