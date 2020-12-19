Require Import Lambda.
Require Import Reduction.
Require Export SetoidClass.

Inductive lameq (l k : Lambda) : Prop :=
| lameq_intro : forall m, (l -->> m) -> (k -->> m) -> lameq l k.
Hint Constructors lameq : core.

Program Instance SetoidL : Setoid Lambda := {|equiv := lameq|}.
Next Obligation.
Proof.
  split.
  - unfold Reflexive.
    intros.
    apply (lameq_intro _ _ x).
    auto.
    auto.
  - unfold Symmetric.
    intros.
    inversion H.
    apply (lameq_intro _ _ m).
    auto.
    auto.
  - unfold Transitive.
    intros.
    inversion H.
    inversion H0.
    assert(CR := Church_Rosser _ _ _ H2 H3).
    destruct CR as [m1].
    destruct H5.
    apply (lameq_intro _ _ m1).
    apply (reductions_trans _ _ _ H1 H5).
    apply (reductions_trans _ _ _ H4 H6).
    
Qed.

Instance lam_proper : 
  Proper (equiv ==> equiv) lam.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  intros.
  inversion H.
  apply (lameq_intro _ _ (\ m)).
  auto.
  auto.
Qed.

Lemma lam_equiv : forall l k, l == k -> \ l == \ k.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Instance app_proper : 
  Proper (equiv ==> equiv ==> equiv) app.
Proof.
  unfold Proper, respectful, equiv. 
  simpl.
  intros.
  inversion H.
  inversion H0.
  apply (lameq_intro _ _ (m @ m0)).
  auto.
  auto.
Qed.

Lemma app_equiv0 : forall l k m, l == k -> l @ m == k @ m.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma app_equiv1 : forall l k m, l == k -> m @ l == m @ k.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Ltac reducte :=
  repeat
  match goal with
  | |- (\ ?l == \ ?k) => apply lam_equiv
  | |- (?l @ ?m == ?k @ ?m) => apply app_equiv0
  | |- (?m @ ?l == ?m @ ?k) => apply app_equiv1
  end.                                                        

Lemma reduct_equiv : forall l k,
  (l -->> k) -> l == k.
Proof.
  intros.
  unfold equiv. simpl.
  apply (lameq_intro _ _ k).
  auto.
  auto.
Qed.
Hint Resolve reduct_equiv : core.

Lemma normal_equiv_reduct : forall l k,
  isNormal k ->
  (l == k) ->
  (l -->> k).
Proof.
  intros.
  inversion H0.
  apply (reductions_trans _ _ _ H1).
  assert(k = m).
  apply normal_reductions.
  auto.
  auto.
  rewrite H3.
  auto.
Qed.

Lemma equiv_reductionl : forall l k, reduct_l l == k -> l == k.
Proof.
  intros.
  assert (l == reduct_l l).
  apply reduct_equiv.
  apply l_reductl.
  rewrite H0.
  auto.
Qed.

Lemma equiv_reductionall : forall l k, reduct_all l == k -> l == k.
Proof.
  intros.
  assert (l == reduct_all l).
  apply reduct_equiv.
  apply l_reductall.
  rewrite H0.
  auto.
Qed.

Opaque equiv.
Ltac betae := apply equiv_reductionl; simpl; lclean.
Ltac betae_all := apply equiv_reductionall; simpl; lclean.

Ltac betaes :=
  repeat
  match goal with
  | |- ?l == ?l => reflexivity
  | _          => betae
  end.

Ltac betaes_all :=
  repeat
  match goal with
  | |- ?l == ?l => reflexivity
  | _          => betae_all
  end.

Lemma f_equiv : forall f x y, Proper (equiv ==> equiv) f -> x == y -> f x == f y.
Proof.
  intros.
  rewrite H0.
  reflexivity.
Qed.

Lemma normal_neq_nequiv : forall l k,
  isNormal l -> isNormal k -> l <> k -> l =/= k.
Proof.
  intros.
  intro.
  contradict H1.
  inversion H2.
  assert (l = m).
  apply normal_reductions. auto. auto.
  assert (k = m).
  apply normal_reductions. auto. auto.
  rewrite H4. rewrite H5.
  reflexivity.
Qed.


Instance Convergent_proper : 
  Proper (equiv ==> equiv) Convergent.
Proof.
  Transparent equiv.
  unfold Proper, respectful, equiv. 
  simpl.
  intros.
  split.
  - intros.
    inversion H0.
    apply (Convergent_intro _ k).
    auto.
    inversion H.
    apply (reductions_trans _ _ _ H4).
    apply (uniqueness x).
    auto.
    auto.
    auto.
  - intros.
    inversion H0.
    apply (Convergent_intro _ k).
    auto.
    inversion H.
    apply (reductions_trans _ _ _ H3).
    apply (uniqueness y).
    auto.
    auto.
    auto.
  Opaque equiv.
Qed.
