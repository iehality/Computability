Require Import Lambda.
Require Import Reduction.
Require Import SetoidL.
Require Import Calc.
Require Export Classical.

Section HaltingProblem.
  Variable H : Lambda.
  Hypothesis H_fv : fv H = 0.
  Hypothesis H_t : forall l, Convergent l -> (H @ l -->> TRUE).
  Hypothesis H_f : forall l, ~ Convergent l -> (H @ l -->> FALSE).

  Theorem HP_Unsolvable : False.
  Proof.
    pose (f := \ H @ ('0 @ '0) @ Omega @ TRUE).
    destruct (classic (Convergent (f @ f))).
    - assert (~ Convergent (f @ f)).
      assert (f @ f == Omega).
      Opaque NAT.
      apply reduct_equiv.
      beta.
      apply (reductions_trans _ _ (TRUE @ Omega @ TRUE)).
      reducts.
      auto.
      unfold TRUE.
      betas.
      auto.
      rewrite H1.
      apply Divergent_Omega.
      contradiction.
    - assert (Convergent (f @ f)).
      assert (f @ f == TRUE).
      apply reduct_equiv.
      beta.
      apply (reductions_trans _ _ (FALSE @ Omega @ TRUE)).
      reducts.
      auto.
      unfold FALSE.
      betas.
      auto.
      rewrite H1.
      auto.
      contradiction.
  Qed.
      
End HaltingProblem.

Inductive feq (l k : Lambda) : Prop :=
| feq_conv : l == k -> feq l k
| feq_div  : ~ Convergent l -> ~ Convergent k -> feq l k.

Lemma nen_f {A : Type} (P : A -> Prop) : ((exists x, ~ P x) -> False) -> (forall x, P x).
Proof.
  intros.
  apply NNPP.
  intro.
  apply H.
  exists x.
  auto.
Qed.

Section PostThm.
  Variable P : Lambda.
  Hypothesis P_fv : fv P = 0.
  Hypothesis P_predicate : forall l, (P @ l -->> TRUE) \/ (P @ l -->> FALSE).

  Hypothesis P_proper0 : forall l, ~ Convergent l -> P @ l -->> FALSE.
  Lemma Post0 : forall l, P @ l -->> FALSE.
  Proof.
    apply nen_f.
    intro.
    destruct H as [c].
    assert(PP := P_predicate c).
    destruct PP.
    pose(g := \ '0 @ c).
    
