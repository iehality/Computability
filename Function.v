Require Import Lambda.
Require Import Reduction.
Require Import SetoidL.
Require Import Calc.
Require Import Pairing.
Require Export Classical.

Opaque equiv.
Opaque NAT.

Inductive numeral :=
| num : nat -> numeral
| undefined.

Inductive Rec (f : nat -> nat) (l : Lambda) : Prop :=
| Rec_intro : (forall x, (l @ [x] == [f x])) -> Rec f l.

Inductive Recursive (f : nat -> nat) : Prop :=
| Recursive_intro : forall l, Rec f l -> Recursive f.

Inductive PR (f : nat -> numeral) (l : Lambda) : Prop :=
| PR_intro : (forall x y, f x = num y <-> (l @ [x] == [y])) -> PR f l.

Inductive PartialRecursive (f : nat -> numeral) :=
| PartialRecursive_intro : forall l, PR f l -> PartialRecursive f.

Parameter code : Lambda -> nat.
Parameter decode : nat -> Lambda.
Axiom code_decode : forall n, code (decode n) = n.
Axiom decode_code : forall l, decode (code l) = l.

Parameter univ : nat -> numeral.
Parameter UNIV : Lambda.
Axiom PR_univ : PR univ UNIV.
Axiom univ_IFF_lambda : forall l x y, univ (code l; x) = num y <-> l @ [x] == [y].

Parameter FST : Lambda.
Axiom FST_fst : forall x y, FST @ [(x; y)] == [x].
Parameter SND : Lambda.
Axiom SND_snd : forall x y, SND @ [(x; y)] == [y].
Parameter CPAIR : Lambda.
Axiom CPAIR_cpair : forall x y, CPAIR @ [x] @ [y] == [(x; y)].
Notation "$( X ; Y )" := (CPAIR @ X @ Y) (at level 0).
Notation "^$( X ; Y )" := (^CPAIR @ X @ Y) (at level 0).

Notation "{* e }" := (fun x => univ (e; x)) (at level 0).
Notation "{* e } ( x )" := (univ (e; x)) (at level 0).

Lemma pr_univ_cpair_code : forall l,
  PR {*code l} l.
Proof.
  intros.
  apply PR_intro.
  intros.
  apply univ_IFF_lambda.
Qed.

Lemma UNIV_univ : forall e x y,
  {*e}(x) = num y <-> UNIV @ $([e]; [x]) == [y].
Proof.
  intros.
  assert (H := PR_univ).
  inversion H.
  specialize (H0 (e; x) y).
  rewrite CPAIR_cpair.
  auto.
Qed.
  
Lemma N_lambda_IFF_univ_u : forall l x,
  {*code l}(x) = undefined <-> (forall y, ~ l @ [x] == [y]).
Proof.
  intros.
  destruct (univ (code l; x)) eqn:E.
  - split.
    intros.
    discriminate.
    intros.
    rewrite univ_IFF_lambda in E.
    specialize (H n). contradiction.
  - split.
    intros.
    intro.
    rewrite <- univ_IFF_lambda in H0.
    rewrite E in H0.
    discriminate.
    intros.
    reflexivity.
Qed.

Definition s_1_1 (n : nat) :=
  code (\ ^(decode (fst n)) @ (^CPAIR @ ^[snd n] @ '0)).

Parameter S_1_1 : Lambda.
Axiom S11_s11 : forall x y, S_1_1 @ [x] @ [y] == [s_1_1 (x; y)].

Theorem smn : forall e x y,
  {*s_1_1 (e; x)}(y) = {*e}((x; y)).
Proof.
  intros.
  unfold s_1_1.
  rewrite pairing_fst.
  rewrite pairing_snd.
  destruct (univ (e; (x; y))) eqn:E.
  - rewrite univ_IFF_lambda.
    betae.
    rewrite CPAIR_cpair.
    rewrite <- univ_IFF_lambda.
    rewrite code_decode.
    auto.
  - rewrite N_lambda_IFF_univ_u.
    intros. intro.
    assert ((\ sf 0 1 (decode e) @ (sf 0 1 CPAIR @ sf 0 1 [x] @ ' 0)) @ [y] == decode e @ [(x; y)]).
    {
      betae.
      rewrite CPAIR_cpair.
      reflexivity.
    }
    rewrite H0 in H.
    rewrite <- univ_IFF_lambda in H.
    rewrite code_decode in H.
    rewrite E in H.
    discriminate.
Qed.

Section RecursionTheorem.

  Definition fixedpoint I :=
    s_1_1 (code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)));
    code (\ ^I @ (^S_1_1 @ ^[code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)))] @ '0))).
    
  Theorem Kleene_Recursion i : forall I, Rec i I ->
    {*fixedpoint I} = {*i (fixedpoint I)}.
  Proof.
    intros.
    inversion H.
    pose (d := code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)))).
    assert (∀ e y, {*e}(e) = num y -> {*s_1_1 (d; e)} = {*y}).
    {
      intros.
      apply functional_extensionality. intros.
      rewrite smn.
      unfold d.
      rewrite UNIV_univ in H1.
      destruct (univ (y; x)) eqn:E.
      - rewrite univ_IFF_lambda.
        betae.
        rewrite FST_fst.
        rewrite SND_snd.
        rewrite H1.
        rewrite UNIV_univ in E.
        auto.
      - rewrite N_lambda_IFF_univ_u.
        intros. intro.
        assert (univ (y; x) = num y0).
        rewrite UNIV_univ.
        rewrite <- H2.
        symmetry.
        betae.
        rewrite FST_fst.
        rewrite SND_snd.
        rewrite H1.
        reflexivity.
        rewrite E in H3.
        discriminate.
    }
    unfold fixedpoint.
    pose (b := code (\ ^I @ (^ S_1_1 @ ^ [d] @ ' 0))).
    fold d.
    fold b.
    apply H1.
    unfold b.
    rewrite univ_IFF_lambda.
    betae.
    fold b.
    rewrite S11_s11.
    auto.
  Qed.
  
End RecursionTheorem.

Inductive defined (n : numeral) : Prop :=
| defined_intro : forall x, n = num x -> defined n.

Inductive reSet (A : nat -> Prop) : Prop :=
| reSet_intro : forall f, PartialRecursive f -> (forall x, defined (f x) <-> A x) -> reSet A.

Inductive recursiveSet (A : nat -> Prop) : Prop :=
| recursiveSet_intro : forall f, Recursive f -> (forall x, f x = 0 <-> A x) -> recursiveSet A.

Definition K := fun x => defined ({*x}(x)).

Theorem K_re : reSet K.
Proof.
  apply (reSet_intro _ (fun x => {*x}(x))).
  - pose (l := \ ^UNIV @ (^CPAIR @ '0 @ '0)).
    apply (PartialRecursive_intro _ l).
    apply PR_intro.
    intros.
    assert (l @ [x] == UNIV @ (CPAIR @ [x] @ [x])).
    unfold l.
    betae.
    reflexivity.
    rewrite H.
    apply UNIV_univ.
  - intros.
    unfold K.
    reflexivity.
Qed.
      

Theorem K_nonrecursive : ~ recursiveSet K.
Proof.
  intro.
  inversion H.
  inversion H0.
  inversion H2.
  pose (D := \ ^ISZERO @ (^l @ '0) @ ^DIVERGENT @ ^[0]).
  destruct (f (code D)) eqn:E.
  - assert (K (code D)).
    rewrite <- H1. auto.
    unfold K in H4.
    inversion H4.
    rewrite univ_IFF_lambda in H5.
    assert (D @ [code D] == DIVERGENT).
    {
      Opaque ISZERO.
      Opaque DIVERGENT.
      betae.
      rewrite H3.
      rewrite E.
      rewrite ISZERO_0_E_TRUE.
      betaes.
    }
    rewrite H5 in H6.
    apply (N_DIVERGENT_E_nat x).
    auto.
  - assert (~ K (code D)).
    {
      intro.
      rewrite <- H1 in H4.
      rewrite E in H4.
      discriminate.
    }
    contradict H4.
    unfold K.
    apply (defined_intro _ 0).
    rewrite univ_IFF_lambda.
    betae.
    rewrite H3.
    rewrite E.
    rewrite ISZERO_Sn_E_FALSE.
    betaes.
    Transparent ISZERO.
    Transparent DIVERGENT.
Qed.

Fixpoint initial (n0 : nat) (f : nat -> nat) : Lambda :=
  match n0 with
  | 0   => \ ^DIVERGENT
  | S n => \ (^LE @ '0 @ ^[n]) @ ((^LE @ ^[n] @ '0) @ ^[f n] @ (^(initial n f) @ '0)) @ ^DIVERGENT
  end.

Lemma initial_eq : forall f n x, x < n -> (initial n f) @ [x] == [f x].
Proof.
  induction n.
  - intros.
    lia.
  - intros.
    Opaque LE.
    Opaque DIVERGENT.
    Opaque NAT.
    simpl.
    betae.
    unfold lt in H.
    apply le_S_n in H.
    destruct (le_lt_eq_dec x n H).
    + rewrite IHn.
      rewrite le_I_LE_E_TRUE.
      rewrite Nle_I_LE_E_FALSE.
      unfold TRUE, FALSE. betaes.
      lia. lia. lia.
    + rewrite le_I_LE_E_TRUE.
      rewrite le_I_LE_E_TRUE.
      rewrite e.
      unfold TRUE.
      betaes.
      lia. lia.
Qed.
