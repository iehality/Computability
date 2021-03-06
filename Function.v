Require Export Lambda.
Require Export Reduction.
Require Export SetoidL.
Require Export Calc.
Require Export Pairing.
Require Export Classical.

Opaque equiv.
Opaque NAT.

Inductive numeral :=
| num : nat -> numeral
| undefined.

Inductive defined (n : numeral) : Prop :=
  defined_intro : forall x, n = num x -> defined n.

Inductive rec (f : nat -> nat) (l : Lambda) : Prop :=
  rec_intro : (forall x, (l @ [x] == [f x])) -> rec f l.

Inductive recursive (f : nat -> nat) : Prop :=
  recursive_intro : forall l, rec f l -> recursive f.

Inductive pr (f : nat -> numeral) (l : Lambda) : Prop :=
  pr_intro : (forall x y, f x = num y <-> (l @ [x] == [y])) -> pr f l.

Inductive precursive (f : nat -> numeral) :=
  precursive_intro : forall l, pr f l -> precursive f.

Parameter code : Lambda -> nat.
Parameter decode : nat -> Lambda.
Axiom code_decode : forall n, code (decode n) = n.
Axiom decode_code : forall l, decode (code l) = l.

Parameter univ : nat -> numeral.
Parameter UNIV : Lambda.
Axiom pr_univ : pr univ UNIV.
Axiom univ_IFF_lambda : forall l x y, univ (code l; x) = num y <-> l @ [x] == [y].

Parameter FST : Lambda.
Axiom FST_fst : forall x y, FST @ [(x; y)] == [x].
Parameter SND : Lambda.
Axiom SND_snd : forall x y, SND @ [(x; y)] == [y].
Parameter CPAIR : Lambda.
Axiom CPAIR_cpair : forall x y, CPAIR @ [x] @ [y] == [(x; y)].
Notation "$( X ; Y )" := (CPAIR @ X @ Y) (at level 0).
Notation "^$( X ; Y )" := (^CPAIR @ X @ Y) (at level 0).

Notation "#{ e }" := (fun x => univ (e; x)) (at level 0).
Notation "#{ e } ( x )" := (univ (e; x)) (at level 0).

Lemma pr_univ_cpair_code : forall l,
  pr #{code l} l.
Proof.
  intros.
  apply pr_intro.
  intros.
  apply univ_IFF_lambda.
Qed.

Lemma UNIV_univ : forall e x y,
  #{e}(x) = num y <-> UNIV @ $([e]; [x]) == [y].
Proof.
  intros.
  assert (H := pr_univ).
  inversion H.
  specialize (H0 (e; x) y).
  rewrite CPAIR_cpair.
  auto.
Qed.
  
Lemma univ_u_IFF_N_lambda : forall l x,
  #{code l}(x) = undefined <-> (forall y, ~ l @ [x] == [y]).
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
  #{s_1_1 (e; x)}(y) = #{e}((x; y)).
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
  - rewrite univ_u_IFF_N_lambda.
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

Section recursionTheorem.

  Definition fixedpoint I :=
    s_1_1 (code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)));
    code (\ ^I @ (^S_1_1 @ ^[code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)))] @ '0))).
    
  Theorem Kleene_recursion : forall i I, rec i I ->
    #{fixedpoint I} = #{i (fixedpoint I)}.
  Proof.
    intros.
    inversion H.
    pose (d := code (\ ^UNIV @ (^CPAIR @ (^UNIV @ (^CPAIR @ (^FST @ '0) @ (^FST @ '0))) @ (^SND @ '0)))).
    assert (∀ e y, #{e}(e) = num y -> #{s_1_1 (d; e)} = #{y}).
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
      - rewrite univ_u_IFF_N_lambda.
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

  Theorem Kleene_recursion_ext : forall i, recursive i ->
    exists n : nat, #{n} = #{i n}.
  Proof.
    intros.
    inversion H.
    apply Kleene_recursion in H0.
    eauto.
  Qed.
    
End recursionTheorem.

Definition Domain (e x : nat) : Prop := defined (#{e}(x)).

Inductive reSet (A : nat -> Prop) : Prop :=
  reSet_intro : forall f, precursive f -> (forall x, defined (f x) <-> A x) -> reSet A.

Inductive recursiveSet (A : nat -> Prop) : Prop :=
  recursiveSet_intro : forall f, recursive f -> (forall x, f x = 0 <-> A x) -> recursiveSet A.

Definition K := fun x => defined (#{x}(x)).

Theorem K_re : reSet K.
Proof.
  apply (reSet_intro _ (fun x => #{x}(x))).
  - pose (l := \ ^UNIV @ (^CPAIR @ '0 @ '0)).
    apply (precursive_intro _ l).
    apply pr_intro.
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

Definition indexSet (A : nat -> Prop) := forall x y, #{x} = #{y} -> A x -> A y.

Lemma N_FA_NP_I_EX_P {A : Type} (P : A -> Prop) :
  (~ forall x, ~ P x) -> (exists x, P x).
Proof.
  intros.
  apply NNPP.
  contradict H.
  intros.
  intro.
  assert (exists x, P x). eauto.
  contradiction.
Qed.

Theorem Rice : forall A,
  recursiveSet A -> indexSet A -> (exists x, A x) -> (exists x, ~ A x) -> False.
Proof.
  intros.
  destruct H1 as [a].
  destruct H2 as [b].
  inversion H.
  unfold indexSet in H0.
  inversion H3.
  inversion H5.
  pose (c := fun x => match (f x) with | 0 => b | _ => a end).
  assert (recursive c).
  {
    pose (C := \ ^ISZERO @ (^l @ '0) @ ^[b] @ ^[a]).
    apply (recursive_intro _ C).
    apply rec_intro.
    intros.
    unfold C.
    Opaque ISZERO.
    betae.
    unfold c.
    rewrite H6.
    destruct (f x) eqn:E.
    - rewrite ISZERO_0_E_TRUE.
      betaes.
    - rewrite ISZERO_Sn_E_FALSE.
      betaes.
  }
  apply Kleene_recursion_ext in H7.
  destruct H7 as [n].
  unfold c in H7.
  destruct (f n) eqn:E.
  - assert (A b).
    {
      apply (H0 _ _ H7).
      rewrite <- H4.
      auto.
    }
    contradiction.
  - assert (f n = 0).
    {
      rewrite H4.
      symmetry in H7.
      apply (H0 _ _ H7).
      auto.
    }
    rewrite E in H8.
    discriminate.
Qed.

Theorem Rice_0 : forall A,
  recursiveSet A -> indexSet A -> (forall x, A x) \/ (forall x, ~ A x).
Proof.
  intros.
  apply NNPP.
  intro.
  apply not_or_and in H1.
  destruct H1.
  apply (Rice A).
  auto.
  auto.
  apply N_FA_NP_I_EX_P.
  auto.
  apply N_FA_NP_I_EX_P.
  contradict H1.
  intros.
  apply NNPP.
  auto.
Qed.
