Require Export Utf8.
Require Export Arith.
Require Export Lia.

Fixpoint Sum (n0 : nat) :=
  match n0 with
  | 0   => 0
  | S n => S (n + Sum n)
  end.

Lemma le_sum : forall n, n <= Sum n.
Proof.
  induction n.
  simpl. lia.
  simpl.
  lia.
Qed.

Definition cpair (n m : nat) : nat := n + Sum (n + m).
Notation "( x ; y )" := (cpair x y) (at level 0).

Lemma le_cpair_fst n m : n <= cpair n m.
Proof.
  unfold cpair.
  lia.
Qed.

Lemma le_cpair_snd n m : m <= cpair n m.
Proof.
  unfold cpair.
  assert(H := le_sum (n + m)).
  lia.
Qed.

(* Sum (summax n) <= n < n + Sum (summax n) *)

Fixpoint summax (n0 : nat) :=
  match n0 with
  | 0 => 0
  | S n =>
    let m := summax n in
    match (le_lt_dec (Sum (S m)) (S n)) with
    | left _  => S m
    | right _ => m
    end
  end.

Definition fst (n : nat) := n - Sum (summax n).
Definition snd (n : nat) := summax n - fst n.

Compute fst 5.
Compute snd 5.

Lemma lt_I_lt_sum_sum : forall n m,
  n < m -> Sum n < Sum m.
Proof.
  assert(forall n m, Sum m < Sum (S n + m)).
  {
    induction n.
    simpl. lia.
    simpl.
    intros.
    specialize (IHn m).
    simpl in IHn.
    lia.
  }
  intros.
  pose (l := m - S n).
  assert (m = S l + n). lia.
  rewrite H1.
  auto.
Qed.

Lemma lt_sum_sum_I_lt : forall n m,
  Sum n < Sum m -> n < m.
Proof.
  assert(forall n m, Sum m <= Sum (n + m)).
  {
    induction n.
    simpl. lia.
    simpl.
    intros.
    specialize (IHn m).
    lia.
  }
  intros.
  destruct(le_lt_dec m n).
  - assert(Sum m <= Sum n).
    pose (s := n - m).
    assert (n = s + m). lia.
    rewrite H1. auto.
    lia.
  - lia.
Qed.

Lemma le_sum_sum_I_le : forall n m,
  Sum n <= Sum m -> n <= m.
Proof.
  intros.
  destruct (le_lt_eq_dec (Sum n) (Sum m) H).
  apply lt_sum_sum_I_lt in l.
  lia.
  destruct(le_lt_dec n m).
  lia.
  apply lt_I_lt_sum_sum in l.
  lia.
Qed.
    
Lemma le_sum_summax_A_lt_sum_s_summax : forall n,
  Sum (summax n) <= n < Sum (S (summax n)).
Proof.
  induction n.
  - simpl. lia.
  - destruct IHn.
    Opaque Sum.
    simpl.
    Transparent Sum.
    destruct (le_lt_dec (Sum (S (summax n))) (S n)).
    split. lia.
    simpl. simpl in H0. simpl in l.
    lia.
    split.
    lia.
    lia.
Qed.

Lemma summax_cpair_E_plus : forall n m,
  summax (cpair n m) = n + m.
Proof.
  unfold cpair.
  intros.
  assert (H := le_sum_summax_A_lt_sum_s_summax (n + Sum (n + m))).
  destruct H.
  assert (n + Sum (n + m) < Sum (S (n + m))).
  simpl. lia.
  assert (summax (n + Sum (n + m)) < S (n + m)).
  apply lt_sum_sum_I_lt. lia.
  assert (n + m < S (summax (n + Sum (n + m)))).
  apply lt_sum_sum_I_lt. lia.
  lia.
Qed.

Theorem pairing_fst : forall n m, fst (cpair n m) = n.
Proof.
  unfold fst.
  intros.
  rewrite summax_cpair_E_plus.
  unfold cpair.
  lia.
Qed.

Theorem pairing_snd : forall n m, snd (cpair n m) = m.
Proof.
  intros.
  unfold snd.
  rewrite pairing_fst.
  rewrite summax_cpair_E_plus.
  lia.
Qed.

Theorem pairing_inj_fst : forall x y u v,
  cpair x y = cpair u v -> x = u.
Proof.
  intros.
  assert(H0 := pairing_fst x y).
  rewrite <- H0.
  rewrite H.
  apply pairing_fst.
Qed.

Theorem pairing_inj_snd : forall x y u v,
  cpair x y = cpair u v -> y = v.
Proof.
  intros.
  assert(H0 := pairing_snd x y).
  rewrite <- H0.
  rewrite H.
  apply pairing_snd.
Qed.

