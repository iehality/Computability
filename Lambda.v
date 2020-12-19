Require Export Utf8.
Require Export Classical.
Require Export FunctionalExtensionality.
Require Export Arith.
Require Export Lia.

(**)
  Definition f_equal2 : 
    forall (A B C : Type) (f : A -> B -> C) (x0 x1 : A) (y0 y1 : B),
    x0 = x1 -> y0 = y1 -> f x0 y0 = f x1 y1 :=
  fun (A B C : Type) (f : A → B → C) (x0 x1 : A) (y0 y1 : B) (H : x0 = x1) (H0 : y0 = y1) =>
  match H in (_ = x) return (_ = f x _) with
  | eq_refl => 
    match H0 in (_ = x) return (_ = f _ x) with
    | eq_refl => eq_refl
    end
  end.
  
  Lemma lt_lt_max_l : forall n m r, n < m -> n < max m r.
  Proof.
  unfold lt.
  intros.
  assert (lml := (Nat.le_max_l m r)).
  apply Nat.le_trans with (m := m).
  auto.
  auto.
  Qed.
  
  Lemma lt_lt_max_r : forall n m r, n < m -> n < max r m.
  Proof.
  unfold lt.
  intros.
  assert (lml := (Nat.le_max_r r m)).
  apply Nat.le_trans with (m := m).
  auto.
  auto.
  Qed.
  
  Lemma le_le_max_l : forall n m r, n <= m -> n <= max m r.
  Proof.
  intros.
  assert (lml := (Nat.le_max_l m r)).
  apply Nat.le_trans with (m := m).
  auto.
  auto.
  Qed.
  
  Lemma le_le_max_r : forall n m r, n <= m -> n <= max r m.
  Proof.
  intros.
  assert (lml := (Nat.le_max_r r m)).
  apply Nat.le_trans with (m := m).
  auto.
  auto.
  Qed.
  
  Lemma nleb_nle : forall x y, x <=? y = false <-> ~ x <= y.
  Proof.
    intros.
    rewrite <- Bool.not_true_iff_false.
    split. intros.
    contradict H.
    apply Nat.leb_le.
    auto.
    intros.
    contradict H.
    apply Nat.leb_le in H.
    auto.
  Qed.

  Lemma neqb_neq : forall x y, x =? y = false <-> ~ x = y.
  Proof.
    intros.
    split. intros.
    rewrite <- Bool.not_true_iff_false in H.
    contradict H.
    rewrite Nat.eqb_eq. auto.
    intros.
    rewrite <- Bool.not_true_iff_false.
    contradict H.
    rewrite Nat.eqb_eq in H.
    auto.
  Qed.
  
  
  
(**)

Inductive Lambda : Type :=
| var : nat -> Lambda
| lam : Lambda -> Lambda
| app : Lambda -> Lambda -> Lambda.

Notation "' v " := (var v) (at level 5).
Notation "\ l" := (lam l) (at level 25, right associativity).
Notation "x @ y" := (app x y) (at level 20, left associativity).

Notation "\0" := (fun x => ('x)) (at level 0).

Fixpoint sf (n k : nat) l0 := 
  match l0 with
  | 'm      => 
    match (le_lt_dec n m) with
    | left _  => '(k + m) (* n <= m *)
    | right _ => 'm       (* m < n *)
    end
  | \ l     => \ (sf (S n) k l)
  | l1 @ l2 => (sf n k l1) @ (sf n k l2)
  end.

Lemma sfn0 : forall l n, sf n 0 l = l.
Proof.
  induction l.
  simpl. intros.
  destruct(le_lt_dec n0 n). auto. auto.
  simpl. intros.
  apply f_equal. auto.
  simpl. intros.
  rewrite IHl1.
  rewrite IHl2.
  auto.
Qed.

Lemma sf_sf : forall l n i j, sf n i (sf n j l) = sf n (i + j) l.
Proof.
  induction l.
  - simpl.
    intros.
    destruct(le_lt_dec n0 n).
    simpl.
    destruct(le_lt_dec n0 (j + n)).
    apply f_equal. lia.
    lia.
    simpl.
    destruct(le_lt_dec n0 n).
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    auto.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto. 
Qed.

Fixpoint rew (i : nat) (s : nat -> Lambda) (l0 : Lambda) : Lambda :=
  match l0 with
  | 'm      => 
    match le_lt_dec i m with
    | left _  => sf 0 i (s (m - i)) (* i <= m *)
    | right _ => 'm                 (* m < i *)
    end
  | \ l     => \ (rew (S i) s l)
  | l1 @ l2 => (rew i s l1) @ (rew i s l2)
  end.
  Notation "l .[ i # s ]" := (rew i s l) (at level 20, left associativity).

Lemma sf_rew0 : forall l m i s, (sf m i l).[m + i# s] = l.[m# fun x => sf 0 i (s x)].
Proof.
  induction l.
  - simpl.
    intros.
    rewrite sf_sf.
    destruct(le_lt_dec m n).
    simpl.
    destruct(le_lt_dec (m + i) (i + n)).
    assert(i + n - (m + i) = n - m). lia. rewrite H.
    auto.
    lia.
    simpl.
    destruct(le_lt_dec (m + i) n).
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    assert(S (m + i) = (S m) + i). lia. rewrite H.
    auto.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto.
Qed.

Lemma sfm_sf0 : forall l m i, sf m i (sf 0 m l) = sf 0 (m + i) l.
Proof.
  assert(forall l m i j, sf (j + m) i (sf j m l) = sf j (m + i) l).
  - induction l.
    + simpl.
      intros.
      destruct(le_lt_dec j n).
      simpl.
      destruct(le_lt_dec (j + m) (m + n)).
      apply f_equal.
      lia.
      lia.
      simpl.
      destruct(le_lt_dec (j + m) n).
      lia.
      auto.
    + simpl.
      intros.
      apply f_equal.
      assert(S (j + m) = S j + m). lia. rewrite H.
      auto.
    + simpl.
      intros.
      rewrite IHl1.
      rewrite IHl2.
      auto.
  - intros.
    specialize (H l m i 0).
    simpl in H.
    auto.
Qed.

Lemma sf0i_rewi_sf0i : forall l i s, 
  (sf 0 i l).[i# s] = sf 0 i (l.[0# s]).
Proof.
  assert(forall l i m s, l.[m# fun x => sf 0 i (s x)] = sf m i (l.[m# s])).
  - induction l.
    + simpl.
      intros.
      rewrite sf_sf.
      destruct(le_lt_dec m n).
      simpl.
      rewrite sfm_sf0.
      auto.
      simpl.
      destruct(le_lt_dec m n).
      lia.
      auto.
    + simpl.
      intros.
      apply f_equal.
      auto.
    + simpl.
      intros.
      rewrite IHl1.
      rewrite IHl2.
      auto.
  - intros.
    assert(S := sf_rew0 l 0 i s).
    simpl in S.
    rewrite S.
    auto.
Qed.

Lemma nested_rew : forall l s0 s1 i, 
  l.[i# s0].[i# s1] = l.[i# fun x => s0 x.[0# s1]].
Proof.
  induction l.
  - simpl. intros.
    destruct(le_lt_dec i n).
    apply sf0i_rewi_sf0i.
    simpl.
    destruct(le_lt_dec i n).
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    auto.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto.
Qed.

Lemma sf__rew : forall l i j, sf i j l = l.[i# fun x => '(j + x)].
Proof.
  induction l.
  - simpl.
    intros.
    destruct (le_lt_dec i n).
    apply f_equal.
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    auto.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto.
Qed.

Lemma rew_i0 : forall l i s, 
  l.[i # s] = l.[0 # fun x => if (le_lt_dec i x) then sf 0 i (s (x - i)) else 'x].
Proof.
  assert(forall l i s j, l.[j + i # s] = l.[j # fun x => if (le_lt_dec i x) then sf 0 i (s (x - i)) else 'x]).
  - induction l.
    + simpl.
      intros.
      destruct (le_lt_dec (j + i) n).
      destruct (le_lt_dec j n).
      destruct (le_lt_dec i (n - j)).
      rewrite sf_sf.
      assert(n - (j + i) = n - j - i). lia. rewrite H.
      auto.
      lia.
      lia. 
      destruct (le_lt_dec j n).
      destruct (le_lt_dec i (n - j)).
      lia.
      simpl.
      apply f_equal. lia.
      auto.
    + simpl.
      intros.
      apply f_equal.
      assert(S (j + i) = (S j) + i). lia. rewrite H.
      auto.
    + simpl.
      intros.
      rewrite IHl1.
      rewrite IHl2.
      auto.
  - intros.
    specialize (H l i s 0).
    simpl in H.
    auto. 
Qed.

Lemma nested_rew_g : forall l s0 s1 i j, 
  l.[i# s0].[j# s1] = 
  l.[0# fun x => (if le_lt_dec i x then sf 0 i (s0 (x - i)) else 'x).[0# fun x0 => if le_lt_dec j x0 then sf 0 j (s1 (x0 - j)) else 'x0]].
Proof.
  intros.
  rewrite (rew_i0 l).
  rewrite (rew_i0 _).
  rewrite (nested_rew l).
  auto.
Qed.

Lemma rew_rew : forall l s0 s1 j, (forall i, s0 i = s1 i) -> l.[j# s0] = l.[j# s1].
Proof.
  intros.
  assert(s0 = s1).
  apply functional_extensionality. auto.
  rewrite H0.
  auto.
Qed.

Definition slide {A : Type} (a : A) (s : nat -> A) : nat -> A := fun x0 => 
  match x0 with
  | 0 => a
  | S m => s m
  end.
  
Definition embed {A : Type} (a : A) (s : nat -> A) : nat -> A := fun n => 
  match n with 
  | 0 => a 
  | _ => s n 
  end.

Notation "l .# i | x" := (l.[i# slide x \0]) (at level 40, left associativity).
Notation "l .| x" := (l.[0# slide x \0]) (at level 40, left associativity).

Lemma rew_sf : forall l k n, (sf 0 (S n) l) .# n | k = sf 0 n l.
Proof.
  intros.
  rewrite sf__rew.
  rewrite nested_rew_g.
  symmetry.
  rewrite sf__rew.
  apply rew_rew.
  intros.
  destruct (le_lt_dec 0 i).
  simpl.
  destruct (le_lt_dec n (S (n + (i - 0)))).
  assert (match n with | 0 => S (n + i) | S n0 => n + i - n0 end = S i).
  {destruct n. lia. lia. }
  rewrite <- minus_n_O.
  rewrite H.
  simpl.
  auto.
  lia.
  lia.
Qed.

Lemma rew_id : forall l n, l = l.[n# \0].
Proof.
    induction l.
    simpl.
    intros.
    destruct (le_lt_dec n0 n).
    apply f_equal. lia.
    auto.
    intros.
    simpl.
    apply f_equal.
    auto.
    intros.
    simpl.
    rewrite (IHl1 n) at 1.
    rewrite (IHl2 n) at 1.
    auto.
Qed.

Lemma rew_sfll : forall l k n, (sf n 1 l) .# n | k = l.
Proof.
  intros.  
  rewrite sf__rew.
  rewrite nested_rew_g.
  symmetry.
  rewrite (rew_id l 0) at 1.
  apply rew_rew.
  simpl.
  intros.
  destruct (le_lt_dec n i).
  simpl.
  rewrite <- minus_n_O.
  assert(n + S (i - n) = S i). lia.
  rewrite H.
  simpl.
  destruct (le_lt_dec n (S i)).
  simpl.
  assert(match n with | 0 => S i | S n0 => i - n0 end = S (i - n)).
  {destruct n. lia. lia. }
  rewrite H0.
  simpl.
  apply f_equal. lia.
  lia.
  Abort.
  
Fixpoint fv (l0 : Lambda) : nat :=
  match l0 with
  | 'n      => S n
  | \ l     => pred (fv l)
  | l1 @ l2 => max (fv l1) (fv l2)
  end.

Lemma fv_sf : forall l i k, fv l <= i -> sf i k l = l.
Proof.
  induction l.
  - simpl.
    intros.
    destruct (le_lt_dec i n).
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    apply IHl.
    lia.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto.
    lia.
    lia.
Qed.

Lemma fv_rew : forall l i s, fv l <= i -> rew i s l = l.
Proof.
  induction l.
  - simpl.
    intros.
    destruct (le_lt_dec i n).
    lia.
    auto.
  - simpl.
    intros.
    apply f_equal.
    apply IHl.
    lia.
  - simpl.
    intros.
    rewrite IHl1.
    rewrite IHl2.
    auto.
    lia.
    lia.
Qed.

Lemma fv0_sf l : fv l = 0 -> forall n, sf 0 n l = l.
Proof.
  intros.
  apply fv_sf.
  lia.
Qed.

Lemma fv0_rew l : fv l = 0 -> forall i s, rew i s l = l.
Proof.
  intros.
  apply fv_rew.
  lia.
Qed.
