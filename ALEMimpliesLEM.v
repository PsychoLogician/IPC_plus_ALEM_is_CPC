From Coq Require Import Lists.List. Import ListNotations.

Inductive formula:= 
  | bot
  | p(i: nat)
  | conj (p1: formula) (p2: formula)
  | disj (p1: formula) (p2: formula)
  | impl (p1: formula) (p2: formula).

Notation " ⊥ " := bot (at level 9).
Notation "A ∧ B" := (conj A B) (at level 90, left associativity).
Notation "A ∨ B" := (disj A B) (at level 90, left associativity).
Notation "A → B" := (impl A B) (at level 80, right associativity).
Notation "¬ A"   := (A → ⊥)   (at level 50, left associativity).

Definition context := list formula.

Reserved Notation " Γ ⊢ A " (at level 95).

Inductive ND: context -> formula -> Prop :=
  | in_cont (Γ: context)(A: formula): In A Γ -> Γ ⊢ A

  | conj_i   (Γ: context)(A B: formula): Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ A ∧ B
  | conj_e_l (Γ: context)(A B: formula): Γ ⊢ A ∧ B -> Γ ⊢ A
  | conj_e_r (Γ: context)(A B: formula): Γ ⊢ A ∧ B -> Γ ⊢ B

  | disj_i_l (Γ: context)(A B: formula): Γ ⊢ A -> Γ ⊢ A ∨ B
  | disj_i_r (Γ: context)(A B: formula): Γ ⊢ B -> Γ ⊢ A ∨ B
  | disj_e (Γ: context)(A B C: formula): Γ ⊢ A ∨ B -> A::Γ ⊢ C -> B::Γ ⊢ C -> Γ ⊢ C

  | impl_i (Γ: context)(A B: formula): A::Γ ⊢ B -> Γ ⊢ A → B
  | impl_e (Γ: context)(A B: formula): Γ ⊢ A → B -> Γ ⊢ A -> Γ ⊢ B 

  | exf (Γ: context)(A: formula): Γ ⊢ ⊥ -> Γ ⊢ A

  (* atomic law of the excluded middle *)
  | A_LEM (Γ: context)(i: nat): Γ ⊢ p i ∨ ¬ p i
where "Γ ⊢ A" := (ND Γ A).

Definition sublist{A} (l1 l2: list A):= forall a, In a l1 -> In a l2.

Lemma In_ext: forall A: Type, forall a: A, forall l1 l2: list A, 
  sublist l1 l2 -> sublist (a::l1) (a::l2).
Proof. unfold sublist. intros. destruct H0; [left| right; apply H]; assumption. Qed.

Lemma condensing_permutation: forall A Γ, Γ ⊢ A -> 
  forall Γ':context, sublist Γ Γ' -> Γ' ⊢ A.
  
Proof. intros. generalize dependent Γ'. induction H; intros Γ' H'.

  - apply in_cont. apply H'. apply H.

  - apply conj_i.
    + apply IHND1; assumption.
    + apply IHND2; assumption.
  - apply conj_e_l with (B:= B). apply IHND; assumption.
  - apply conj_e_r with (A:= A). apply IHND; assumption.

  - apply disj_i_l. apply IHND; assumption.
  - apply disj_i_r. apply IHND; assumption.
  - apply (disj_e Γ' A B).
    + apply IHND1. assumption.
    + apply IHND2. apply In_ext. assumption.
    + apply IHND3. apply In_ext. assumption.

  - apply impl_i. apply IHND. apply In_ext; assumption.
  - apply impl_e with (A:= A).
    + apply IHND1; assumption.
    + apply IHND2; assumption.

  - apply exf. apply IHND; assumption.

  - apply A_LEM.
Qed.

Theorem atomic_LEM_concludes_LEM: forall A: formula, nil ⊢ A ∨ ¬ A.
Proof. induction A.

  (* ⊥ ∨ ¬ ⊥ *)
  - apply disj_i_r. apply impl_i. apply in_cont. left; reflexivity.

  (* p i ∨ ¬ p i *)
  - apply (A_LEM nil).

  (* A1 ∧ A2 ∨ ¬ (A1 ∧ A2) *)
  - apply (disj_e nil A1 (¬ A1)).
    + assumption.
    + apply (disj_e [A1] A2 (¬ A2)).
      * apply (condensing_permutation (A2 ∨ ¬ A2) nil); try assumption; intros B H; destruct H.
      * apply disj_i_l. apply conj_i; apply in_cont; simpl; [right; left| left]; reflexivity.
      * apply disj_i_r. apply impl_i. apply impl_e with (A:= A2).
        -- apply in_cont. right; left; reflexivity.
        -- apply conj_e_r with (A:= A1). apply in_cont. left; reflexivity.
    + apply disj_i_r. apply impl_i. apply impl_e with (A:= A1).
      -- apply in_cont. right; left; reflexivity.
      -- apply conj_e_l with (B:= A2). apply in_cont. left; reflexivity.

  (* A1 ∨ A2 ∨ ¬ (A1 ∨ A2) *)
  - apply (disj_e nil A1 (¬ A1)).
    + assumption.
    + apply disj_i_l. apply disj_i_l. apply in_cont. left; reflexivity.
    + apply (disj_e [¬ A1] A2 (¬ A2)).
      * apply (condensing_permutation (A2 ∨ ¬ A2) nil); try assumption; intros B H; destruct H.
      * apply disj_i_l. apply disj_i_r. apply in_cont. left; reflexivity.
      * apply disj_i_r. apply impl_i. apply (disj_e [A1 ∨ A2; ¬ A2; ¬ A1] A1 A2).
        -- apply in_cont. left; reflexivity.
        -- apply impl_e with (A:= A1); apply in_cont;
          [right; right; right; left|left]; reflexivity.
        -- apply impl_e with (A:= A2); apply in_cont;
          [right; right; left|left]; reflexivity.

  (* A1 → A2 ∨ ¬ (A1 → A2) *)
  - apply (disj_e nil A2 (¬ A2)).
    + assumption.
    + apply disj_i_l. apply impl_i. apply in_cont. right; left; reflexivity.
    + apply (disj_e [¬ A2] A1 (¬ A1)).
      * apply condensing_permutation with (Γ:= nil); try assumption; intros B H; destruct H.
      * apply disj_i_r. apply impl_i. apply impl_e with (A:= A2).
        -- apply in_cont. right; right; left; reflexivity.
        -- apply impl_e with (A:= A1); apply in_cont; [left| right; left]; reflexivity.
      *apply disj_i_l. apply impl_i. apply exf. apply impl_e with (A:= A1); apply in_cont; [right; left| left]; reflexivity.
Qed.