Require Import Arith.EqNat.
Require Import Bool.
Require Import List.

Fixpoint search (n : nat) (lst : list nat) := 
  match lst with
  | nil => false
  | cons n' lst' => if (beq_nat n n') then true else search n lst'
  end.

Lemma searchEmpty (n : nat): search n nil = false.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma recSearch (n : nat) (n': nat) (lst : list nat): search n (n'::lst) = orb (beq_nat n n') (search n lst).
Proof.
  auto.
Qed.

Lemma isTrueEq (b:bool): Is_true b <-> b = true.
Proof.
  split.
  - apply Is_true_eq_true.
  - apply Is_true_eq_left.
Qed.

Lemma inTail (n:nat) (a:nat) (lst:list nat): Is_true (search n (a::lst)) -> a <> n ->  Is_true (search n lst).
Proof.
  intros.
  rewrite recSearch in H.
  apply orb_prop_elim in H.
  case H.
    - intros n_a.
    apply isTrueEq in n_a.
    apply beq_nat_true in n_a.
    contradict n_a.
    exact (not_eq_sym H0).
    - intros ok. exact ok.
Qed.

(* Copied from Arith.PeanoNat, as my coq can find it *)
Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n; destruct m.
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.

Theorem search_ok (n: nat) (lst: list nat): In n lst <-> Is_true (search n lst).
Proof.
  split.
  - induction lst.
    -- simpl.
      intros false. exact false.

    -- intros ou.
      case ou.

      --- intros a_n.
        rewrite a_n.
        apply isTrueEq.
        rewrite -> recSearch.
        rewrite <- beq_nat_refl.
        apply orb_true_l.

     --- intros in_n.
        rewrite -> recSearch.
        apply IHlst in in_n.
        apply isTrueEq.
        apply isTrueEq in in_n.
        apply orb_true_iff.
        refine (or_intror _).
        exact in_n.

  - induction lst.
    -- simpl.
      intros false. exact false.

    -- intros H.
      case (eq_dec a n).
      --- intros a_n.
          simpl.
          refine (or_introl _).
          exact (a_n).
      --- intros na_n.
          simpl.
          refine (or_intror _).
          apply IHlst.
          apply inTail in H.
          exact H.
          exact na_n.
Qed.