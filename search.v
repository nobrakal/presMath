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
    contradict n_a.
    rewrite isTrueEq.
    rewrite beq_nat_true_iff.
    exact (not_eq_sym H0).
    - intros ok. exact ok.
Qed.

Theorem search_ok (n: nat) (lst: list nat): In n lst <-> Is_true (search n lst).
Proof.
  split.
  - induction lst.
    -- simpl.
      intros false. exact false.

    -- intros ou.
      case ou.

      --- intros a_n.
        apply isTrueEq.
        rewrite -> recSearch.
        rewrite orb_true_iff.
        refine (or_introl _).
        rewrite beq_nat_true_iff.
        exact (eq_sym a_n).

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
      case (eq_nat_decide a n).
      --- intros a_n.
          simpl.
          refine (or_introl _).
          apply eq_nat_is_eq.
          exact a_n.
      --- intros na_n.
          simpl.
          refine (or_intror _).
          apply IHlst.
          apply inTail in H.
          exact H.
          rewrite <- eq_nat_is_eq.
          exact na_n.
Qed.