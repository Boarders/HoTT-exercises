From HoTT Require Import HoTT.
(* By default, the HoTT library does not dump a bunch of notations in your
   scope.  However, these notations are tremendously useful, so most users
   of the HoTT library will want to open these two scopes, which introduce
   notations for paths and for equivalences.  The Cliff's notes version of
   these notations:
Notation "1" := idpath : path_scope.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Notation "p ^" := (inverse p) (at level 3) : path_scope.
Notation "p # x" := (transport _ p x) (right associativity, at level 65) : path_scope.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
NB: ^ and ^-1 bind quite tightly, so it's not uncommon to see terms like 'f^-1 a'
or '(f a)^-1'.
*)
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope fibration_scope.

(* There are also a number of other notations which /are/ enabled by default. The
most important ones are these:
Notation idmap := (fun x => x).
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Notation "x .2" := (projT2 x) (at level 3) : fibration_scope.
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.
Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.
NB: When writing code using the projT* notations, the space is usually omitted,
as in 'x.1' or 'p..2'. Coq will format it with a space, however.
 *)

(* Exercise 1.1  *)
(* Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C.
Show that we have h ◦ (g ◦ f ) ≡ (h ◦ g) ◦ f . *)
Definition comp {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).

Theorem comp_assoc : forall {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D),
    comp h (comp g f) = comp (comp h g) f.
Proof.
  reflexivity.
Qed.

(* Exercise 1.2  *)
(* Derive the recursion principle for products recA×B using only the projections, and
verify that the definitional equalities are valid. Do the same for Σ-types. *)
Definition prod_rec {A B C : Type} (f : A -> (B -> C)) (p : A * B) : C :=
  f (fst p) (snd p).

Theorem prod_comp : forall {A B C : Type} (f : A -> (B -> C)) (a : A) (b : B),
    prod_rec f (a , b) = f a b.
Proof.
  reflexivity.
Qed.


Definition sigma_rec {A B : Type} {P : A -> Type}
           (f : forall (a : A), P a -> B) (p : { a | P a}) : B :=
  f (p .1) (p .2).



Theorem sigma_comp :
  forall {A B : Type} {P : A -> Type}
         (f : forall (a : A), P a -> B) (a : A) (pa : P a),
    sigma_rec f (a ; pa) = f a pa.
Proof.
  reflexivity.
Qed.


(*
Exercise 1.3. Derive the induction principle for products indA×B, using only the projections and
the propositional uniqueness principle uniqA×B. Verify that the definitional equalities are valid.
Generalize uniqA×B to Σ-types, and do the same for Σ-types.
 *)

Theorem prod_uniq :
  forall {A B : Type} {p : A * B},
    (fst p, snd p) = p.
Proof.
  intros A B [p1 p2]. reflexivity.
Qed.

Definition prod_ind :
  forall {A B : Type} {P : A * B -> Type}
         (f : forall (a : A) (b : B), P (a , b)) (p : A * B), P p.
Proof.
  intros A B P f p. apply (transport P prod_uniq). exact (f (fst p) (snd p)).
Qed.

Theorem sigma_uniq :
  forall {A : Type} {P : A -> Type} {p : {a | P a}},
    (p .1; p .2) = p.
Proof.
  intros A B [p1 p2]. reflexivity.
Qed.

Definition sigma_ind :
  forall {A : Type} {P : A -> Type} {Q : {a | P a} -> Type}
         (f : forall (a : A) (p : P a), Q (a ; p)) (p : {a | P a}), Q p.
Proof.
  intros A P Q f p. apply (transport Q sigma_uniq). exact (f (p .1) (p .2)).
Qed.

(*
Exercise 1.4. Assuming as given only the iterator for natural numbers:

    iter : (C : U) -> (C -> C) -> nat → C

with the defining equations:

    iter ( C, c 0 , c s , 0 ) : ≡ c 0 ,
    iter ( C, c 0 , c s , succ ( n )) : ≡ c s ( iter ( C, c 0 , c s , n ))

derive a function having the type of the recursor rec N . Show that the defining equations of the
recursor hold propositionally for this function, using the induction principle for N.
 *)

Module nat_rec.
Local Open Scope nat_scope.

Fixpoint nat_iter (C : Type) (c0 : C) (csuc : C -> C) (n : nat) : C :=
  match n with
  | 0 => c0
  | S n => csuc (nat_iter C c0 csuc n)
  end.

Definition sigsuc (P : nat -> Type) (psuc : forall n, P n -> P (S n)) (p : {n | P n}) : {n | P n} :=
  match p with
  | (n ; pn) => (S n; psuc _ pn)
  end.

Definition nat_rec' (P : nat -> Type) (p0 : P 0) (psuc : forall n, P n -> P (S n)) (n : nat) : {n | P n} :=
  nat_iter (sig P) (0 ; p0) (sigsuc P psuc) n.

Lemma nat_rec_proj1 :
  forall (P : nat -> Type) (p0 : P 0) (psuc : forall n, P n -> P (S n)) (n : nat),
    (nat_iter (sig P) (0 ; p0) (sigsuc P psuc) n) .1 = n.
Proof.
  intros P p0 psuc n. induction n as [| n' IH].
  - reflexivity.
  - simpl.  rewrite -> IH. reflexivity.
Qed.

Definition nat_rec (P : nat -> Type) (p0 : P 0) (psuc : forall n, P n -> P (S n)) (n : nat) : P n.
Proof.
  - rewrite <- (nat_rec_proj1 P p0 psuc n).
    exact ((nat_iter (sig P) (0 ; p0) (sigsuc P psuc) n) .2).
Qed.

Close Scope nat_scope.
End nat_rec.
(*
Exercise 1.5.
Show that if we define A + B : ≡ ∑ ( x:2 ) rec 2 (U , A, B, x ) , then we can give a definition
of ind A + B for which the definitional equalities stated in §1.7 hold.
 *)
(* The Bool type from Types/Bool.v is called Bool in the HoTT library *)
Definition Sum (A : Type) (B : Type) :=
  sig (Bool_rect (fun _ => Type) A B).

Definition my_inl {A : Type} (B : Type) (a : A) : Sum A B :=
  (true ; a).

Definition my_inr {B : Type} (A : Type) (b : B) : Sum A B :=
  (false ; b).

Definition sum_ind {A B C : Type} (on_left : A -> C) (on_right : B -> C) (e : Sum A B) : C.
Proof.
  refine
    (sig_rect
      Bool
      (Bool_rect (fun _ => Type) A B)
      (fun _ => C)
      _
      e).
  intros b e_b.
  destruct b.
  - simpl in e_b. apply on_left. exact e_b.
  - simpl in e_b. apply on_right. exact e_b.
Defined.

Lemma sum_ind_inl
  : forall {A B C : Type} (on_left : A -> C) (on_right : B -> C) (a : A),
    sum_ind on_left on_right (my_inl B a) = on_left a.
Proof.
  reflexivity.
Qed.

Lemma sum_ind_inr
  : forall {A B C : Type} (on_left : A -> C) (on_right : B -> C) (b : B),
    sum_ind on_left on_right (my_inr A b) = on_right b.
Proof.
  reflexivity.
Qed.

(*
Exercise 1.6. Show that if we define
  A × B : ≡ ∏ ( x:2 ) rec 2 (U , A, B, x ),
then we can give a definition of ind A × B for which the definitional equalities
stated in §1.5 hold propositionally (i.e. using equality types).
*)

Definition Prod (A : Type) (B : Type) :=
  forall b : Bool, Bool_rect (fun _ => Type) A B b.

Definition proj_1 {A B : Type} (p : Prod A B) : A :=
  p true.

Definition proj_2 {A B : Type} (p : Prod A B) : B :=
  p false.

Definition Prod_intro {A B : Type} (a : A) (b : B) : Prod A B := fun x =>
  match x with
  | true => a
  | false => b
  end.

Definition Prod_ind {A B C : Type} (f : A -> (B -> C)) (p : Prod A B) : C :=
  f (proj_1 p) (proj_2 p).

Lemma Prod_ind_compute
  : forall {A B C : Type} (f : A -> (B -> C)) (a : A) (b : B),
      (Prod_ind f (Prod_intro a b)) = f a b.
Proof.
  reflexivity.
Qed.

(*
Exercise 1.7. Give an alternative derivation of
  ind'=A from ind=A
which avoids the use of universes.
(This is easiest using concepts from later chapters.)
 *)

Set Printing Implicit.

Section based_path_induction.
  Variable A : Type.
  Variable a : A.

  Definition based_path_space : Type :=
    sig (fun x => a = x).

  Definition
    free_path_ind : forall (P : forall (x y : A) (p : x = y), Type)
                           (x y : A) (p : x = y) (p0 : P x x idpath), P x y p.
  Proof.
    intros P x y p p0. apply paths_ind. assumption.
  Defined.

  Instance pathspace_contr : Contr based_path_space.
  Proof.
    - refine (Build_Contr _ (a ; idpath) _).
      * intros [x p].
        exact (free_path_ind (fun a x p => (a; idpath) = (x; p)) a x p idpath).
  Defined.

  Definition based_path_ind (C : forall (x : A) (p : a = x), Type)
           (c_refl : C a idpath) : forall (x : A) (p : a = x), C x p.
  Proof.
    apply equiv_sig_ind'. intros sg.
    assert (H : (a ; idpath) = sg).
    { exact (@contr based_path_space pathspace_contr sg).}
    exact (transport (fun sg => C sg.1 sg.2) H c_refl).
  Defined.
End based_path_induction.
(*
Exercise 1.8
Define multiplication and exponentiation using rec N . Verify that:
   (N, + , 0, × , 1) is a semiring using only ind N .
You will probably also need to use symmetry and transitivity of
equality, Lemmas 2.1.1 and 2.1.2.
 *)
  (* symmetry of equality (2.1.1) corresponds to the symmetry tactic *)
  (* transitivity of equality is given by @ notation *)

Section Semiring_nat.

  Definition add : nat -> nat -> nat.
  Proof.
    refine (nat_ind (fun _ => nat -> nat) _ _).
    (* zero case *)
    * exact id.
    (* successor case *)
    * intros n add_n m. exact (S (add_n m)).
  Defined.

  Definition mult : nat -> nat -> nat.
  Proof.
    refine (nat_ind (fun _ => nat -> nat) _ _).
    (* zero case *)
    * intros _. exact 0%nat.
    (* successor case *)
    * intros n mul_n m. exact (add m (mul_n m)).
  Defined.

  Definition exp_rev : nat -> nat -> nat.
  Proof.
    refine (nat_ind (fun _ => nat -> nat) _ _).
    (* zero case *)
    * intros _. exact 1%nat.
    (* successor case *)
    * intros n exp_n m. exact (mul m (exp_n m)).
  Defined.

  Definition exp : nat -> nat -> nat := flip exp_rev.

  Variable
    n m l : nat.

  (* proof that addition is a commutative monoid *)
  Lemma add_id_l : (add 0 n) = n.
  Proof.
    reflexivity.
  Defined.

  Lemma add_id_r : forall n, (add n 0) = n.
  Proof.
    refine (nat_ind (fun n => (add n 0) = n) _ _).
    * reflexivity.
    * intros n' IH. simpl. rewrite IH. reflexivity.
  Defined.

  Lemma add_assoc : forall m n l, add (add m n) l = add m (add n l).
  Proof.
    refine (nat_ind _ _ _).
    * reflexivity.
    * intros n' IH m' l'. simpl. rewrite -> IH. reflexivity.
  Defined.

  Lemma succ_r : forall n m, add n (S m) = (S (add n m)).
  Proof.
    refine (nat_ind _ _ _).
    * reflexivity.
    * intros n' IH m'.  simpl. rewrite IH. reflexivity.
  Defined.

  Lemma add_comm : forall n m, add n m = add m n.
  Proof.
    refine (nat_ind _ _ _).
    * intros m'.  rewrite (add_id_r m'). reflexivity.
    * intros n' IH m'. simpl. rewrite IH. rewrite succ_r. reflexivity.
  Defined.

  (* Proof that multiplication defines a monoid *)

  Lemma mult_id_l : forall n, (mult 1 n) = n.
  Proof.
    refine (nat_ind _ _ _).
    * reflexivity.
    * intros n' IH. simpl. rewrite add_id_r. reflexivity.
  Defined.

  Lemma mult_id_r : forall n, (mult n 1) = n.
  Proof.
    refine (nat_ind _ _ _).
    * reflexivity.
    * intros n' IH. simpl. rewrite IH. reflexivity.
  Defined.

  (* show show annihilation and distributivity axioms *)
  Lemma mult_0_r : forall n, (mult n 0%nat) = 0%nat.
  Proof.
    refine (nat_ind _ _ _).
    * reflexivity.
    * intros n' IH. simpl. rewrite IH. reflexivity.
  Defined.

  Lemma mult_dist_r : forall m n l, (mult (add m n) l) = add (mult m l) (mult n l).
  Proof.
    refine (nat_ind _ _ _).
    * intros n' l'. reflexivity.
    * intros m' IH n' l'. simpl. rewrite IH. rewrite add_assoc. reflexivity.
  Defined.

  Lemma mult_assoc : forall m n l, (mult (mult m n) l) = mult m (mult n l).
  Proof.
    refine (nat_ind _ _ _).
    * intros n' l'. reflexivity.
    * intros m' IH n' l'. simpl.  rewrite <- IH. rewrite mult_dist_r. reflexivity.
  Defined.

End Semiring_nat.
(*
Exercise 1.9.
Define the type family Fin : N → U mentioned at the end of §1.3, and the
dependent function fmax : ∏ ( n:N ) Fin ( n + 1 ) mentioned in §1.4.
*)

  Section Fin.

    Fixpoint Fin (n : nat) : Type :=
      match n with
      | 0%nat => Empty
      | (S n) => sum Unit (Fin n)
      end.

    Definition fmax : forall (n : nat), Fin (S n).
    Proof.
      refine (nat_rec _ _ _).
      * exact (inl tt).
      * intros n max_n. exact (inr max_n).
    Defined.

  End Fin.

(*
Exercise 1.10. Show that the Ackermann function ack : N → N → N is definable using only
rec N satisfying the following equations:

  ack ( 0, n ) ≡ succ ( n ) ,
  ack ( succ ( m ) , 0 ) ≡ ack ( m, 1 ) ,
  ack ( succ ( m ) , succ ( n )) ≡ ack ( m, ack ( succ ( m ) , n )).

 *)

Definition ack : nat -> nat -> nat.
Proof.
  refine (nat_rec _ _ _).
    (* ack 0 n = succ n *)
  - exact succ.
  - intros m ack_m.
    Check nat_rec.
    refine (nat_rec _ _ _).
    (* ack (succ m) 0 = ack m 1 *)
    * exact (ack_m 1%nat).
    * intros ack_succ_m_0 ack_succ_m_n.
      refine (ack_m _).
    (* ack (succ m) (succ n) = ack m (ack (succ m) n) *)
      exact ack_succ_m_n.
    Defined.

Compute ack (succ 0) 0.

Lemma ack_0 : forall m , ack (succ m) 0 = ack m 1.
Proof.
  reflexivity.
Qed.

Lemma ack_n : forall m n, ack (succ m) (succ n) = ack m (ack (succ m) n).
Proof.
  reflexivity.
Qed.

(* Exercise 1.11. Show that for any type A, we have ¬¬¬ A → ¬ A. *)
Section dne.
  Variable A : Type.

  Theorem dne_stable : ~~~ A -> ~A.
  Proof.
    intros not_not_not_a a. apply not_not_not_a. intros not_a. apply not_a. exact a.
  Defined.
End dne.

(*
Exercise 1.12.
Using the propositions as types interpretation, derive the following tautologies.
(i) If A, then (if B then A).
(ii) If A, then not (not A).
(iii) If (not A or not B), then not (A and B).
 *)
Section tautologies.
  Variable A B : Type.

  Lemma taut_1 (a : A) : forall (b : B), A.
  Proof.
    intros _. exact a.
  Defined.

  Lemma taut_2 (a : A) : ~~A.
  Proof.
    intros not_a. apply not_a. exact a.
  Defined.

  Lemma taut_3 (p : sum (~A) (~B)) : ~ (A * B).
  Proof.
    intros [a b]. Locate sum. destruct p as [not_a | not_b].
    * apply not_a. exact a.
    * apply not_b. exact b.
  Defined.

End tautologies.

(*
Exercise 1.13. Using propositions-as-types, derive the double negation of the principle of ex-
cluded middle, i.e. prove not (not (P or not P)).
*)

Section excl_middle_stable.
  Variable P : Type.
  Theorem excl_middle_stable : ~ ~ (sum P (~ P)).
  Proof.
    intros not_em_p. apply not_em_p. right. intros p. apply not_em_p. left. exact p.
  Defined.

End excl_middle_stable.

(*
Exercise 1.16. Show that addition of natural numbers is commutative:

(i,j : nat ) (i + j = j + i)
*)


Section nat_comm.

  Lemma nat_r_id : forall i : nat, add i 0 = add 0 i.
  Proof.
    refine (nat_ind (fun i => add i 0 = add 0 i) _ _).
    - reflexivity.
    - intros n IH. simpl. rewrite IH. reflexivity.
  Defined.

  Lemma nat_succ_r : forall j i : nat, add i (succ j) = succ (add i j).
  Proof.
    intros j.
    refine (nat_ind (fun i => add i (succ j) = succ (add i j)) _ _).
    - reflexivity.
    - intros n IH. simpl. rewrite IH. reflexivity.
    Qed.

  Theorem nat_comm : forall i j : nat, add i j = add j i.
  Proof.
    intros i.
    refine (nat_ind (fun j => add i j = add j i) _ _).
    * exact (nat_r_id i).
    * intros n IH.  rewrite nat_succ_r. simpl. rewrite IH. reflexivity.
  Defined.
