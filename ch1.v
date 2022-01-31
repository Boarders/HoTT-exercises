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
(*
Exercise 1.5.
Show that if we define A + B : ≡ ∑ ( x:2 ) rec 2 (U , A, B, x ) , then we can give a definition
of ind A + B for which the definitional equalities stated in §1.7 hold.
 *)
(* The Bool type from Types/Bool.v is called Bool in the HoTT library *)
Definition Sum (A : Type) (B : Type) :=
  sig (Bool_rect (fun _ => Type) A B).

Definition inl {A : Type} (B : Type) (a : A) : Sum A B :=
  (true ; a).

Definition inr {B : Type} (A : Type) (b : B) : Sum A B :=
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
    sum_ind on_left on_right (inl B a) = on_left a.
Proof.
  reflexivity.
Qed.

Lemma sum_ind_inr
  : forall {A B C : Type} (on_left : A -> C) (on_right : B -> C) (b : B),
    sum_ind on_left on_right (inr A b) = on_right b.
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
    Check (transport, sig).
    Check equiv_sig_ind'.
    Check sig.
    assert (C_cur : forall (p : {x | a = x}), Type).
    { exact (fun sg => C sg.1 sg.2).
    }
    Check equiv_sig_ind'.
    exact (transport (fun sg => C sg.1 sg.2) H c_refl).
  Defined.
