From HoTT Require Import HoTT.
From HoTT.Basics Require PathGroupoids.
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

(* 
Exercise 2.1. Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.

Lemma 2.1.2: 
Given:
  A : Type, 
  a b c : A

We have a function:
  (a = b) -> (b = c) -> (x = z)
 *)
Section trans_pfs.
  Context {A : Type}.
    Definition
      free_path_ind : forall (P : forall (x y : A) (p : x = y), Type)
                           (x y : A) (p : x = y) (p0 : P x x idpath), P x y p.
    Proof.
      intros P x y p p0. apply paths_ind. assumption.
    Defined.

 
  Theorem trans1 : forall {x y z : A}, (x = y) -> (y = z) -> (x = z).
  Proof.
    enough (H : forall x y : A, (x = y) -> forall z, (y = z) -> (x = z)).
    - intros x y z p q. exact (H x y p z q).
    - intros x y p.
      refine (free_path_ind (fun x y q => forall z, (y = z) ->  (x = z)) x y p _).
      ** refine (@paths_ind A x (fun z q => x = z) _).
         exact idpath.
  Defined.

  Theorem trans2 : forall {x y z : A}, (x = y) -> (y = z) -> (x = z).
  Proof.
    enough (H : forall x y : A, (x = y) -> forall z, (y = z) -> (x = z)).
    - intros x y z p q. exact (H x y p z q).
    - intros x y p.
      refine (free_path_ind (fun x y q => forall z, (y = z) ->  (x = z)) x y p _).
      ** intros z q. exact q.
  Defined.

  Theorem trans3 : forall {x y z : A}, (x = y) -> (y = z) -> (x = z).
  Proof.
    enough (H : forall x y : A, (x = y) -> forall z, (y = z) -> (x = z)).
    - intros x y z p q. exact (H x y p z q).
    - intros x y p. Check paths_ind.
      refine (@paths_ind A y (fun z q => x = z) _).
      * exact p.
  Defined.

  Context {x y z : A}.
  Theorem trans1_eq_2 : forall (p : x = y) (q : y = z), (trans1 p q) = (trans2 p q).
  Proof.
    refine
      (@paths_ind A x (fun y p => forall (q : y = z), trans1 p q = trans2 p q) _ y).
    refine
      (@paths_ind A x (fun z q => trans1 _ q = trans2 _ q) _ z).
    exact idpath.
  Defined.

  Theorem trans2_eq_3 : forall (p : x = y) (q : y = z), (trans2 p q) = (trans3 p q).
  Proof.
    refine
      (@paths_ind A x (fun y p => forall (q : y = z), trans2 p q = trans3 p q) _ y).
    refine
      (@paths_ind A x (fun z q => trans2 _ q = trans3 _ q) _ z).
    exact idpath.
  Defined.

  Theorem trans1_eq_3 : forall (p : x = y) (q : y = z), (trans1 p q) = (trans3 p q).
  Proof.
    refine
      (@paths_ind A x (fun y p => forall (q : y = z), trans1 p q = trans3 p q) _ y).
    refine
      (@paths_ind A x (fun z q => trans1 _ q = trans3 _ q) _ z).
    exact idpath.
  Defined.
End trans_pfs.

Section trans_pfs_comm.
  
(*
Exercise 2.2. Show that the three equalities of proofs constructed in the previous exercise form a
commutative triangle. In other words, if the three definitions of concatenation are denoted by
(trans1 p q), (trans2 p q), and (trans3 p q), then the concatenated equality:

  (trans1 p q) = (trans2 p q) = (trans3 p q)

is equal to the equality (trans1 p q) = (trans3 p q).
 *)
  Variable A : Type.
  Variable x y z : A.
                 
  Theorem trans_comm_triangle
    : forall (p : x = y) (q : y = z),
      (trans1_eq_2 p q @ trans2_eq_3 p q) =
      (trans1_eq_3 p q).
  Proof.
    refine
      (@paths_ind A x
      (fun y p => forall (q : y = z), (trans1_eq_2 p q @ trans2_eq_3 p q) = (trans1_eq_3 p q)) _ y).
    refine
      (@paths_ind A x (fun z q => (trans1_eq_2 _ q @ trans2_eq_3 _ q) = (trans1_eq_3 _ q)) _ z).
    exact idpath.
  Defined.

  End trans_pfs_comm.

(*
Exercise 2.3. Give a fourth, different, proof of Lemma 2.1.2, and prove that it is equal to the others.
 *)
Section transport_trans.
  Variable A : Set.
  Theorem trans_4 : forall x y z : A, (x = y) -> (y = z) -> (x = z).
  Proof.
    intros x y z p q.
    exact (transport (fun x' => x' = z) (p ^) q).
  Defined.

End transport_trans.

(*
Exercise 2.4 
Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths.

n-paths:

n = 0 - A 0-path is a point
            x
            .   : 0-path A
n = 1 - A 1-path is a equality between two 0-paths i.e. x, y : A, x = y
          x   y
          . ~ . : 1-path A
n = 2 - A 2-path is an equality between one paths i.e. p q : n_path 1, p = q.
            p
          . ~ .
          |   |  : 2-path A
          . ~ .
            q
...
*)

Section n_path.
  Variable A : Type.
        
  Fixpoint n_path (n : nat) : Type :=
    match n with
    | O => A
    | S n' => {x : n_path n' & ({y : n_path n' & (x = y)})}
    end.
End n_path.

Eval compute in (n_path nat 2).
(*
Exercise 2.5. Prove that the functions (2.3.6) and (2.3.7) are inverse equivalences.

A B : Type
x y : A
p   : x = y
f   : A -> B

(2.3.6): 
  (f x = f y) -> (p_*(f x) = f y)

(2.3.7):
  (p_*(f x) = f y) -> f x = f y

*)
Module non_dep_apd.
  Check transport_const.

  Lemma forward {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
    (f x = f y) -> (transport (fun _ => B) p (f x)) = (f y).
  Proof.
    intros f_path.
    refine (transport_const p (f x) @ _).
    exact f_path.
  Defined.

  Lemma backward {A B : Type} (f : A -> B) {x y : A} (p : x = y) : (transport (fun _ => B) p (f x)) = (f y) -> (f x) = (f y).
  Proof.
    intros f_apd_p.
    Check transport_const.
    refine ((transport_const p (f x)) ^ @ _).
    exact f_apd_p.
  Defined.

  Theorem for_back {A B : Type} (f : A -> B) {x y : A} {p : x = y} (f_p : f x = f y) :
    forward f p o backward f p == idmap.
  Proof.
    intros dep_eq.
    
    unfold forward. unfold backward.
    path_induction.
    reflexivity.
  Defined.

  Theorem back_for {A B : Type} (f : A -> B) {x y : A} {p : x = y} (f_p : f x = f y) :
    backward f p o forward f p == idmap.
  Proof.
    intros dep_eq.
    unfold forward. unfold backward.
    path_induction.
    reflexivity.
  Defined.

  (* Theorem triangle_law  *)


  Instance ex_2_4 {A B : Type} (f : A -> B) {x y : A} {p : x = y} (f_p : f x = f y) :
    IsEquiv (forward f p).
  Proof.
    Check Build_IsEquiv.
    refine (Build_IsEquiv _ _ (forward f p) (backward f p) (for_back f f_p) (back_for f f_p) _).
    - 
    
    
    
      
    
  
  
    
End non_dep_apd.

