From ITree Require Import
  ITree
  Eq
  Basics.Monad.

From ExtLib Require Import
     Structures.Functor.

From Coq Require Import 
     Morphisms.

Definition PropT (E: Type -> Type) (X: Type): Type :=
  itree E X -> Prop.

Definition eutt_closed {E X} (P: itree E X -> Prop): Prop :=
  Proper (eutt eq ==> iff) P.

#[global] Polymorphic Instance Eq1_PropT {E} : Eq1 (PropT E) :=
  fun a PA PA' =>
    (forall x y, x ≈ y -> (PA x <-> PA' y)) /\
      eutt_closed PA /\ eutt_closed PA'.

  Definition PropT_itree_map {E F X} (f : itree E X -> itree F X) (pe : PropT E X) : PropT F X
    := fun tf => exists te, pe te /\ f te ≈ tf.

  #[global] Instance Functor_Prop {E}
    : Functor (PropT E) :=
    {| fmap := fun A B f PA b => exists (a: itree E A), PA a /\ b = fmap f a |}.

  Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
  | ReturnsRet: forall t, t ≈ Ret a -> Returns a t
  | ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
  | ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
  .
  Hint Constructors Returns: core.

  (* Definition 5.1 *)
  Definition bind_PropT {E} :=
    fun A B (specA : PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        specA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

  Definition bind_PropT_stronger {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A) (k: A -> itree E B),
        PA ta /\
        tb ≈ bind ta k /\
        (forall a, Returns a ta -> K a (k a)).

(* Alternate, logically equivalent version of bind.
   It should not matter which one we use. Since bind_PropT has fewer cases, we should
   stick to it.*)
  Definition bind_PropT' {E} :=
    fun A B (PA: PropT E A) (K: A -> PropT E B) (tb: itree E B) =>
      exists (ta: itree E A),  PA ta /\
                          ((exists (k: A -> itree E B),
                               (forall a, Returns a ta -> K a (k a))
                               /\ tb ≈ bind ta k)
                           \/ (forall k, (forall a, K a (k a)) /\ tb ≈ bind ta k)).

  Lemma bind_PropT_bind_PropT' {E}:
    forall A B PA K (tb : itree E B), bind_PropT A B PA K tb <-> bind_PropT' A B PA K tb.
  Proof.
    intros. split.
    intros.
    - red. red in H.
      destruct H as (ta & ka & HPA & eq & HR).
      exists ta. split; auto.
      left.  exists ka. split; auto.
    - intros.
      red. red in H.
      destruct H as  (ta & EQ1 & [(k & KA & EQ2) | HX]).
      + exists ta. exists k. auto.
      + exists ta. exists (fun _ => ITree.spin).
        split; auto.
        specialize (HX (fun _ => ITree.spin)).
        destruct HX as (HA & H).
        split; auto.
  Qed.

#[global] Instance Monad_Prop {E} : Monad (PropT E) :=
  {|
    ret := fun _ x y => y ≈ ret x
  ; bind := bind_PropT
  |}.
