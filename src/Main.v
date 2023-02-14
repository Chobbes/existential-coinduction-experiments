From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom
     Nondeterminism.

Require Import Paco.paco.

From ExistentialCoinduction Require Import
                            PropT.

Variant NatEvent : Type -> Type :=
  | nat_ev : nat -> NatEvent nat.

Variant BoolEvent : Type -> Type :=
  | bool_ev : bool -> BoolEvent bool.

Definition nb (n : nat) (b : bool) : Prop :=
  (n = 1%nat /\ b = true) \/ (n = 0%nat /\ b = false).

Definition NatE := nondetE +' NatEvent.
Definition BoolE := nondetE +' BoolEvent.

Definition event_rel (ne : NatEvent nat) (be : BoolEvent bool) : Prop
  := match ne, be with
     | nat_ev n, bool_ev b => nb n b
     end.

Definition event_rel_ans (ne : NatEvent nat) (n_ans : nat) (be : BoolEvent bool) (b_ans : bool) : Prop
  := match ne, be with
     | nat_ev n, bool_ev b => nb n b /\ nb n_ans b_ans
     end.

Definition nondetE_handle {E} X (e : (nondetE +' E) X) : PropT E X
  := match e with
     | inl1 e' =>
         match e' with
         | Or =>
             fun (t : itree E bool) => t = Ret true \/ t = Ret false
         end
     | inr1 e' => fun t => t ≈ @ITree.trigger E X e'
     end.

Definition runInf {X} (t : itree InfE X) : PropT (IEvent +' OOME) X
  := interp_prop nondetE_handle eq t (OOM:=OOME).

Definition runFin {X} (t : itree FinE X) : PropT (FEvent +' OOME) X
  := interp_prop nondetE_handle eq t (OOM:=OOME).
