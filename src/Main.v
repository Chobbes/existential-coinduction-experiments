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

From ExtLib Require Import
     Structures.Monads.

From ExistentialCoinduction Require Import
  PropT
  InterpProp.

Import MonadNotation.
Open Scope monad.

(** * My events *)
Variant NatEvent : Type -> Type :=
  | nat_ev : nat -> NatEvent nat.

Variant BoolEvent : Type -> Type :=
  | bool_ev : bool -> BoolEvent bool.

Definition NatE := nondetE +' NatEvent.
Definition BoolE := nondetE +' BoolEvent.

(** * Handlers *)
Definition nondetE_handle {E} X (e : (nondetE +' E) X) : PropT E X
  := match e with
     | inl1 e' =>
         match e' with
         | Or =>
             fun (t : itree E bool) => t = Ret true \/ t = Ret false
         end
     | inr1 e' => fun t => t ≈ @ITree.trigger E X e'
     end.

(** * Interpreters *)
Definition runNat {X} (t : itree NatE X) : PropT NatEvent X
  := interp_prop nondetE_handle eq t.

Definition runBool {X} (t : itree BoolE X) : PropT BoolEvent X
  := interp_prop nondetE_handle eq t.

(** * Event relations for rutt *)

(** Relation between nat values and bool values *)
Definition nb (n : nat) (b : bool) : Prop :=
  (n = 1%nat /\ b = true) \/ (n = 0%nat /\ b = false).

(** Base event relations between NatEvent and BoolEvent *)

Definition event_rel (ne : NatEvent nat) (be : BoolEvent bool) : Prop
  := match ne, be with
     | nat_ev n, bool_ev b => nb n b
     end.

Definition event_rel_ans (ne : NatEvent nat) (n_ans : nat) (be : BoolEvent bool) (b_ans : bool) : Prop
  := match ne, be with
     | nat_ev n, bool_ev b => nb n b /\ nb n_ans b_ans
     end.

(** Top level event relations *)

Definition top_level_rel {X Y} (i : NatE X) (f : BoolE Y) : Prop.
  refine (match i, f with
          | inl1 i, inl1 f =>
              match i, f with
              | Or, Or =>
                  True
              end
          | inr1 (nat_ev n), inr1 (bool_ev b) => nb n b
          | _, _ => False
          end).
Defined.

Definition top_level_rel_ans {X Y} (i : NatE X) (x : X) (f : BoolE Y) (y : Y) : Prop.
  refine (match i, f with
          | inl1 i, inl1 f =>
              match i, f with
              | Or, Or =>
                  _
              end
          | inr1 (nat_ev n), inr1 (bool_ev b) => _
          | _, _ => False
          end).

  - inversion i. inversion f.
    subst.
    exact (x = y).
  - inversion n0. inversion b0.
    subst.
    exact (nb n b /\ nb H H1).
Defined.

Definition event_rel' {X Y} (ne : NatEvent X) (be : BoolEvent Y) : Prop
  := match ne, be with
     | nat_ev n, bool_ev b => nb n b
     end.

Definition event_rel_ans' {X Y} (ne : NatEvent X) (n_ans : X) (be : BoolEvent Y) (b_ans : Y) : Prop.
  refine match ne, be with
         | nat_ev n, bool_ev b => _
         end.

  inversion ne. inversion be.
  subst.
  exact (nb n b /\ nb n_ans b_ans).
Defined.

(** * Inversion lemmas / axioms *)

Require Import Coq.Logic.ClassicalEpsilon.
Require Import ChoiceFacts.

Lemma or_Type_inv : forall (P : Prop) (Q : Prop), (P \/ Q) -> (P + Q)%type.
Proof.
  intros P Q H.
  pose proof excluded_middle_informative P.
  pose proof excluded_middle_informative Q.
  destruct H0.
  apply (inl p).
  destruct H1.
  apply (inr q).

  exfalso.
  destruct H; auto.
Qed.

Axiom rutt_inv_Type :
  forall {E1 E2 : Type -> Type}
    (R1 R2 : Type) (PRE : prerel E1 E2) (POST : postrel E1 E2) (RR : R1 -> R2 -> Prop) (t1 : itree E1 R1) (t2 : itree E2 R2),
    @rutt E1 E2 R1 R2 PRE POST RR t1 t2 ->
    ((rutt_ PRE POST RR
        (upaco2
           (rutt_ PRE POST RR) bot2) t1 t2) *

       ( (* Returns on both sides *)
         ({r1 & {r2 &
                   RR r1 r2 *
                     (RetF r1 = observe t1) *
                     (RetF r2 = observe t2)}}) +
           (* Double Tau *)
           ({m1 & {m2 &
                     (paco2 (rutt_ PRE POST RR) bot2 m1 m2) *
                       (TauF m1 = observe t1) *
                       (TauF m2 = observe t2)}}) +
           (* Vis Nodes *)
           ({A & {B & {e1 & {e2 & {k1 & {k2 &
                                           (PRE A B e1 e2) *
                                             (forall (a : A) (b : B),
                                                 POST A B e1 a e2 b ->
                                                 upaco2
                                                   (rutt_ PRE POST RR) bot2 (k1 a) (k2 b)) *
                                             (VisF e1 k1 = observe t1) *
                                             (VisF e2 k2 = observe t2)}}}}}}) +

           (* Tau Left *)
           ({t1' & {ot2 &
                      (ruttF PRE POST RR
                         (upaco2
                            (rutt_ PRE POST RR) bot2)
                         (observe t1') (observe t2)) *
                        (TauF t1' = observe t1) *
                        (ot2 = observe t2)}}) +

           (* Tau Right *)
           ({ot1 & {t2' &
                      (ruttF PRE POST RR
                         (upaco2
                            (rutt_ PRE POST RR) bot2)
                         (observe t1) (observe t2')) *
                        (ot1 = observe t1) *
                        (TauF t2' = observe t2)}})
             
    ))%type.

Axiom interp_PropTF_vis_l_inv_Type :
  forall {E F : Type -> Type}
    X
    (h : forall T : Type, E T -> PropT F T)
    (R1 R2 : Type)
    (RR : R1 -> R2 -> Prop)
    (b1 b2 : bool)
    (sim : itree E R1 -> itree F R2 -> Prop)
    (e : E X) k t',
    interp_PropTF h RR b1 b2 sim (VisF e k) (observe t') ->
    ({k2 & {ta &
              (forall (a : X), Returns a ta -> upaco2 (interp_PropT_ h RR b1 b2) bot2 (k a) (k2 a)) *
                (h X e ta) *
                (t' ≈ x <- ta;; k2 x)}})%type.

Axiom interp_prop_inv_Type :
  forall {E F : Type -> Type} (h_spec : forall T : Type, E T -> PropT F T) (R1 R2 : Type) (RR : R1 -> R2 -> Prop) (t1 : itree E R1) (t2 : itree F R2),
    @interp_prop E F h_spec R1 R2 RR t1 t2 ->
    ((interp_PropT_ h_spec RR true
        true
        (upaco2
           (interp_PropT_ h_spec RR
              true true) bot2) t1 t2) *

       ( (* Returns on both sides *)
         ({r1 & {r2 & RR r1 r2 * (RetF r1 = observe t1) * (RetF r2 = observe t2)}}) +
           (* Double tau *)
           ({t1' & {t2' & (paco2 (interp_PropT_ h_spec RR true true) bot2 t1' t2') * (TauF t1' = observe t1) * (TauF t2' = observe t2)}}) +
           (* Tau left *)
           ({t1' & {t2' &
                      (interp_PropTF h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true) bot2) (observe t1') (observe t2)) *
                        (TauF t1' = observe t1) * (t2' = observe t2)}}) +
           (* Tau right *)
           ({t1' & {t2' &
                      (interp_PropTF h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true) bot2) (observe t1) (observe t2')) *
                        (t1' = observe t1) * (TauF t2' = observe t2)}}) +

           (* Vis nodes *)
           ({A & {e & {k1 & {k2 & {ta & {t2' &
                                           (forall (a : A), Returns a ta -> upaco2 (interp_PropT_ h_spec RR true true) bot2 (k1 a) (k2 a)) *
                                             (h_spec A e ta) *
                                             (t2' ≈ x <- ta;; k2 x) *
                                             (VisF e k1 = observe t1) *
                                             (observe t2' = observe t2)}}}}}})
       )
    )%type.

(** * Tactics *)

Ltac inj_pair2_existT :=
  repeat
      match goal with
      | H : _ |- _ => apply inj_pair2 in H
      end.

Ltac subst_existT :=
  inj_pair2_existT; subst.

Ltac forward H :=
  let H' := fresh in
  match type of H with
  | ?P -> _ => assert P as H'; [| specialize (H H'); clear H']
  end.

Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.


(** * Constructing a nat tree from a bool tree *)

Lemma get_nat_tree :
  forall t_nat t_bool,
    rutt (@top_level_rel) (@top_level_rel_ans) nb t_nat t_bool ->
    forall t_bool2, runBool t_bool t_bool2 ->
           itree NatEvent nat.
Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  revert RUN.
  revert REL.
  revert t_nat t_bool t_bool2.
  cofix CIH.
  intros t_nat t_bool t_bool2 REL RUN.
  apply rutt_inv_Type in REL as (REL' & REL).
  destruct REL as [[[[RET | TAU] | VIS] | TauL] | TauR].
  - (* Ret *)
    destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
    apply (ret r1).
  - (* Double Tau *)
    destruct TAU as (m1 & m2 & (HS & TAU1) & TAU2).
    apply go.
    apply TauF.
    eapply CIH with (t_bool:=m2) (t_bool2:=t_bool2).
    apply HS.
    red; red in RUN.
    setoid_rewrite <- (tau_eutt m2).
    pstep. rewrite TAU2.
    red.
    cbn.
    punfold RUN.
  - (* Vis *)
    destruct VIS as (A & B & e1 & e2 & k1 & k2 & (HS & VIS1) & VIS2).
    destruct HS as (e1e2 & ANS).
    destruct e1, e2; cbn in e1e2; try inversion e1e2; subst;
      try destruct n, n0; try contradiction.
    + (* nondetE *)
      cbn in *.
      (* Need to know the choice made here for t_bool2 *)
      red in RUN.
      apply interp_prop_inv_Type in RUN as (RUN' & RUN).
      destruct RUN as [[[[RETP | TAUP] | TAULP] | TAURP] | VISP].
      { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
          setoid_rewrite <- VIS2 in RET1; inversion RET1.
      }
      { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
        setoid_rewrite <- VIS2 in TAU1; inversion TAU1.
      }
      { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
        setoid_rewrite <- VIS2 in TAU1; inversion TAU1.
      }
      { (* Tau on right... *)
        destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
        apply go.
        apply TauF.
        eapply CIH.
        red; eauto.
        pstep; eauto.
      }
      { (* Vis events *)
        destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & T_BOOL) &T_BOOL2)).
        (* t_bool2 was a vis node... *)
        setoid_rewrite <- VIS2 in T_BOOL.
        inversion T_BOOL; subst.
        subst_existT.
        red in HANDLE.
        apply or_Type_inv in HANDLE.
        destruct HANDLE; subst.
        - setoid_rewrite bind_ret_l in SPEC.
          apply go.
          apply TauF.

          specialize (ANS true true eq_refl).
          specialize (HS true).
          forward HS.
          constructor; reflexivity.
          pclearbot.

          eapply CIH with (t_bool2:=k2' true); eauto.
        - setoid_rewrite bind_ret_l in SPEC.
          apply go.
          apply TauF.

          specialize (ANS false false eq_refl).
          specialize (HS false).
          forward HS.
          constructor; reflexivity.
          pclearbot.

          eapply CIH with (t_bool2:=k2' false); eauto.
      }
    + (* Uninterpreted events *)
      destruct n, b; cbn in *.
      cbn in *.
      specialize (ANS n b).
      forward ANS; auto.
      pclearbot.

      (* Need to know stuff about continuations... *)
      red in RUN.
      apply interp_prop_inv_Type in RUN as (RUN' & RUN).
      destruct RUN as [[[[RETP | TAUP] | TAULP] | TAURP] | VISP].
      { destruct RETP as (r1 & r2 & (RRr1r2 & RET1) & RET2);
          setoid_rewrite <- VIS2 in RET1; inversion RET1.
      }
      { destruct TAUP as (m1 & m2 & (HS & TAU1) & TAU2).
        setoid_rewrite <- VIS2 in TAU1; inversion TAU1.
      }
      { destruct TAULP as (m1 & m2 & (HS & TAU1) & TAU2).
        setoid_rewrite <- VIS2 in TAU1; inversion TAU1.
      }
      { (* Tau on right... *)
        destruct TAURP as (m1 & m2 & (HS & TAU1) & TAU2).
        setoid_rewrite <- VIS2 in HS.

        apply interp_PropTF_vis_l_inv_Type in HS.
        destruct HS as (k2' & ta & (K & HANDLE) & EQ).
        red in HANDLE.
        rewrite HANDLE in EQ.
        cbn in EQ.
        rewrite bind_trigger in EQ.
        subst.
        
        (* t_bool2 has an extra tau *)
        apply go.
        apply TauF.
        eapply CIH with (t_bool2:=k2' b).
        apply ANS.
        red; eauto.
        pstep; eauto.

        specialize (K b).
        forward K.
        { setoid_rewrite HANDLE.
          unfold ITree.trigger.
          eapply ReturnsVis with (x:=b).
          reflexivity.
          cbn.
          constructor; reflexivity.
        }

        pclearbot.
        punfold K.
      }
      { (* Vis events *)
        destruct VISP as (A & e & k1' & k2' & ta & t2' & ((((HS & HANDLE) & SPEC) & T_BOOL) &T_BOOL2)).
        (* t_bool2 was a vis node... *)
        setoid_rewrite <- VIS2 in T_BOOL.
        inversion T_BOOL; subst.
        subst_existT.
        red in HANDLE.

        specialize (HS b).
        forward HS.
        { setoid_rewrite HANDLE.
          unfold ITree.trigger.
          eapply ReturnsVis with (x:=b).
          reflexivity.
          cbn.
          constructor; reflexivity.
        }

        pclearbot.

        apply go.
        apply TauF.
        eapply CIH with (t_bool2 := k2' b).
        apply ANS.
        apply HS.
      }
  - (* TauL *)
    destruct TauL as (t1' & ot2 & ((HS & T_NAT) & T_BOOL)).
    apply go.
    apply TauF.
    eapply CIH; eauto.
    pstep. red.
    eauto.
  - (* TauR *)
    destruct TauR as (ot1 & t2' & ((HS & T_NAT) & T_BOOL)).
    apply go.
    apply TauF.
    eapply CIH; eauto.
    pstep. red.
    eauto.
Defined.

(** * Main Theorem *)

Require Import Coq.Program.Equality.

Ltac pdepdes H := punfold H; dependent destruction H; pclearbot.

Lemma main :
  forall t_nat t_bool,
    rutt (@top_level_rel) (@top_level_rel_ans) nb t_nat t_bool ->
    forall t_bool2, runBool t_bool t_bool2 ->
           exists t_nat2,
             runNat t_nat t_nat2 /\
               rutt (@event_rel') (@event_rel_ans') nb t_nat2 t_bool2.
Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree t_nat t_bool REL t_bool2 RUN).
  split.
  { revert RUN.
    revert REL.
    revert t_nat t_bool t_bool2.
    pcofix CIH.
    intros t_nat t_bool t_bool2 REL RUN.
    (* Cannot seem to do anything with REL / RUN because they're used in the goal? *)
    Fail pdepdes REL.
    Fail punfold REL.
    Fail pinversion REL.
    Fail dependent destruction REL.
    Fail dependent inversion REL.
    Fail dependent induction REL.

    (* If the goal changes I can do stuff with REL... *)
    exfalso.
    pinversion REL.
Abort.
