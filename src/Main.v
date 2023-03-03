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

Inductive detE X : Type -> Type :=
| DetE : X -> detE X unit.

Definition nondetE_handle_det {E} X (e : (nondetE +' E) X) : PropT (detE bool +' E) X
  := match e with
     | inl1 e' =>
         match e' with
         | Or =>
             fun (t : itree (detE bool +' E) bool) => t = vis (inl1 (DetE bool true)) (fun _ => Ret true) \/ t = vis (inl1 (DetE bool false)) (fun _ => Ret false)
         end
     | inr1 e' => fun t => t ≈ @ITree.trigger (detE bool +' E) X (inr1 e')
     end.

(** * Interpreters *)
Definition runNat {X} (t : itree NatE X) : PropT NatEvent X
  := interp_prop nondetE_handle eq t.

Definition runNatDet {X} (t : itree NatE X) : PropT (detE bool +' NatEvent) X
  := interp_prop nondetE_handle_det eq t.

Definition runBool {X} (t : itree BoolE X) : PropT BoolEvent X
  := interp_prop nondetE_handle eq t.

Definition runBoolDet {X} (t : itree BoolE X) : PropT (detE bool +' BoolEvent) X
  := interp_prop nondetE_handle_det eq t.

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

Lemma get_nat_tree' :
  forall (t_bool2 : itree BoolEvent bool), itree NatEvent nat.
Proof.
  cofix CIH.
  intros t_bool2.
  inversion t_bool2.
  inversion _observe.
  - (* Ret *)
    apply (ret (if r then 1 else 0)).
  - (* Tau *)
    apply go.
    apply TauF.
    apply CIH.
    apply t.
  - (* Vis *)
    inversion e; subst.
    rename H into r.
    apply go.
    apply (VisF (nat_ev (if r then 1 else 0))).
    intros n. (* Result *)
    apply CIH.
    apply (if Nat.eqb n 0 then k false else if Nat.eqb n 1 then k true else k false).
Defined.

Import Morphisms.

(* Lemma get_nat_tree'_unfold : *)
(*   forall (t : itree BoolEvent bool), *)
(*     get_nat_tree' t = *)
(*       (fun _observe : itree' BoolEvent bool => *)
(*          (fun _observe0 : itree' BoolEvent bool => *)
(*             let X := *)
(*               match _observe0 with *)
(*               | RetF r => (fun r0 : bool => (fun r1 : bool => ret (if r1 then 1 else 0)) r0) r *)
(*               | TauF t => *)
(*                   (fun t0 : itree BoolEvent bool => (fun t1 : itree BoolEvent bool => Tau (get_nat_tree' t1)) t0) t *)
(*               | @VisF _ _ _ X e k => *)
(*                   (fun (X0 : Type) (e0 : BoolEvent X0) (k0 : X0 -> itree BoolEvent bool) => *)
(*                      (fun (e1 : BoolEvent X0) (k1 : X0 -> itree BoolEvent bool) => *)
(*                         let X1 := *)
(*                           match e1 in (BoolEvent T) return (T = X0 -> itree NatEvent nat) with *)
(*                           | bool_ev x => *)
(*                               (fun (H : bool) (H0 : bool = X0) => *)
(*                                  (fun H1 : bool = X0 => *)
(*                                     let H2 : bool = X0 := H1 in *)
(*                                     eq_rect bool (fun _ : Type => bool -> itree NatEvent nat) *)
(*                                       (fun H3 : bool => *)
(*                                          eq_rect bool *)
(*                                            (fun X1 : Type => *)
(*                                               BoolEvent X1 -> (X1 -> itree BoolEvent bool) -> itree NatEvent nat) *)
(*                                            (fun (_ : BoolEvent bool) (k2 : bool -> itree BoolEvent bool) => *)
(*                                               Vis (nat_ev (if H3 then 1 else 0)) *)
(*                                                 (fun n : nat => *)
(*                                                    get_nat_tree' *)
(*                                                      (if Nat.eqb n 0 *)
(*                                                       then k2 false *)
(*                                                       else if Nat.eqb n 1 then k2 true else ITree.spin))) X0 H1 e1 k1) X0 *)
(*                                       H2) H0 H) x *)
(*                           end in *)
(*                             X1 eq_refl) e0 k0) X e k *)
(*               end in *)
(*             X) _observe) (_observe t). *)

(* #[global] Instance get_nat_tree'_Proper_eq_itree : *)
(*   Proper (eq_itree eq ==> eq_itree eq) get_nat_tree'. *)
(* Proof. *)
(*   unfold Proper, respectful. *)

(*   intros x y. *)
(*   rewrite (itree_eta_ x). *)
(*   rewrite (itree_eta_ y). *)

(*   genobs x ox. *)
(*   genobs y oy. *)

(*   clear x y Heqox Heqoy. *)

(*   revert ox oy. *)
(*   pcofix CIH. *)

(*   intros ox oy EQ. *)

(*   pinversion EQ; subst. *)
(*   - cbn in *. *)
(*     rewrite <- H, <- H0. *)
(*     pstep. red. cbn. *)
(*     constructor. *)
(*     reflexivity. *)
(*   - cbn in *. *)
(*     rewrite <- H, <- H0. *)
(*     pstep. red. cbn. *)
(*     constructor. *)
(*     rewrite (itree_eta_ m1). *)
(*     rewrite (itree_eta_ m2). *)
(*     right. *)
(*     eapply CIH. *)
(*     punfold REL. *)
(*     pstep. red. cbn. *)
(*     red in REL. *)
(*     eauto. *)
(*   - cbn in *. *)
(*     rewrite <- H, <- H0. *)
(*     inversion e; subst. *)
(*     pstep. red. cbn. *)
(*     (* Why isn't this reducing??? *) *)
(*     admit. *)
(* Defined. *)

#[global] Instance get_nat_tree'_Proper :
  Proper (eutt eq ==> eutt eq) get_nat_tree'.
Proof.
  unfold Proper, respectful.
  intros x y EQ.
  rewrite (itree_eta x) in EQ.
  ginit. gcofix CIH.

  pinversion EQ; subst.
  - gstep. red.
Admitted.

(** * Main Theorem *)

Require Import Coq.Program.Equality.

Ltac pdepdes H := punfold H; dependent destruction H; pclearbot.

Lemma main' :
  forall t_nat t_bool,
    rutt (@top_level_rel) (@top_level_rel_ans) nb t_nat t_bool ->
    forall t_bool2, runBool t_bool t_bool2 ->
           exists t_nat2,
             runNat t_nat t_nat2 /\
               rutt (@event_rel') (@event_rel_ans') nb t_nat2 t_bool2.
Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree' t_bool2).
  split.
  { revert RUN.
    revert REL.

    setoid_rewrite (itree_eta_ t_nat).
    setoid_rewrite (itree_eta_ t_bool).
    setoid_rewrite (itree_eta_ t_bool2).

    genobs t_nat ot_nat.
    genobs t_bool ot_bool.
    genobs t_bool2 ot_bool2.
    clear t_nat Heqot_nat.
    clear t_bool Heqot_bool.
    clear t_bool2 Heqot_bool2.

    revert ot_nat ot_bool ot_bool2.
    pcofix CIH.
    intros ot_nat ot_bool ot_bool2 REL RUN.

    punfold REL.
    red in REL.
    cbn in REL.

    remember (upaco2 (rutt_ (@top_level_rel) (@top_level_rel_ans) nb) bot2) as r'.
    revert Heqr'.

    dependent induction REL; intros Heqr'.
    - subst.
      apply interp_prop_ret_inv in RUN.
      destruct RUN as [r3 [REQ EQ]]; subst.

      (assert (get_nat_tree' {| _observe := ot_bool2 |} ≈ (get_nat_tree' (ret r3)))).
      { rewrite <- EQ.
        reflexivity.
      }

      eapply paco2_mon_bot; eauto.
      rewrite H0.

      pstep; red; cbn.
      constructor.
      destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
    - punfold RUN.
      red in RUN.
      cbn in RUN.
      remember (TauF m2) as M2.
      revert m1 m2 H HeqM2.
      induction RUN; intros m1 m2 H' HeqM2; try discriminate.
      + pstep. red. cbn.
        constructor; auto.
        right.

        specialize (CIH (observe m1) (observe m2) (observe t2)).
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ t2).

        eapply CIH.

        subst r'.
        pclearbot.
        repeat rewrite <- itree_eta_.
        apply H'.

        pclearbot.
        repeat rewrite <- itree_eta_.

        inversion HeqM2; subst.
        apply HS.
      + (* Need to apply IHRUN *)
        inversion HeqM2; subst.
        clear HeqM2.

        pclearbot.
        setoid_rewrite (itree_eta_ m2) in H'.
        desobs m2 Hm2; setoid_rewrite Hm2 in RUN; setoid_rewrite Hm2 in IHRUN.
        { (* Ret *)
          clear IHRUN.

          pose proof H' as H''.
          eapply rutt_inv_Ret_r in H'.
          destruct H' as [r1 [H' NB]].

          inversion RUN.
          - subst.

            eapply paco2_mon_bot; eauto.
            rewrite H'.

            pstep; red; cbn.
            constructor; auto.
            cbn.

            constructor.
            destruct NB as [[R1 R3] | [R1 R3]]; subst; auto.
          - pstep; red; cbn.
            constructor; auto.
            right.

            specialize (CIH (observe m1) (observe m2) (observe t0)).
            rewrite (itree_eta_ m1).
            rewrite (itree_eta_ t0).

            eapply CIH; eauto.
            rewrite Hm2.
            rewrite H'.
            cbn.
            pstep; red; cbn.
            constructor; auto.

            rewrite Hm2.
            pstep; red; cbn.
            auto.
        }

        { (* Tau *)
          apply rutt_inv_Tau_r in H'.
          eapply IHRUN.
          left. eapply H'.
          reflexivity.
        }

        { (* Vis *)
          clear IHRUN Hm2.

          apply rutt_inv_Vis_r in H'.
          destruct H' as [U1 [e1 [k1 [VIS [EV_REL K_RUTT]]]]].

          (* I need to show that Tau m1 somehow relates to get_nat_tree' t2...

             One possibility is to go through RUN... That should give
             me that t2 is either a Tau, in which case we can use the
             CIH... Or that t2 is a Vis node.

             *Actually*, the second case is not where t2 is a Vis node.
             It's the vis case of interp_prop...

               | Interp_PropT_Vis : forall (A : Type) (e : E A) (k1 : A -> itree E R1) 
                         (k2 : A -> itree F R2) (ta : itree F A) (t2 : itree F R2),
                       (forall a : A, Returns a ta -> sim (k1 a) (k2 a)) ->
                       h_spec A e ta ->
                       t2 ≈ x <- ta;; k2 x ->
                       interp_PropTF h_spec RR b1 b2 sim (VisF e k1) (observe t2).

             So all I know is that t2 is eutt a bind with ta... Where
             ta is the implementation of the event. In the case of nondeterminism
             events this means that ta = Ret true \/ ta = Ret false, so I know that
             t2 ≈ k2 true \/ t2 ≈ k2 false

             I must be able to use HK to show anything, then...
           *)

          dependent induction RUN.
          - (* t2 is a Tau *)
            subst.
            pstep; red; cbn.
            constructor.
            right.

            rewrite (itree_eta_ m1).
            rewrite (itree_eta_ t2).

            eapply CIH.
            rewrite VIS.
            cbn.

            2: {
              pstep; red; cbn.
              eauto.
            }

            pstep; red; cbn.
            constructor; eauto.

            intros a b H2.
            left.
            eapply K_RUTT; eauto.
          - (* t2 is a Vis *)
            rename H into HANDLER.
            rename H0 into VIS_HANDLED.

            red in HANDLER.
            destruct e, e1; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.
            { (* NonDet event *)
              destruct HANDLER; subst; setoid_rewrite bind_ret_l in VIS_HANDLED.
              - (* True *)
                specialize (HK true).
                forward HK. constructor; reflexivity.
                pclearbot.
                rewrite <- VIS_HANDLED in HK.

                (* eapply paco2_mon_bot; eauto. *)
                (* rewrite VIS. *)

                (* pstep; red; cbn. *)
                (* constructor; auto. *)

                (* eapply Interp_PropT_Vis with (k2:=(fun b => (get_nat_tree' {| _observe := observe (k2 b) |}))). *)
                (* 2: { *)
                (*   red. left; reflexivity. *)
                (* } *)

                (* 2: { *)
                (*   setoid_rewrite bind_ret_l. *)
                (*   rewrite VIS_HANDLED. *)
                (*   reflexivity. *)
                (* } *)

                (* intros a H. *)
                (* left. *)

                rewrite (itree_eta_ t2) in HK.
                rewrite (itree_eta_ t2) in VIS_HANDLED.
                genobs t2 ot2.
                clear Heqot2 t2.

                punfold VIS. red in VIS. cbn in VIS.
                rewrite (itree_eta_ m1).
                genobs m1 om1.
                clear Heqom1 m1.

                punfold HK. red in HK. cbn in HK.

                dependent induction VIS.
                { red in REL.
                  pclearbot.

                  dependent induction HK.
                  - Opaque get_nat_tree'.
                    pstep; red; cbn.
                    constructor; auto.
                    cbn.

                    eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' (Ret r2)).
                    2: {
                      red. left; reflexivity.
                    }
                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                    right.

                    rewrite (itree_eta_ (k3 true)).
                    rewrite (itree_eta_ (Ret _)).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.

                      specialize (K_RUTT true true).
                      forward K_RUTT; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                      setoid_rewrite <- x in K_RUTT.

                      setoid_rewrite EQ.
                      pstep; red; cbn.
                      eauto.
                    + cbn.
                      pstep; red; cbn.
                      constructor; auto.
                  - pstep; red; cbn.
                    Transparent get_nat_tree'.
                    cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        left; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      rewrite <- x.
                      constructor; auto.
                      pclearbot.
                      punfold HS.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := t2 |}).
                    2: {
                      red.
                      left; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 true)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT true true).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.
                      constructor; auto.
                  - pstep; red; cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        left; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      auto.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := observe t2 |}).
                    2: {
                      red.
                      left; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 true)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT true true).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.

                      destruct e.
                      { destruct n.
                        red in H.
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK true).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            left; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            right; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                      }

                      { red in H.

                        eapply Interp_PropT_Vis with (k2:=fun x => k4 x).
                        2: {
                          red.
                          eauto.
                        }

                        2: {
                          eauto.
                        }

                        intros a H1.
                        apply HK in H1.
                        eauto.
                      }
                }

                { (* Tau... *)
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  specialize (IHVIS k1 eq_refl I).
                  forward IHVIS; auto.
                  pstep; red; cbn.
                  constructor; auto.
                  punfold IHVIS; red in IHVIS; cbn in IHVIS.
                  setoid_rewrite <- itree_eta_ in IHVIS.
                  cbn in *.
                  auto.
                }

              - (* False *)
                specialize (HK false).
                forward HK. constructor; reflexivity.
                pclearbot.
                rewrite <- VIS_HANDLED in HK.

                (* eapply paco2_mon_bot; eauto. *)
                (* rewrite VIS. *)

                (* pstep; red; cbn. *)
                (* constructor; auto. *)

                (* eapply Interp_PropT_Vis with (k2:=(fun b => (get_nat_tree' {| _observe := observe (k2 b) |}))). *)
                (* 2: { *)
                (*   red. left; reflexivity. *)
                (* } *)

                (* 2: { *)
                (*   setoid_rewrite bind_ret_l. *)
                (*   rewrite VIS_HANDLED. *)
                (*   reflexivity. *)
                (* } *)

                (* intros a H. *)
                (* left. *)

                rewrite (itree_eta_ t2) in HK.
                rewrite (itree_eta_ t2) in VIS_HANDLED.
                genobs t2 ot2.
                clear Heqot2 t2.

                punfold VIS. red in VIS. cbn in VIS.
                rewrite (itree_eta_ m1).
                genobs m1 om1.
                clear Heqom1 m1.

                punfold HK. red in HK. cbn in HK.

                dependent induction VIS.
                { red in REL.
                  pclearbot.

                  dependent induction HK.
                  - Opaque get_nat_tree'.
                    pstep; red; cbn.
                    constructor; auto.
                    cbn.

                    eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' (Ret r2)).
                    2: {
                      red. right; reflexivity.
                    }
                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                    right.

                    rewrite (itree_eta_ (k3 false)).
                    rewrite (itree_eta_ (Ret _)).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                      setoid_rewrite <- x in K_RUTT.

                      setoid_rewrite EQ.
                      pstep; red; cbn.
                      eauto.
                    + cbn.
                      pstep; red; cbn.
                      constructor; auto.
                  - pstep; red; cbn.
                    Transparent get_nat_tree'.
                    cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        right; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      rewrite <- x.
                      constructor; auto.
                      pclearbot.
                      punfold HS.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := t2 |}).
                    2: {
                      red.
                      right; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 false)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.
                      constructor; auto.
                  - pstep; red; cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        right; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      auto.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := observe t2 |}).
                    2: {
                      red.
                      right; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 false)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.

                      destruct e.
                      { destruct n.
                        red in H.
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK true).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            left; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            right; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                      }

                      { red in H.

                        eapply Interp_PropT_Vis with (k2:=fun x => k4 x).
                        2: {
                          red.
                          eauto.
                        }

                        2: {
                          eauto.
                        }

                        intros a H1.
                        apply HK in H1.
                        eauto.
                      }
                }

                { (* Tau... *)
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  specialize (IHVIS k1 eq_refl I).
                  forward IHVIS; auto.
                  pstep; red; cbn.
                  constructor; auto.
                  punfold IHVIS; red in IHVIS; cbn in IHVIS.
                  setoid_rewrite <- itree_eta_ in IHVIS.
                  cbn in *.
                  auto.
                }
            }

            { (* Regular events *)
              destruct b.

              rewrite HANDLER in VIS_HANDLED.
              punfold VIS_HANDLED.
              red in VIS_HANDLED.

              punfold VIS. red in VIS.
              dependent induction VIS.
              - rewrite (itree_eta_ m1).
                rewrite <- x.

                dependent induction VIS_HANDLED; subst_existT.
                + rewrite <- x0.
                  pstep; red; cbn.
                  constructor; auto.
                  cbn.

                  assert
                    (VisF (nat_ev (if b then 1 else 0))
                       (fun n0 : nat =>
                          get_nat_tree'
                            (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)) =
                       observe (Vis (nat_ev (if b then 1 else 0))
                         (fun n0 : nat =>
                            get_nat_tree'
                              (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)))) as EQVIS by reflexivity.
                  rewrite EQVIS.

                  eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                       get_nat_tree' (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false))).
                  2: {
                    red.
                    reflexivity.
                  }
                  2: {
                    setoid_rewrite bind_trigger.
                    destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto;
                      reflexivity.
                  }

                  intros a RET.
                  right.

                  clear EQVIS.

                  rewrite (itree_eta_ (k3 a)).
                  rewrite (itree_eta_ (if Nat.eqb a 0 then k0 false else if Nat.eqb a 1 then k0 true else k0 false)).

                  specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                  forward K_RUTT; cbn; auto.

                  eapply CIH.
                  { specialize (REL a).
                    red in REL. pclearbot.
                    assert (k3 a ≈ k1 a) as EQ by auto.
                    rewrite EQ.

                    punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                    pstep; red; cbn.
                    eauto. 
                  }

                  { setoid_rewrite HANDLER in HK.

                    specialize (REL0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                    red in REL0.
                    pclearbot.
                    assert (k0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false) ≈ k2 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)) as K0K2.
                    { repeat red.
                      punfold REL0.
                    }

                    destruct a; [| destruct a]; cbn in *.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK true).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - (* Bogus case *)
                      repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                  }
                + rewrite <- x.
                  Transparent get_nat_tree'.
                  pstep; red; cbn.
                  constructor.
                  right.

                  rewrite (itree_eta_ (Vis _ _)).
                  rewrite (itree_eta_ t1).
                  eapply CIH.
                  -- pstep; red; cbn.
                     apply Rutt.EqVis with (e2 := (inr1 (bool_ev b))).
                     red; auto.

                     intros a b0 H.

                     specialize (REL a).
                     red in REL. pclearbot.
                     assert (k3 a ≈ k1 a) as EQ by auto.
                     left.
                     (* Why can't I rewrite? *)
                     (* setoid_rewrite EQ. *)
                     Print Assumptions itree_eta_.
                     replace k3 with k1 by admit.

                     eapply K_RUTT; eauto.
                  -- pstep; red; cbn.
                     eapply Interp_PropT_Vis.
                     2: {
                       red. reflexivity.
                     }

                     intros a H.
                     eapply HK.
                     setoid_rewrite HANDLER.
                     auto.
                     
                     pstep; red; cbn; eauto.
              - rewrite (itree_eta_ m1).
                rewrite <- x.

                dependent induction VIS_HANDLED; subst_existT.
                + rewrite <- x0.
                  setoid_rewrite HANDLER in HK.

                  pstep; red; cbn.
                  constructor; auto.
                  cbn.

                  constructor; auto.

                  dependent induction VIS; subst_existT.
                  { rewrite <- x.
                    assert
                      (VisF (nat_ev (if b then 1 else 0))
                         (fun n0 : nat =>
                            get_nat_tree'
                              (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)) =
                         observe (Vis (nat_ev (if b then 1 else 0))
                                    (fun n0 : nat =>
                                       get_nat_tree'
                                         (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)))) as EQVIS by reflexivity.
                    rewrite EQVIS.

                    eapply Interp_PropT_Vis with (k2:=(fun n0 : nat => 
                                                         get_nat_tree' (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false))).

                    2: {
                      red.
                      reflexivity.
                    }
                    2: {
                      setoid_rewrite bind_trigger.
                      cbn.
                      destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto; reflexivity.
                    }

                    intros a RET.
                    right.

                    rewrite (itree_eta_ (k4 _)).
                    rewrite (itree_eta_ (if Nat.eqb a 0 then k0 false else if Nat.eqb a 1 then k0 true else k0 false)).

                    eapply CIH.
                    - clear EQVIS.

                      specialize (REL0 a).
                      red in REL0. pclearbot.
                      assert (k4 a ≈ k1 a) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                      forward K_RUTT.
                      cbn; auto.

                      setoid_rewrite <- itree_eta_.
                      eauto.
                    - specialize (REL (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).

                      assert (k0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false) ≈ k2 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)) as K0K2.
                      { repeat red.
                        red in REL.
                        pclearbot.
                        punfold REL.
                      }

                      destruct a; [| destruct a]; cbn in *.
                      + repeat (rewrite <- itree_eta_).
                        setoid_rewrite K0K2.
                        specialize (HK false).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold ITree.trigger.
                          reflexivity.
                          constructor. reflexivity.
                        }
                        pclearbot.
                        repeat red.
                        punfold HK; red in HK.
                      + repeat (rewrite <- itree_eta_).
                        setoid_rewrite K0K2.
                        specialize (HK true).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold ITree.trigger.
                          reflexivity.
                          constructor. reflexivity.
                        }
                        pclearbot.
                        repeat red.
                        punfold HK; red in HK.
                      + (* Bogus case *)
                        repeat (rewrite <- itree_eta_).
                        specialize (HK false).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold ITree.trigger.
                          reflexivity.
                          constructor. reflexivity.
                        }
                        pclearbot.
                        setoid_rewrite K0K2.
                        eapply HK.
                  }

                  { (* t1 = Tau *)
                    eapply IHVIS; eauto.
                    constructor; auto.
                  }
                  
                  eapply Interp_PropT_Vis. with (k2:=(fun n0 : nat => 
                                                       get_nat_tree' (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false))).
                  2: {
                    red.
                    reflexivity.
                  }
                  2: {
                    setoid_rewrite bind_trigger.
                    destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto;
                      reflexivity.
                  }

                  intros a RET.
                  right.

                  clear EQVIS.

                  rewrite (itree_eta_ (k3 a)).
                  rewrite (itree_eta_ (if Nat.eqb a 0 then k0 false else if Nat.eqb a 1 then k0 true else k0 false)).

                  specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                  forward K_RUTT; cbn; auto.

                  eapply CIH.
                  { specialize (REL a).
                    red in REL. pclearbot.
                    assert (k3 a ≈ k1 a) as EQ by auto.
                    rewrite EQ.

                    punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                    pstep; red; cbn.
                    eauto. 
                  }

                  { setoid_rewrite HANDLER in HK.

                    specialize (REL0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                    red in REL0.
                    pclearbot.
                    assert (k0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false) ≈ k2 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)) as K0K2.
                    { repeat red.
                      punfold REL0.
                    }

                    destruct a; [| destruct a]; cbn in *.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK true).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - (* Bogus case *)
                      repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                  }
                + rewrite <- x.
                  Transparent get_nat_tree'.
                  pstep; red; cbn.
                  constructor.
                  right.

                  rewrite (itree_eta_ (Vis _ _)).
                  rewrite (itree_eta_ t1).
                  eapply CIH.
                  -- pstep; red; cbn.
                     apply Rutt.EqVis with (e2 := (inr1 (bool_ev b))).
                     red; auto.

                     intros a b0 H.

                     specialize (REL a).
                     red in REL. pclearbot.
                     assert (k3 a ≈ k1 a) as EQ by auto.
                     left.
                     (* Why can't I rewrite? *)
                     (* setoid_rewrite EQ. *)
                     Print Assumptions itree_eta_.
                     replace k3 with k1 by admit.

                     eapply K_RUTT; eauto.
                  -- pstep; red; cbn.
                     eapply Interp_PropT_Vis.
                     2: {
                       red. reflexivity.
                     }

                     intros a H.
                     eapply HK.
                     setoid_rewrite HANDLER.
                     auto.
                     
                     pstep; red; cbn; eauto.
                     

                     constructor. to
                     red.


                  rewrite <- x0.
                  pstep; red; cbn.
                  constructor; auto.
                  cbn.

                  assert
                    (VisF (nat_ev (if b then 1 else 0))
                       (fun n0 : nat =>
                          get_nat_tree'
                            (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)) =
                       observe (Vis (nat_ev (if b then 1 else 0))
                         (fun n0 : nat =>
                            get_nat_tree'
                              (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false)))) as EQVIS by reflexivity.
                  rewrite EQVIS.

                  eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                       get_nat_tree' (if Nat.eqb n0 0 then k0 false else if Nat.eqb n0 1 then k0 true else k0 false))).
                  2: {
                    red.
                    reflexivity.
                  }
                  2: {
                    setoid_rewrite bind_trigger.
                    destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto;
                      reflexivity.
                  }

                  intros a RET.
                  right.

                  clear EQVIS.

                  rewrite (itree_eta_ (k3 a)).
                  rewrite (itree_eta_ (if Nat.eqb a 0 then k0 false else if Nat.eqb a 1 then k0 true else k0 false)).

                  specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                  forward K_RUTT; cbn; auto.

                  eapply CIH.
                  { specialize (REL a).
                    red in REL. pclearbot.
                    assert (k3 a ≈ k1 a) as EQ by auto.
                    rewrite EQ.

                    punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                    pstep; red; cbn.
                    eauto. 
                  }

                  { setoid_rewrite HANDLER in HK.

                    specialize (REL0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                    red in REL0.
                    pclearbot.
                    assert (k0 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false) ≈ k2 (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)) as K0K2.
                    { repeat red.
                      punfold REL0.
                    }

                    destruct a; [| destruct a]; cbn in *.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - repeat (rewrite <- itree_eta_).
                      specialize (HK true).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                    - (* Bogus case *)
                      repeat (rewrite <- itree_eta_).
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }
                      pclearbot.
                      setoid_rewrite K0K2.
                      eapply HK.
                  }

                    rewrite <- K0K2.

                    specialize (REL a).
                    red in REL. pclearbot.

                    specialize (HK b).
                    forward HK.
                    { eapply ReturnsVis.
                      unfold ITree.trigger.
                      reflexivity.
                      constructor. reflexivity.
                    }

                    pclearbot.

                    (* Somehow I need to get the bool that `a` is related to... *)
                    (* I *could* just do case analysis on `a`, maybe? *)
                    (* b should be related somehow, though? *)
                    specialize (K_RUTT a b).
                    forward K_RUTT; cbn; auto.
                    punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                    pstep; red; cbn.
                    eauto. 


                    unfold top_level_rel_ans in K_RUTT.

                    destruct a.
                    - (* a=0, False *)
                      specialize (HK false).
                      forward HK.
                      { eapply ReturnsVis.
                        unfold ITree.trigger.
                        reflexivity.
                        constructor. reflexivity.
                      }

                      pclearbot.

                      

                    
                    destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                    - specialize (K_RUTT 1 true).
                      forward K_RUTT; cbn; auto.
                      split; red; auto.

                      destruct a.
                      +  

                      
                      eapply Returns_vis_inversion_ in RET.
                      2: {
                        unfold ITree.trigger.
                        reflexivity.
                      }

                      destruct RET as [a' RET].
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      
                      remember (ITree.trigger (nat_ev 1)).
                      dependent induction RET; subst.
                      + pinversion H.
                      + eapply IHRET.
                        admit.
                      + 
                      pinversion H.

                      punfold K_RUTT. red in K_RUTT.
                      dependent induction K_RUTT.
                      + rewrite <- x.
                        red.
                        red in REL0.
                        specialize (REL0 true).
                        pclearbot.
                        punfold REL0. red in REL0.
                        dependent induction REL0.
                        -- 
                      
                      red in 
                    destruct a.
                    - cbn in *. red in REL0.
                      specialize (REL0 false).
                      pclearbot.
                      specialize (HK false).
                      specialize (K_RUTT 0 false).
                      forward K_RUTT; auto.
                      
                      forward HK.
                      constructor.
                      reflexivity.

                  }
                  
                    ((VisF (nat_ev (if b then 1 else 0))
                             (fun n0 : nat =>
                                get_nat_tree'
                                  (if Nat.eqb n0 0
                                   then ITree.subst k2 (Ret false)
                                   else if Nat.eqb n0 1 then ITree.subst k2 (Ret true) else ITree.spin))) = observe (Vis (nat_ev (if b then 1 else 0))
                                                                                                                       (fun n0 : nat =>
                                                                                                                          get_nat_tree'
                                                                                                                            (if Nat.eqb n0 0
                                                                                                                             then ITree.subst k2 (Ret false)
                                                                                                                             else if Nat.eqb n0 1 then ITree.subst k2 (Ret true) else ITree.spin)))) as EQVIS by reflexivity.
                  rewrite EQVIS.

              dependent induction VIS_HANDLED; subst_existT.
              - red in REL.
                punfold VIS. red in VIS.
                dependent induction VIS.
                + cbn in *.
                  pstep; red; cbn.
                  rewrite (itree_eta_ m1).
                  setoid_rewrite <- x.


              pstep; red; cbn.
              assert ((VisF (nat_ev (if b then 1 else 0))
       (fun n0 : nat =>
        get_nat_tree'
          (if Nat.eqb n0 0
           then ITree.subst k2 (Ret false)
           else if Nat.eqb n0 1 then ITree.subst k2 (Ret true) else ITree.spin))) = observe (Vis (nat_ev (if b then 1 else 0))
       (fun n0 : nat =>
        get_nat_tree'
          (if Nat.eqb n0 0
           then ITree.subst k2 (Ret false)
           else if Nat.eqb n0 1 then ITree.subst k2 (Ret true) else ITree.spin)))) as EQVIS by reflexivity.

              rewrite EQVIS.

              eapply Interp_PropT_Vis with
                (k2:= fun v =>
                        (get_nat_tree'
                           (if Nat.eqb v 0
                            then ITree.subst k2 (Ret false)
                            else if Nat.eqb v 1 then ITree.subst k2 (Ret true) else ITree.spin))).

              2: {
                red.
                reflexivity.
              }
              2: {
                cbn.
                rewrite bind_trigger.
                destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto;
                reflexivity.
              }

              intros a RET.
              right.
              
              econstructor; auto.
              
              setoid_rewrite VIS_HANDLED.
              
              rewrite VIS_HANDLED.
                        eapply Interp_PropT_Vis with (k2:=fun x => k4 x).
              
              destruct HANDLER; subst; setoid_rewrite bind_ret_l in VIS_HANDLED.
              - (* True *)
                specialize (HK true).
                forward HK. constructor; reflexivity.
                pclearbot.
                rewrite <- VIS_HANDLED in HK.

                (* eapply paco2_mon_bot; eauto. *)
                (* rewrite VIS. *)

                (* pstep; red; cbn. *)
                (* constructor; auto. *)

                (* eapply Interp_PropT_Vis with (k2:=(fun b => (get_nat_tree' {| _observe := observe (k2 b) |}))). *)
                (* 2: { *)
                (*   red. left; reflexivity. *)
                (* } *)

                (* 2: { *)
                (*   setoid_rewrite bind_ret_l. *)
                (*   rewrite VIS_HANDLED. *)
                (*   reflexivity. *)
                (* } *)

                (* intros a H. *)
                (* left. *)

                rewrite (itree_eta_ t2) in HK.
                rewrite (itree_eta_ t2) in VIS_HANDLED.
                genobs t2 ot2.
                clear Heqot2 t2.

                punfold VIS. red in VIS. cbn in VIS.
                rewrite (itree_eta_ m1).
                genobs m1 om1.
                clear Heqom1 m1.

                punfold HK. red in HK. cbn in HK.

                dependent induction VIS.
                { red in REL.
                  pclearbot.

                  dependent induction HK.
                  - Opaque get_nat_tree'.
                    pstep; red; cbn.
                    constructor; auto.
                    cbn.

                    eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' (Ret r2)).
                    2: {
                      red. left; reflexivity.
                    }
                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                    right.

                    rewrite (itree_eta_ (k3 true)).
                    rewrite (itree_eta_ (Ret _)).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.

                      specialize (K_RUTT true true).
                      forward K_RUTT; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                      setoid_rewrite <- x in K_RUTT.

                      setoid_rewrite EQ.
                      pstep; red; cbn.
                      eauto.
                    + cbn.
                      pstep; red; cbn.
                      constructor; auto.
                  - pstep; red; cbn.
                    Transparent get_nat_tree'.
                    cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        left; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      rewrite <- x.
                      constructor; auto.
                      pclearbot.
                      punfold HS.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := t2 |}).
                    2: {
                      red.
                      left; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 true)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT true true).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.
                      constructor; auto.
                  - pstep; red; cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        left; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      auto.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := observe t2 |}).
                    2: {
                      red.
                      left; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 true)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL true).
                      assert (k3 true ≈ k1 true) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT true true).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.

                      destruct e.
                      { destruct n.
                        red in H.
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK true).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            left; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            right; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                      }

                      { red in H.

                        eapply Interp_PropT_Vis with (k2:=fun x => k4 x).
                        2: {
                          red.
                          eauto.
                        }

                        2: {
                          eauto.
                        }

                        intros a H1.
                        apply HK in H1.
                        eauto.
                      }
                }

                { (* Tau... *)
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  specialize (IHVIS k1 eq_refl I).
                  forward IHVIS; auto.
                  pstep; red; cbn.
                  constructor; auto.
                  punfold IHVIS; red in IHVIS; cbn in IHVIS.
                  setoid_rewrite <- itree_eta_ in IHVIS.
                  cbn in *.
                  auto.
                }

              - (* False *)
                specialize (HK false).
                forward HK. constructor; reflexivity.
                pclearbot.
                rewrite <- VIS_HANDLED in HK.

                (* eapply paco2_mon_bot; eauto. *)
                (* rewrite VIS. *)

                (* pstep; red; cbn. *)
                (* constructor; auto. *)

                (* eapply Interp_PropT_Vis with (k2:=(fun b => (get_nat_tree' {| _observe := observe (k2 b) |}))). *)
                (* 2: { *)
                (*   red. left; reflexivity. *)
                (* } *)

                (* 2: { *)
                (*   setoid_rewrite bind_ret_l. *)
                (*   rewrite VIS_HANDLED. *)
                (*   reflexivity. *)
                (* } *)

                (* intros a H. *)
                (* left. *)

                rewrite (itree_eta_ t2) in HK.
                rewrite (itree_eta_ t2) in VIS_HANDLED.
                genobs t2 ot2.
                clear Heqot2 t2.

                punfold VIS. red in VIS. cbn in VIS.
                rewrite (itree_eta_ m1).
                genobs m1 om1.
                clear Heqom1 m1.

                punfold HK. red in HK. cbn in HK.

                dependent induction VIS.
                { red in REL.
                  pclearbot.

                  dependent induction HK.
                  - Opaque get_nat_tree'.
                    pstep; red; cbn.
                    constructor; auto.
                    cbn.

                    eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' (Ret r2)).
                    2: {
                      red. right; reflexivity.
                    }
                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                    right.

                    rewrite (itree_eta_ (k3 false)).
                    rewrite (itree_eta_ (Ret _)).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                      setoid_rewrite <- x in K_RUTT.

                      setoid_rewrite EQ.
                      pstep; red; cbn.
                      eauto.
                    + cbn.
                      pstep; red; cbn.
                      constructor; auto.
                  - pstep; red; cbn.
                    Transparent get_nat_tree'.
                    cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        right; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      rewrite <- x.
                      constructor; auto.
                      pclearbot.
                      punfold HS.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := t2 |}).
                    2: {
                      red.
                      right; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 false)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.
                      constructor; auto.
                  - pstep; red; cbn.
                    constructor.
                    right.

                    rewrite (itree_eta_ (Vis _ _)).
                    rewrite (itree_eta_ t2).

                    eapply CIH.
                    + rewrite <- itree_eta_.
                      pstep; red; cbn.

                      eapply Rutt.EqVis with (e2 := (inl1 Or)); auto.
                      intros a b H.
                      cbn in H. subst.

                      specialize (REL b).
                      assert (k3 b ≈ k1 b) as EQ by auto.

                      specialize (K_RUTT b b).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      left.
                      assert (rutt (@top_level_rel) (@top_level_rel_ans) nb (k3 b) (k b)).
                      { setoid_rewrite EQ.
                        pstep; red; cbn.
                        apply K_RUTT.
                      }

                      pstep; red; cbn.
                      punfold H.
                    + pstep; red; cbn.
                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        right; auto.
                      }
                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      left.
                      pstep; red; cbn.
                      auto.
                  - pstep; red; cbn.
                    constructor; auto.
                    cbn.
                    eapply Interp_PropT_Vis with (k2:=fun _ => get_nat_tree' {| _observe := observe t2 |}).
                    2: {
                      red.
                      right; auto.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    intros a RET.
                    eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                    right.

                    rewrite (itree_eta_ (k3 false)).
                    eapply CIH.
                    + rewrite <- itree_eta_.

                      specialize (REL false).
                      assert (k3 false ≈ k1 false) as EQ by auto.
                      rewrite EQ.

                      specialize (K_RUTT false false).
                      forward K_RUTT; cbn; auto.
                      punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.

                      pstep; red; cbn.
                      eauto.
                    + pstep; red; cbn.
                      setoid_rewrite <- x.

                      destruct e.
                      { destruct n.
                        red in H.
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK true).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            left; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            right; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                      }

                      { red in H.

                        eapply Interp_PropT_Vis with (k2:=fun x => k4 x).
                        2: {
                          red.
                          eauto.
                        }

                        2: {
                          eauto.
                        }

                        intros a H1.
                        apply HK in H1.
                        eauto.
                      }
                }

                { (* Tau... *)
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  forward IHVIS; auto.
                  specialize (IHVIS k1 eq_refl I).
                  forward IHVIS; auto.
                  pstep; red; cbn.
                  constructor; auto.
                  punfold IHVIS; red in IHVIS; cbn in IHVIS.
                  setoid_rewrite <- itree_eta_ in IHVIS.
                  cbn in *.
                  auto.
                }
            }

            
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            left; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                          2: {
                            red.
                            right; auto.
                          }

                          2: {
                            setoid_rewrite bind_ret_l.
                            reflexivity.
                          }

                          intros a RET.
                          eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                          left.
                          rewrite H0.
                          auto.
                      }
                        -

                        red in H.
                        destruct H; subst; setoid_rewrite bind_ret_l in H0.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          left.
                          rewrite H0.
                          auto.
                        - specialize (HK false).
                          forward HK.
                          constructor; reflexivity.
                          pclearbot.

                          left.
                          rewrite H0.
                          auto.
                        
                        specialize (HK false).
                        forward HK.
                        constructor. reflexivity.
                        right.

                        rewrite (itree_eta_ (k3 false)).
                        eapply CIH.

                        2: 
                          econstructor; auto.

                      }

                      eapply Interp_PropT_Vis with (k2:=fun _ => t2).
                      2: {
                        red.
                        left; auto.
                      }

                      2: {
                        setoid_rewrite bind_ret_l.
                        reflexivity.
                      }

                      intros a RET.
                      eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                      right.

                      rewrite (itree_eta_ (k3 false)).
                      eapply CIH.

                      2: 
                      econstructor; auto.
                    
                }

                
                dependent induction HK.
                { setoid_rewrite <- x in K_RUTT.

                }

                genobs (k false) okt.
                setoid_rewrite <- Heqokt in HK.
                clear Heqokt.

                
                
                dependent induction VIS.
                { admit.

                }


                induction om1, ot2.

                dependent induction ot2.
                + pstep; red; cbn.
                  constructor; auto.
                  
                
                punfold HK. red in HK.
                dependent induction HK; subst.
                admit.
                admit.
                + admit.
                + 
                + rewrite <- x.
                  pstep; red; cbn.
                  constructor; eauto.

                  punfold VIS. red in VIS.
                  dependent induction VIS.
                  -- admit.
                  -- 
                  -- rewrite <- x.
                     assert ((@RetF NatEvent nat (itree NatEvent nat) (if r2 then 1 else 0)) = observe ((Ret (if r2 then 1 else 0)))).
                     reflexivity.
                     rewrite H.

                     eapply Interp_PropT_Vis with (k2:=fun _ => Ret (if r2 then 1 else 0)).
                     econstructor.
                     2: {
                       red.
                       left; reflexivity.
                     }
                     2: {
                       setoid_rewrite bind_ret_l.
                       reflexivity.
                     }

                     rename H0 into RET.
                     eapply Returns_Ret_ in RET; [| reflexivity].
                     subst.

                     specialize (REL true).
                     red in REL.
                     pclearbot.

                     specialize (K_RUTT true true).
                     forward K_RUTT.
                     cbn. auto.

                     replace (k1 true) with (k3 true) in K_RUTT.
                     2: admit.

                     punfold K_RUTT.
                     red in K_RUTT; cbn in K_RUTT.
                     setoid_rewrite <- x0 in K_RUTT.

                     clear x0 x1.

                     dependent induction K_RUTT.
                     { pstep; red; cbn.
                       setoid_rewrite <- x.
                       constructor.
                       destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
                     }
                     { pstep; red; cbn.
                       setoid_rewrite <- x.
                       constructor; auto.

                       specialize (IHK_RUTT r2 k3 REL).
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                       forward IHK_RUTT; auto.
                     }

                     
                     rewrite REL.

                     
                
                rewrite (itree_eta_ t2) in VIS_HANDLED, HK.
                genobs t2 ot2.
                clear t2 Heqot2.
                destruct ot2.
                + eapply paco2_mon_bot; eauto.
                  rewrite VIS.
                  rewrite tau_eutt.
                  pstep; red.
                  econstructor.
                + pstep; red; cbn.
                  constructor.
                  right.
                  rewrite (itree_eta_ m1).
                  rewrite (itree_eta_ t).
                  eapply CIH.

                  rewrite VIS_HANDLED in HK.
                  rewrite VIS.
                  cbn.
                  pstep; red; cbn.
                  econstructor.
                  2: {
                    intros a b H.
                    left.
                    eapply K_RUTT.
                    eapply H.
                  }
                  cbn; auto.

                  pstep; red; cbn.
                  econstructor.
                  3: {
                    rewrite <- (tau_eutt t).
                    rewrite VIS_HANDLED.
                  }

                    punfold HK. red in HK.
                  dependent induction HK.
                  -- punfold K_RUTT; red in K_RUTT; cbn in K_RUTT.
                     setoid_rewrite <- x in K_RUTT.
                     inversion 
                     pstep; red; cbn.
                     constructor; auto.

                
                (* Maybe I don't want to do this... Can use CIH for vis, in theory... *)
                eapply paco2_mon_bot; eauto.
                rewrite tau_eutt.
                rewrite VIS_HANDLED.
                rewrite VIS.
                
                pstep; red; cbn.
                eapply Interp_PropT_Vis with (k2:=(fun b => (get_nat_tree' {| _observe := observe (k2 b) |}))).

                2: {
                  red.
                  left.
                  reflexivity.
                }

                2: {
                  setoid_rewrite bind_ret_l.
                  reflexivity.
                }

                intros a RET.
                eapply Returns_Ret_ in RET; [| reflexivity].
                subst.

                right.


                punfold VIS_HANDLED.
                red in VIS_HANDLED.

                punfold HK. red in HK.
                dependent induction VIS_HANDLED.
                + rewrite <- x0 in *.
                  rewrite <- x in *.
                  subst.

                  eapply paco2_mon_bot; eauto.
                  rewrite tau_eutt.
                  rewrite H1.
                  pstep; red; cbn.
                  cbn.
                  assert (@RetF NatEvent nat _ (if r2 then 1 else 0) = observe (ret (if r2 then 1 else 0))). reflexivity.
                  rewrite H.
                  eapply Interp_PropT_Vis with (k2:=(fun _ => ret (if r2 then 1 else 0))).
                  2: {
                    red.
                    left; auto.
                  }
                  2: {
                    cbn.
                    rewrite bind_ret_l.
                    reflexivity.
                  }

                  intros a H0.
                  left.

                  eapply Returns_Ret_ in H0; [| reflexivity].
                  subst.

                  punfold ANS_REL. red in ANS_REL; cbn in ANS_REL.
                  rewrite (itree_eta_ (k1 true)).

                  { dependent induction ANS_REL.
                    - rewrite <- x2.
                      setoid_rewrite <- x in HK.
                      inversion HK; subst.

                      pstep; red; cbn.
                      constructor.
                      destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
                    - rewrite <- x2.
                      pstep; red; cbn.
                      constructor; auto.
                      
                      
                  }

                (* I probably need to save `r` in the paco2 relation
                   because I'm going to need to use CIH? *)

                specialize (CIH (observe (k1 true)) (observe (k true)) (observe (k2 true))).
                forward CIH.
                { repeat rewrite <- itree_eta_.
                  auto.
                }
                forward CIH.
                { repeat rewrite <- itree_eta_.
                  apply HK.
                }

                (* I believe for interp_prop, I can only actually use CIH for the tau / tau case.. *)
                clear CIH.

                (* THIS MIGHT CAUSE PROBLEMS LATER IF I NEED TO PRESERVE r *)
                (* Probably not the case, though, because I cannot use the CIH... Unless observe t2 is a tau... *)
                eapply paco2_mon_bot; eauto.
                rewrite H1.
                rewrite tau_eutt.
                rewrite VIS_HANDLED.

                cbn.
                pstep; red; cbn.
                eapply Interp_PropT_Vis with (k2:=fun b => get_nat_tree' {| _observe := observe (k2 b) |}).
                2: {
                  red.
                  left.
                  constructor.
                }

                intros a H.
                left.

                2: {
                  setoid_rewrite bind_ret_l.
                  reflexivity.
                }

                pstep. red.

                right.
                
                rewrite <- H7 in HK.
                
                punfold H7. red in H7.
                
                admit.
              - admit.
            }
            { (* nat_ev / bool_ev *)
              destruct b.
              
            }
            

            inversion RUN; subst.
            { pstep. red.
              cbn.
              constructor.
              right.

              

            }

            eapply paco2_mon_bot; eauto.
            setoid_rewrite H.
            rewrite tau_eutt.

            rewrite H7.
            red in H6.
            destruct e.
            + destruct n.
              destruct e1; cbn in H0.
              -- destruct n.
                 destruct H6; subst; setoid_rewrite bind_ret_l; cbn.
                 ++ pstep; red; cbn.
                    eapply Interp_PropT_Vis with (k2:=(fun b => get_nat_tree' {| _observe := observe (k3 b) |})).

                    intros a H2.
                    2: {
                      red.
                      left.
                      reflexivity.
                    }

                    2: {
                      setoid_rewrite bind_ret_l.
                      reflexivity.
                    }

                    left.
                    
                    intros a H2.
                    2: {
                      red.
                      left.
                      reflexivity.
                    }

                    left.
                    reflexivity.

                 
              -- setoid_rewrite bind_ret_l.
                 specialize (HK true).
                 forward HK. constructor; reflexivity.
                 pclearbot.

                    



          (* TODO: interp_PropTF inversion lemma *)
          Set Nested Proofs Allowed.
          Lemma interp_prop_inv_vis_l :
            
          

          
          apply interp_prop_vis_inv in RUN.
          apply interp_prop
        }

            


          eapply interp_prop_inv_tau_l in RUN.
          eapply interp_prop_

          eapply paco2_mon_bot; eauto.
          rewrite H'.

          pstep; red; cbn.
          constructor; auto.
          cbn.
          

          
          


          specialize (IHRUN (Ret r1).
          eapply IHRUN.
          rewrite tau_eutt.

          pstep; red; cbn; auto.

          pstep; red; cbn.


          eapply paco
          Import Morphisms.
          epose proof (interp_prop_eutt_Proper nondetE_handle eq (Tau m1)).
          unfold Proper, respectful in H.
          assert (Tau m1 ≈ Ret r1).
          { rewrite H'. rewrite tau_eutt. reflexivity. }
          specialize (H _ H0).
          specialize (H (get_nat_tree' {| _observe := t2 |}) (get_nat_tree' {| _observe := t2 |})).
          forward H.
          reflexivity.
          destruct H.
          forward H1.
          repeat red in H1.
          pfold.
          red.
          apply H1.
          
          apply H in H0.
          eapply interp_prop_eutt_Proper.
          eapply interp_prop_Proper_R3.
          pstep; red; cbn.
          
          rewrite H'.
          punfold H'. red in H'.
          cbn in *.
          admit.
        }

        { (* Tau *)
          apply rutt_inv_Tau_r in H'.
          eapply IHRUN; eauto.
        }

        { (* Vis *)
          
        }
        
        { setoid_rewrite Hm2 in RUN.
          inversion RUN; subst.
          + punfold H'; red in H'.
            cbn in H'.
            inversion H'; subst.
            -- pstep; red; cbn.
               constructor; auto.
               cbn.
               destruct H1 as [[R1 R3] | [R1 R3]]; subst; cbn; auto.
            -- pstep; red; cbn.
               constructor; auto.
               cbn.
               constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
              eapply CIH.


              constructor; auto.
               right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.

            eapply paco2_mon_bot; eauto.

          punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          + rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            -- pstep; red; cbn.
               constructor; auto.
               destruct H as [[R1 R3] | [R1 R3]]; subst; cbn; auto.
            -- pstep; red; cbn.
               constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          + rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            -- rewrite x. eapply IHH'.
               pstep; red; cbn.
               constructor; auto.
               cbn.
               rewrite x.
               constructor; auto.
               destruct H as [[R1 R3] | [R1 R3]]; subst; cbn; auto.

            -- 

            pstep; red; cbn.
            constructor; auto.
            constructor; auto.

            forward IHRUN; auto.
            specialize (IHRUN r2 H).
            forward IHRUN; auto.
            forward IHRUN; auto.

            pstep. red.
            cbn.
            constructor; auto.

            punfold IHRUN.
        }
        { punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - setoid_rewrite Hm2 in RUN.
            rewrite <- x.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor; auto.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.

            + 

            eapply IHRUN; eauto.
        }


        desobs m1 Hm1.
        { punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - setoid_rewrite <- x in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r0)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - eapply IHRUN; eauto.
        }

        { (* Tau *)
          apply rutt_inv_Tau_l in H'.
          eapply 
          eapply IHRUN; eauto.
          punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - eapply IHRUN. 2: symmetry; apply x.
            left.
            pstep; red; cbn.
            constructor.
            pclearbot.
            punfold H.
          - pstep; red; cbn.
            constructor; auto.
            cbn.
            constructor; auto.
            punfold H1.
            red.
            cbn
          punfold H'; red in H'; cbn in H'.
          pstep; red; cbn.
          constructor; eauto.

          specialize 

          rewrite <- Hm1.
          eapply IHRUN.
          rewrite Hm1.
          left.
          eapply rutt_Proper_R3.
          4: apply tau_eutt.
          red
          eapply rutt_Proper.
          setoid_rewrite tau_eutt.
          left.
          pstep. red. apply H'.
          dependent induction H'.
          - setoid_rewrite <- x in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r0)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - eapply IHRUN; eauto.

        }
    

          pstep; red; cbn.
          constructor; auto.
          cbn.
          punfold H'.
          red in H'.
          
          
          dependent induction H'.
          + inversion HeqM2; subst.
            rewrite <- 

            destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
          + forward IHRUN; auto.
            specialize (IHRUN r2 H).
            forward IHRUN; auto.
            forward IHRUN; auto.

            pstep. red.
            cbn.
            constructor; auto.

            punfold IHRUN.

          - 

        }

        inversion HeqM2; subst.
        eapply IHRUN.
        
        rewrite (itree_eta m1) in Hrutt.
        desobs m1 Hm1; clear m1 Hm1.
        pclearbot.
        punfold H'.
        red in H'.
        desobs m2 Hm2; setoid_rewrite Hm2 in IHRUN; clear m2 Hm2 RUN HeqM2.
        -- pstep; red; cbn.
           constructor; auto.

           inversion H'; subst.
           ++ 
           
           
        eapply IHRUN; eauto.
        
    - admit.
    - pstep. red.
      cbn.
      constructor; auto.

      forward IHREL; auto.
      forward IHREL; auto.
      punfold IHREL.
    - forward IHREL.
      { red.
        red in RUN.
        rewrite tau_eutt in RUN.
        rewrite (itree_eta_ t2) in RUN.
        auto.
      }

      forward IHREL; auto.
  }
      
      forward IHREL; auto.
      forward IHREL; auto.
      punfold IHREL.
      

    
    dependent induction ot_bool2.
    - punfold RUN; red in RUN.
      cbn in RUN.
      dependent induction RUN.
      + punfold REL; red in REL.
        cbn in REL.
        dependent induction REL.
        -- pstep.
           red.
           cbn.
           constructor.
           destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
        -- pstep.
           red.
           cbn.
           constructor; auto.

           specialize (IHREL r0).
           forward IHREL; auto.
           forward IHREL; auto.
           punfold IHREL.
      + punfold REL; red in REL.
        cbn in REL.
        dependent induction REL.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { rewrite <- (tau_eutt {| _observe := observe t1 |}).
             setoid_rewrite <- Eqit.itree_eta_.
             pstep. red.
             cbn.
             eapply Rutt.EqTauL.
             eauto.             
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             eauto.
           }
           forward IHRUN; auto.

           punfold IHRUN.
      + punfold REL; red in REL.
        cbn in REL.

        destruct e.
        { inversion n; subst.
          cbn in H.
          destruct n.
          destruct H as [TRUE | FALSE]; subst.
          { specialize (HK true).
            forward HK.
            constructor. reflexivity.
            pclearbot.

            setoid_rewrite bind_ret_l in H0.
            rewrite <- H0 in HK.
            punfold HK. red in HK.
            rewrite x in HK.
            inversion HK; subst.
            - inversion REL; subst_existT; cbn in *; subst.
              + pstep. red.
                Opaque get_nat_tree'.
                cbn.
                econstructor.
                -- intros a H.
                   left.
                   pstep.
                   red.


                specialize (H6  true).

            punfold H0.
            red in H0.
            rewrite x in H0.

            inversion H0; subst.
            + pstep. red.
              Opaque get_nat_tree'.
              cbn.
              inversion REL; subst_existT; cbn in *; subst.
              -- econstructor.
                 intros a H1; eauto.
                 specialize (H6 a r2).
                 right.

              

            cbn in H0.


            
          punfold H0.
          red in H0.
          rewrite x in H0.
          inversion H0; subst.

        
        dependent induction REL.
        -- destruct e.
           ++ inversion n; subst.
              cbn in H.
              destruct n.
              destruct H as [TRUE | FALSE]; subst.
              { pstep. red.
                cbn.

                specialize (HK true).
                forward HK.
                constructor. reflexivity.
                pclearbot.
              }

          pstep.
           red.
           cbn.


           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { rewrite <- (tau_eutt {| _observe := observe t1 |}).
             setoid_rewrite <- Eqit.itree_eta_.
             pstep. red.
             cbn.
             eapply Rutt.EqTauL.
             eauto.             
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             eauto.
           }
           forward IHRUN; auto.

           punfold IHRUN.

           specialize (IHREL t1).
           forward IHREL; auto.
           forward IHREL.
           { intros CIH0 r1 REL0 H.
             inversion H; subst.

             pstep. red.
             cbn.

           }

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- 

           red in IHRUN.
           cbn in IHRUN.
           
           forward IHREL; auto.
           punfold IHREL.
           
           red in REL.
           inversion REL; subst.
           destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.


           destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
        -- pstep.
           red.
           cbn.
           constructor; auto.

           specialize (IHREL r0).
           forward IHREL; auto.
           forward IHREL; auto.
           punfold IHREL.
           
           red in REL.
           inversion REL; subst.
           destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.
           destruct
    
    pinversion REL.
    - (* Both t_nat and t_bool were ret nodes

         This means t_bool2 is either:

         - A ret node
         - Tau on the right
       *)

      subst.
      pstep.
      red.
      setoid_rewrite <- H.

      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* t_bool2 is a ret *)
        rewrite <- x.
        cbn.
        constructor.
        subst.
        red in H1.
        destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.
      + (* t_bool2 is a tau on the right... *)
        (* Need some kind of inductive hypothesis, I think *)
        rewrite <- x.
        cbn.
        constructor; auto.

        setoid_rewrite (itree_eta_ t2).
        eapply IHRUN; eauto.
    - (* Double tau nodes *)
      pose proof RUN as RUN2.
      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* Tau *)
        subst.
        pstep.
        red.
        setoid_rewrite <- H.

        rewrite <- x.
        cbn.
        constructor.
        right.
        eapply CIH; eauto.

        red in RUN2.
        red.
        eapply interp_prop_eutt_Proper_impl.
        apply tau_eutt.
        apply tau_eutt.
        setoid_rewrite H0.
        setoid_rewrite x.

        pstep.
        red.
        cbn.
        punfold RUN2.
      + (* TauL *)
        pstep. red.
        setoid_rewrite <- H.
        constructor; auto.
        eapply IHRUN; eauto.


Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree' t_bool2).
  split.
  { revert RUN.
    revert REL.

    setoid_rewrite (itree_eta_ t_nat).
    setoid_rewrite (itree_eta_ t_bool).
    setoid_rewrite (itree_eta_ t_bool2).

    genobs t_nat ot_nat.
    genobs t_bool ot_bool.
    genobs t_bool2 ot_bool2.
    clear t_nat Heqot_nat.
    clear t_bool Heqot_bool.
    clear t_bool2 Heqot_bool2.

    revert ot_nat ot_bool ot_bool2.
    pcofix CIH.
    intros ot_nat ot_bool ot_bool2 REL RUN.

    (* I want to know that the generated tree refines `t_nat`...

       
     *)
    punfold REL.
    red in REL.
    cbn in REL.

    remember (upaco2 (rutt_ (@top_level_rel) (@top_level_rel_ans) nb) bot2) as r'.
    revert Heqr'.

    dependent induction REL; intros Heqr'.
    - subst.
      apply interp_prop_ret_inv in RUN.
      destruct RUN as [r3 [REQ EQ]]; subst.

      (assert (get_nat_tree' {| _observe := ot_bool2 |} ≈ (get_nat_tree' (ret r3)))).
      { rewrite <- EQ.
        reflexivity.
      }

      eapply paco2_mon_bot; eauto.
      rewrite H0.

      pstep; red; cbn.
      constructor.
      destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
    - punfold RUN.
      red in RUN.
      cbn in RUN.

      dependent induction RUN.
      + pstep; red; cbn.
        constructor.
        destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
      + forward IHRUN; auto.
        specialize (IHRUN r2 H).
        forward IHRUN; auto.
        forward IHRUN; auto.

        pstep. red.
        cbn.
        constructor; auto.

        punfold IHRUN.
    - punfold RUN.
      red in RUN.
      cbn in RUN.

      subst.
      remember (TauF m2) as M2.
      revert m1 m2 H HeqM2.
      induction RUN; intros m1 m2 H' HeqM2; try discriminate.
      + pstep. red. cbn.
        constructor; auto.
        right.

        specialize (CIH (observe m1) (observe m2) (observe t2)).
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ t2).

        eapply CIH.

        pclearbot.
        repeat rewrite <- itree_eta_.
        apply H'.

        pclearbot.
        repeat rewrite <- itree_eta_.

        inversion HeqM2; subst.
        apply HS.
      + (* Need to apply IHRUN *)
        inversion HeqM2; subst.
        clear HeqM2.

        pclearbot.
        setoid_rewrite (itree_eta_ m2) in H'.
        desobs m2 Hm2; setoid_rewrite Hm2 in RUN; setoid_rewrite Hm2 in IHRUN.
        { (* Ret *)
          eapply rutt_inv_Ret_r in H'.
          destruct H' as [r1 [H' NB]].
          
          eapply paco2_mon_bot; eauto.
          rewrite H'.

          specialize (IHRUN (Ret r1) 
          eapply IHRUN.
          rewrite tau_eutt.

          pstep; red; cbn; auto.

          pstep; red; cbn.


          eapply paco
          Import Morphisms.
          epose proof (interp_prop_eutt_Proper nondetE_handle eq (Tau m1)).
          unfold Proper, respectful in H.
          assert (Tau m1 ≈ Ret r1).
          { rewrite H'. rewrite tau_eutt. reflexivity. }
          specialize (H _ H0).
          specialize (H (get_nat_tree' {| _observe := t2 |}) (get_nat_tree' {| _observe := t2 |})).
          forward H.
          reflexivity.
          destruct H.
          forward H1.
          repeat red in H1.
          pfold.
          red.
          apply H1.
          
          apply H in H0.
          eapply interp_prop_eutt_Proper.
          eapply interp_prop_Proper_R3.
          pstep; red; cbn.
          
          rewrite H'.
          punfold H'. red in H'.
          cbn in *.
          admit.
        }

        { (* Tau *)
          apply rutt_inv_Tau_r in H'.
          eapply IHRUN; eauto.
        }

        { (* Vis *)
          
        }
        
        { setoid_rewrite Hm2 in RUN.
          inversion RUN; subst.
          + punfold H'; red in H'.
            cbn in H'.
            inversion H'; subst.
            -- pstep; red; cbn.
               constructor; auto.
               cbn.
               destruct H1 as [[R1 R3] | [R1 R3]]; subst; cbn; auto.
            -- pstep; red; cbn.
               constructor; auto.
               cbn.
               constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
              eapply CIH.


              constructor; auto.
               right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.

            eapply paco2_mon_bot; eauto.

          punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          + rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            -- pstep; red; cbn.
               constructor; auto.
               destruct H as [[R1 R3] | [R1 R3]]; subst; cbn; auto.
            -- pstep; red; cbn.
               constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          + rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            -- rewrite x. eapply IHH'.
               pstep; red; cbn.
               constructor; auto.
               cbn.
               rewrite x.
               constructor; auto.
               destruct H as [[R1 R3] | [R1 R3]]; subst; cbn; auto.

            -- 

            pstep; red; cbn.
            constructor; auto.
            constructor; auto.

            forward IHRUN; auto.
            specialize (IHRUN r2 H).
            forward IHRUN; auto.
            forward IHRUN; auto.

            pstep. red.
            cbn.
            constructor; auto.

            punfold IHRUN.
        }
        { punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - setoid_rewrite Hm2 in RUN.
            rewrite <- x.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - rewrite <- x.
            setoid_rewrite Hm2 in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor; auto.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r1)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.

            + 

            eapply IHRUN; eauto.
        }


        desobs m1 Hm1.
        { punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - setoid_rewrite <- x in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r0)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - eapply IHRUN; eauto.
        }

        { (* Tau *)
          apply rutt_inv_Tau_l in H'.
          eapply 
          eapply IHRUN; eauto.
          punfold H'; red in H'; cbn in H'.
          dependent induction H'.
          - eapply IHRUN. 2: symmetry; apply x.
            left.
            pstep; red; cbn.
            constructor.
            pclearbot.
            punfold H.
          - pstep; red; cbn.
            constructor; auto.
            cbn.
            constructor; auto.
            punfold H1.
            red.
            cbn
          punfold H'; red in H'; cbn in H'.
          pstep; red; cbn.
          constructor; eauto.

          specialize 

          rewrite <- Hm1.
          eapply IHRUN.
          rewrite Hm1.
          left.
          eapply rutt_Proper_R3.
          4: apply tau_eutt.
          red
          eapply rutt_Proper.
          setoid_rewrite tau_eutt.
          left.
          pstep. red. apply H'.
          dependent induction H'.
          - setoid_rewrite <- x in RUN.
            inversion RUN; subst.
            + pstep; red; cbn.
              constructor; auto.
              constructor.
              destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
            + pstep; red; cbn.
              constructor; auto.

              rewrite (itree_eta_ (Ret r0)).
              rewrite (itree_eta_ t0).
              right.

              eapply CIH.
              pstep; red; cbn.
              constructor; eauto.

              pstep; red; cbn.
              auto.
          - eapply IHRUN; eauto.

        }
    

          pstep; red; cbn.
          constructor; auto.
          cbn.
          punfold H'.
          red in H'.
          
          
          dependent induction H'.
          + inversion HeqM2; subst.
            rewrite <- 

            destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
          + forward IHRUN; auto.
            specialize (IHRUN r2 H).
            forward IHRUN; auto.
            forward IHRUN; auto.

            pstep. red.
            cbn.
            constructor; auto.

            punfold IHRUN.

          - 

        }

        inversion HeqM2; subst.
        eapply IHRUN.
        
        rewrite (itree_eta m1) in Hrutt.
        desobs m1 Hm1; clear m1 Hm1.
        pclearbot.
        punfold H'.
        red in H'.
        desobs m2 Hm2; setoid_rewrite Hm2 in IHRUN; clear m2 Hm2 RUN HeqM2.
        -- pstep; red; cbn.
           constructor; auto.

           inversion H'; subst.
           ++ 
           
           
        eapply IHRUN; eauto.
        
    - admit.
    - pstep. red.
      cbn.
      constructor; auto.

      forward IHREL; auto.
      forward IHREL; auto.
      punfold IHREL.
    - forward IHREL.
      { red.
        red in RUN.
        rewrite tau_eutt in RUN.
        rewrite (itree_eta_ t2) in RUN.
        auto.
      }

      forward IHREL; auto.
  }
      
      forward IHREL; auto.
      forward IHREL; auto.
      punfold IHREL.
      

    
    dependent induction ot_bool2.
    - punfold RUN; red in RUN.
      cbn in RUN.
      dependent induction RUN.
      + punfold REL; red in REL.
        cbn in REL.
        dependent induction REL.
        -- pstep.
           red.
           cbn.
           constructor.
           destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
        -- pstep.
           red.
           cbn.
           constructor; auto.

           specialize (IHREL r0).
           forward IHREL; auto.
           forward IHREL; auto.
           punfold IHREL.
      + punfold REL; red in REL.
        cbn in REL.
        dependent induction REL.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { rewrite <- (tau_eutt {| _observe := observe t1 |}).
             setoid_rewrite <- Eqit.itree_eta_.
             pstep. red.
             cbn.
             eapply Rutt.EqTauL.
             eauto.             
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             eauto.
           }
           forward IHRUN; auto.

           punfold IHRUN.
      + punfold REL; red in REL.
        cbn in REL.

        destruct e.
        { inversion n; subst.
          cbn in H.
          destruct n.
          destruct H as [TRUE | FALSE]; subst.
          { specialize (HK true).
            forward HK.
            constructor. reflexivity.
            pclearbot.

            setoid_rewrite bind_ret_l in H0.
            rewrite <- H0 in HK.
            punfold HK. red in HK.
            rewrite x in HK.
            inversion HK; subst.
            - inversion REL; subst_existT; cbn in *; subst.
              + pstep. red.
                Opaque get_nat_tree'.
                cbn.
                econstructor.
                -- intros a H.
                   left.
                   pstep.
                   red.


                specialize (H6  true).

            punfold H0.
            red in H0.
            rewrite x in H0.

            inversion H0; subst.
            + pstep. red.
              Opaque get_nat_tree'.
              cbn.
              inversion REL; subst_existT; cbn in *; subst.
              -- econstructor.
                 intros a H1; eauto.
                 specialize (H6 a r2).
                 right.

              

            cbn in H0.


            
          punfold H0.
          red in H0.
          rewrite x in H0.
          inversion H0; subst.

        
        dependent induction REL.
        -- destruct e.
           ++ inversion n; subst.
              cbn in H.
              destruct n.
              destruct H as [TRUE | FALSE]; subst.
              { pstep. red.
                cbn.

                specialize (HK true).
                forward HK.
                constructor. reflexivity.
                pclearbot.
              }

          pstep.
           red.
           cbn.


           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { rewrite <- (tau_eutt {| _observe := observe t1 |}).
             setoid_rewrite <- Eqit.itree_eta_.
             pstep. red.
             cbn.
             eapply Rutt.EqTauL.
             eauto.             
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- pstep.
           red.
           cbn.

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             eauto.
           }
           forward IHRUN; auto.

           punfold IHRUN.

           specialize (IHREL t1).
           forward IHREL; auto.
           forward IHREL.
           { intros CIH0 r1 REL0 H.
             inversion H; subst.

             pstep. red.
             cbn.

           }

           forward IHRUN; auto.
           specialize (IHRUN r0).
           forward IHRUN.
           { pstep. red.
             cbn.
             constructor.
             pclearbot.
             punfold H.
           }
           forward IHRUN; auto.

           punfold IHRUN.
        -- 

           red in IHRUN.
           cbn in IHRUN.
           
           forward IHREL; auto.
           punfold IHREL.
           
           red in REL.
           inversion REL; subst.
           destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.


           destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
        -- pstep.
           red.
           cbn.
           constructor; auto.

           specialize (IHREL r0).
           forward IHREL; auto.
           forward IHREL; auto.
           punfold IHREL.
           
           red in REL.
           inversion REL; subst.
           destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.
           destruct
    
    pinversion REL.
    - (* Both t_nat and t_bool were ret nodes

         This means t_bool2 is either:

         - A ret node
         - Tau on the right
       *)

      subst.
      pstep.
      red.
      setoid_rewrite <- H.

      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* t_bool2 is a ret *)
        rewrite <- x.
        cbn.
        constructor.
        subst.
        red in H1.
        destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.
      + (* t_bool2 is a tau on the right... *)
        (* Need some kind of inductive hypothesis, I think *)
        rewrite <- x.
        cbn.
        constructor; auto.

        setoid_rewrite (itree_eta_ t2).
        eapply IHRUN; eauto.
    - (* Double tau nodes *)
      pose proof RUN as RUN2.
      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* Tau *)
        subst.
        pstep.
        red.
        setoid_rewrite <- H.

        rewrite <- x.
        cbn.
        constructor.
        right.
        eapply CIH; eauto.

        red in RUN2.
        red.
        eapply interp_prop_eutt_Proper_impl.
        apply tau_eutt.
        apply tau_eutt.
        setoid_rewrite H0.
        setoid_rewrite x.

        pstep.
        red.
        cbn.
        punfold RUN2.
      + (* TauL *)
        pstep. red.
        setoid_rewrite <- H.
        constructor; auto.
        eapply IHRUN; eauto.

Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree' t_bool2).
  split.
  { revert RUN.
    revert REL.
    revert t_nat t_bool t_bool2.
    pcofix CIH.
    intros t_nat t_bool t_bool2 REL RUN.

    (* I want to know that the generated tree refines `t_nat`...

       
     *)
    
    pinversion REL.
    - (* Both t_nat and t_bool were ret nodes

         This means t_bool2 is either:

         - A ret node
         - Tau on the right
       *)

      subst.
      pstep.
      red.
      setoid_rewrite <- H.

      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* t_bool2 is a ret *)
        rewrite <- x.
        cbn.
        constructor.
        subst.
        red in H1.
        destruct H1 as [[R1 R3] | [R1 R3]]; subst; auto.
      + (* t_bool2 is a tau on the right... *)
        (* Need some kind of inductive hypothesis, I think *)
        rewrite <- x.
        cbn.
        constructor; auto.

        setoid_rewrite (itree_eta_ t2).
        eapply IHRUN; eauto.
    - (* Double tau nodes *)
      pose proof RUN as RUN2.
      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).

      dependent induction RUN.
      + (* Tau *)
        subst.
        pstep.
        red.
        setoid_rewrite <- H.

        rewrite <- x.
        cbn.
        constructor.
        right.
        eapply CIH; eauto.

        red in RUN2.
        red.
        eapply interp_prop_eutt_Proper_impl.
        apply tau_eutt.
        apply tau_eutt.
        setoid_rewrite H0.
        setoid_rewrite x.

        pstep.
        red.
        cbn.
        punfold RUN2.
      + (* TauL *)
        pstep. red.
        setoid_rewrite <- H.
        constructor; auto.
        eapply IHRUN; eauto.

        
        right.
        eapply CIH; eauto.

        red in RUN2.
        red.
        eapply interp_prop_eutt_Proper_impl.
        apply tau_eutt.
        apply tau_eutt.
        setoid_rewrite H0.
        setoid_rewrite x.

        pstep.
        red.
        cbn.
        punfold RUN2.

        

        unfold get_nat_tree'.

      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).
      clear - H H1 RUN.
      genobs t_bool2 otb2.
      clear t_bool2 Heqotb2.
      dependent induction RUN; subst.
      + (* t_bool2 is ret *)
        pfold. red.
        setoid_rewrite <- H.
        cbn.

        constructor.

        red in H1.
        destruct H1; destruct H0; subst; auto.
      + (* t_bool2 is a Tau node... TauR in Run *)
        pfold.
        red.
        cbn.
        constructor; auto.
        pose proof (IHRUN r2).
        forward H0.
        reflexivity.
        specialize (H0 H1 H).
        punfold H0.
    - (* Double tau *)

      (* Both t_nat and t_bool are Tau nodes... *)

(*          t_bool2 is either: *)

(*          - Tau *)
(*          - Anything (TauL) *)
(*        *)

      
      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).
      pstep. red.
      setoid_rewrite <- H.
      clear - CIH H1 RUN.
      genobs t_bool2 otb2.
      clear t_bool2 Heqotb2.
      pose proof RUN as RUN'.
      constructor; auto.

      rewrite (itree_eta_ m1) in H1.
      revert m1 H1.
      dependent induction RUN; subst; intros om1 H1.
      + cbn. constructor; auto.
        pclearbot.
        right.
        eauto.
      + constructor; auto.
        right.
        pclearbot.
        eapply CIH; eauto.
      + eapply IHRUN.
        apply CIH.
        3: {
          constructor; auto.
          apply RUN.
        }
        JMeq
        apply H1.
        eapply IHRUN in H1; eauto.
        punfold H1.
        red in H1.
        cbn.
        pose proof (IHRUN CIH m2).
        forward H0.
        admit.
        specialize (H0 H1 H).
        punfold H0.
      + pfold.
        red.
        cbn.
        pose proof (IHRUN CIH m2).
        forward H0.
        admit.
        specialize (H0 H1 H).
        punfold H0.

        red in H0.
        reflexivity.
        specialize (H0 H1 H).
        punfold H0.

Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree' t_bool2).
  split.
  { setoid_rewrite (itree_eta_ t_bool2).
    setoid_rewrite (itree_eta_ t_nat).
    setoid_rewrite (itree_eta_ t_nat) in REL.
    setoid_rewrite (itree_eta_ t_bool) in REL.
    setoid_rewrite (itree_eta_ t_bool) in RUN.
    setoid_rewrite (itree_eta_ t_bool2) in RUN.
    genobs t_bool otb.
    genobs t_bool2 otb2.
    genobs t_nat otn.
    clear t_nat Heqotn.
    clear t_bool Heqotb.
    clear t_bool2 Heqotb2.

    revert RUN.
    revert REL.

    revert otn otb otb2.
    pcofix CIH.
    intros t_nat t_bool t_bool2 REL RUN.
    punfold REL.
    red in REL.
    cbn in *.
    dependent induction REL.
    - (* Both t_nat and t_bool were ret nodes *)

(*          This means t_bool2 is either: *)

(*          - A ret node *)
(*          - Tau on the right *)
(*        *)
      rename H into NB.
      punfold RUN. red in RUN.
      dependent induction RUN; subst.
      + pfold. red. cbn in *.
        rewrite <- x.
        cbn.
        constructor.
        red in NB;
          destruct NB; destruct H; subst; auto.
      + (* t_bool2 is a Tau node... TauR in Run *)
        pfold. red. cbn in *.
        rewrite <- x.
        cbn.
        constructor; auto.
        pose proof (IHRUN CIH (observe t2) _ NB eq_refl eq_refl).
        punfold H.
    - (* Double tau *)

      (* Both t_nat and t_bool are Tau nodes... *)

(*          t_bool2 is either: *)

(*          - Tau *)
(*          - Anything (TauL) *)
(*          - A Tau because RUN was constructed with TauR *)
(*        *)
      rename H into REL'.

      punfold RUN. red in RUN.
      cbn in *.
      (* clear - CIH REL' RUN. *)
(*       genobs t_bool2 otb2. *)
(*       clear t_bool2 Heqotb2. *)
(*       dependent induction RUN; subst. *)
(*        *)

      clear - CIH REL' RUN.
      clear - RUN.
      pose proof RUN.
      dependent induction H.
      admit.
      admit.
      admit.
      admit.
      admit.
      + admit.
      +
          
      + (* Tau *)
        pstep.
        red.
        cbn. constructor; auto.
        right.
        pclearbot.
        specialize (CIH (observe m1) (observe m2) (observe t2)).
        repeat setoid_rewrite <- itree_eta_ in CIH.
        eauto.
      + (* TauL *)
        pstep.
        red.
        constructor; auto.
        specialize (IHRUN CIH _ REL').
        forward IHRUN.
        

        (* RUN : interp_PropTF nondetE_handle eq true true (upaco2 (interp_PropT_ nondetE_handle eq true true) bot2) (TauF m2) otb2 *)

        eapply IHRUN.
        -- apply CIH.
        -- (* IHRUN needs to know that (observe m2 ~= TauF ?m2 ) *)

(*               Why should this be the case at all? I had (TauF m2) on the left hand side... *)

(*               | Interp_PropT_TauL : forall (t1 : itree E R1) (t2 : itree' F R2), *)
(*                 is_true b1 -> interp_PropTF h_spec RR b1 b2 sim (observe t1) t2 -> interp_PropTF h_spec RR b1 b2 sim (TauF t1) t2 *)

              
(*             *)

        -- apply REL'.
        inversion Heqtm2; subst.
        eapply IHRUN in REL'; eauto.
        admit.
      + (* TauR *)
        eapply IHRUN in REL'; eauto.
        admit.
    - (* Double vis *)
  }
Abort.

Lemma main :
  forall t_nat t_bool,
    rutt (@top_level_rel) (@top_level_rel_ans) nb t_nat t_bool ->
    forall t_bool2, runBool t_bool t_bool2 ->
           exists t_nat2,
             runNat t_nat t_nat2 /\
               rutt (@event_rel') (@event_rel_ans') nb t_nat2 t_bool2.
Proof.
  intros t_nat t_bool REL t_bool2 RUN.

  (* Maybe if I generalize everything I can do case analysis on observed itrees *)
  setoid_rewrite (itree_eta_ t_bool2).
  setoid_rewrite (itree_eta_ t_bool2) in RUN.
  setoid_rewrite (itree_eta_ t_bool) in RUN.
  setoid_rewrite (itree_eta_ t_bool) in REL.
  setoid_rewrite (itree_eta_ t_nat) in REL.
  setoid_rewrite (itree_eta_ t_nat).

  genobs t_nat ot_nat.
  genobs t_bool ot_bool.
  genobs t_bool2 ot_bool2.

  clear t_nat Heqot_nat.
  clear t_bool Heqot_bool.
  clear t_bool2 Heqot_bool2.

  exists (get_nat_tree {| _observe := ot_nat |} {| _observe := ot_bool |} REL {| _observe := ot_bool2 |} RUN).

  split.
  {
    (* revert ot_nat ot_bool REL ot_bool2 RUN. *)
    (* intros ot_nat ot_bool REL ot_bool2 RUN. *)

    pcofix CIH.

    revert ot_nat ot_bool REL ot_bool2 RUN CIH.

    induction ot_nat, ot_bool;
      intros REL ot_bool2 RUN CIH.

    - 
    
    intros ot_nat ot_bool REL ot_bool2 RUN.
    

    pstep.
    red.
    cbn.

    
    pinversion RUN.

  }

  


  induction ot_nat.
  admit.
  admit.
  induction ot_nat, ot_bool; intros REL.
  - pinversion REL; subst.
    intros ot_bool2 RUN.
    punfold RUN.
    red in RUN.
    cbn in RUN.
    dependent induction RUN.
    + exists (ret r).
      split.
      -- pstep.
         constructor.
         reflexivity.
      -- pstep.
         constructor.
         auto.
    + specialize (IHRUN r0 REL H1).
      forward IHRUN; auto.
      destruct IHRUN as [t_nat2 [RUN2 REL2]].
      exists t_nat2.
      split; auto.

      pstep.
      red.
      cbn.
      constructor.
      punfold REL2.
  - pinversion REL.
    intros ot_bool2 RUN.
    punfold RUN.
    red in RUN.
    cbn in RUN.
    subst.
    dependent induction RUN.
    + pclearbot.
      exists (Ret r).
      split; auto.
      pstep. constructor. auto.

      pstep.
      red.
      cbn.
      constructor.
      punfold HS.
      red in HS.


exists (ret r).
      split.
      -- pstep.
         constructor.
         reflexivity.
      -- pstep.
         red.
         cbn.
         constructor.

         constructor.
         auto.      
    red in RUN.
    red in RUN.
    red in RUN.
    pinversion RUN; subst; cbn in *.
    

  intros ot_nat ot_bool REL.
  dependent induction REL.
  
  punfold REL.
  punfold RUN.
  red in RUN, REL.
  genobs
  red in RUN.
  red in RUN.
  red in RUN.

  exists (get_nat_tree t_nat t_bool REL t_bool2 RUN).
  split.
  { revert RUN RUN2 HeqRUN2.
    revert REL.
    revert t_nat t_bool t_bool2.
    pcofix CIH.
    intros t_nat t_bool t_bool2 REL RUN RUN2 HeqRUN2.
    subst.
    pattern RUN.
    pattern REL.

    refine (
        match RUN as RUN' return
                       paco2 (interp_PropT_ nondetE_handle eq true true) r t_nat
                       (get_nat_tree t_nat t_bool REL t_bool2 RUN)
with
        | _ => _
        end
      ).
    
    pattern RUN.


    clear RUN2 HeqRUN2.
    generalize RUN.
    apply interp_prop_inv_Type in RUN.

    pstep. red.
    destruct RUN.
    remember (observe (get_nat_tree t_nat t_bool REL t_bool2 RUN)) as t.
    induction t.
    - clear Heqt.
      exfalso.
      punfold REL.
      red in REL.

    
    remember (get_na
t_tree t_nat t_bool REL t_bool2 RUN) as t.
    destruct t.
    pstep. red.
    punfold RUN.
    remember 
    revert RUN HeqRUN2.
    
    punfold RUN2.
    pinversion RUN2.

    pinversion RUN.
    pinversion REL.

    (* Cannot seem to do anything with REL / RUN because they're used in the goal? *)
    Fail pdepdes REL.
    Fail punfold REL.
    Fail pinversion REL.
    Fail dependent destruction REL.
    Fail dependent inversion REL.
    Fail dependent induction REL.

    remember REL as REL2.
    assert (RUN2:=RUN).

    clear HeqREL2.
    red in REL.
    punfold REL.
    red in REL2.
    dependent destruction REL2; pclearbot.

    - pstep. red.
      rename H into NB.
      rename x0 into TNAT.
      rename x into TBOOL.

      (* Need to figure out what t_bool2 is *)
      punfold RUN2.
      red in RUN2.
      setoid_rewrite <- TBOOL in RUN2.
      inversion RUN2; subst.
      + (* Everything is a ret *)
        setoid_rewrite <- TNAT.

        (* I can't replace t_nat / t_bool / t_bool2 in this part of the goal:

           (observe (get_nat_tree t_nat t_bool REL t_bool2 RUN))

           because REL depends on t_nat and t_bool, and RUN depends on t_bool and t_bool2.
         *)
        setoid_rewrite (itree_eta_ t_nat). t_nat_eta        
        replace t_nat with ({| _observe := observe t_nat |}).

        unfold get_nat_tree.
      pinversion RUN2.

      setoid_rewrite <- H.
      red.

  }
Qed.

Lemma main' :
  forall t_nat t_bool,
    rutt (@top_level_rel) (@top_level_rel_ans) nb t_nat t_bool ->
    forall t_bool2, runBool t_bool t_bool2 ->
           exists t_nat2,
             runNat t_nat t_nat2 /\
               rutt (@event_rel') (@event_rel_ans') nb t_nat2 t_bool2.
Proof.
  intros t_nat t_bool REL t_bool2 RUN.
  exists (get_nat_tree' t_bool2).
  split.
  { revert RUN.
    revert REL.
    revert t_nat t_bool t_bool2.
    pcofix CIH.
    intros t_nat t_bool t_bool2 REL RUN.
    pinversion REL.
    - (* Both t_nat and t_bool were ret nodes

         This means t_bool2 is either:

         - A ret node
         - Tau on the right
      *)

      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).
      clear - H H1 RUN.
      genobs t_bool2 otb2.
      clear t_bool2 Heqotb2.
      dependent induction RUN; subst.
      + (* t_bool2 is ret *)
        pfold. red.
        setoid_rewrite <- H.
        cbn.

        constructor.

        red in H1.
        destruct H1; destruct H0; subst; auto.
      + (* t_bool2 is a Tau node... TauR in Run *)
        pfold.
        red.
        cbn.
        constructor; auto.
        pose proof (IHRUN r2).
        forward H0.
        reflexivity.
        specialize (H0 H1 H).
        punfold H0.
    - (* Double tau *)

      (* Both t_nat and t_bool are Tau nodes...

         t_bool2 is either:

         - Tau
         - Anything (TauL)
       *)

      
      punfold RUN. red in RUN.
      setoid_rewrite <- H0 in RUN.
      setoid_rewrite (itree_eta_ t_bool2).
      pstep. red.
      setoid_rewrite <- H.
      clear - CIH H1 RUN.
      genobs t_bool2 otb2.
      clear t_bool2 Heqotb2.
      dependent induction RUN; subst.
      + cbn. constructor; auto.
        right.
        pclearbot.
        eapply CIH; eauto.
      + eapply IHRUN in H1; eauto.
        punfold H1.
        red in H1.
        cbn.
        pose proof (IHRUN CIH m2).
        forward H0.
        admit.
        specialize (H0 H1 H).
        punfold H0.
      + pfold.
        red.
        cbn.
        pose proof (IHRUN CIH m2).
        forward H0.
        admit.
        specialize (H0 H1 H).
        punfold H0.

        red in H0.
        reflexivity.
        specialize (H0 H1 H).
        punfold H0.


pstep. red.
        cbn.
        setoid_rewrite <- H.
        constructor; auto.
        cbn.
        eapply IHRUN.
        pclearbot.
        eapply CIH; eauto.
  }
  
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
