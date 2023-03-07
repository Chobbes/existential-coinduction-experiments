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

Lemma get_nat_tree'_rutt :
  forall t,
    rutt (@event_rel') (@event_rel_ans') nb (get_nat_tree' t) t.
Proof.
  intros t.
  rewrite (itree_eta_ t).
  genobs t ot.
  clear t Heqot.
  revert ot.
  pcofix CIH.
  intros ot.

  induction ot.
  - (* Ret *)
    pstep; red; cbn.
    constructor.
    destruct r0; red; tauto.
  - (* Tau *)
    pstep; red; cbn.
    constructor.
    right.
    rewrite (itree_eta_ t).
    apply CIH.
  - (* Vis nodes *)
    destruct e.
    pstep; red; cbn.
    constructor.
    red. destruct b; red; tauto.

    intros a b0 H.
    cbn in H.
    destruct H.

    destruct H0 as [[A B0] | [A B0]]; subst; cbn.
    + right.
      rewrite (itree_eta_ (k _)).
      apply CIH.
    + right.
      rewrite (itree_eta_ (k _)).
      apply CIH.
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

      assert (DEC: (exists m3, ot_bool2 = TauF m3) \/ (forall m3, ot_bool2 <> TauF m3)).
      { destruct ot_bool2; eauto; right; red; intros; inversion H0. }

      destruct DEC as [EQ | EQ].
      { destruct EQ as [m3 EQ].
        subst.
        pstep; red; cbn.
        constructor.
        right.
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ m3).
        eapply CIH.

        pclearbot.
        punfold H; red in H.
        pstep. red. cbn.
        eauto.

        red.
        rewrite <- itree_eta_.
        rewrite <- itree_eta_.

        rewrite <- tau_eutt.
        rewrite <- (tau_eutt m3).
        pstep; red; cbn.
        auto.
      }

      inversion RUN; subst.
      + specialize (EQ t2).
        contradiction.
      + pstep; red; cbn.
        constructor; auto.

        rewrite (itree_eta_ m2) in H.
        rewrite (itree_eta_ m2) in RUN.
        genobs m2 om2.
        setoid_rewrite <- Heqom2 in HS.
        clear Heqom2.
        clear m2.
        induction HS; subst.
        -- inversion RUN; subst.
           cbn in *.
           inversion HS; subst.

           pclearbot.
           punfold H.
           red in H.

           { dependent induction H.
             - rewrite <- x.
               constructor.
               destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
             - rewrite <- x.
               constructor; auto.
           }
        -- specialize (EQ t2).
           contradiction.
        -- eapply IHHS; eauto.
           left.
           pclearbot.
           assert (rutt (@top_level_rel) (@top_level_rel_ans) nb  m1 (Tau t1)).
           { apply H.
           }
           setoid_rewrite tau_eutt in H0.
           rewrite <- itree_eta_.
           apply H0.
        -- specialize (EQ t2).
           contradiction.
        -- { dependent induction RUN; subst.
             - rewrite <- x in EQ.
               specialize (EQ t0).
               contradiction.
             - (* TauL *)
               clear IHRUN.
               pclearbot.

               apply rutt_inv_Vis_r in H.
               destruct H as [U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]].
               punfold M1.
               red in M1.
               genobs m1 om1.
               clear m1 Heqom1.
               dependent induction M1.
               + rename H1 into VIS_HANDLED.
                 destruct e, e1; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.

                   { (* Nondeterminism events *)
                     red in H0.
                     destruct H0.
                     - (* True *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK true).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
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
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT true true).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                         rewrite K0K3.
                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                     - (* False *)
                       subst.
                       setoid_rewrite bind_ret_l in VIS_HANDLED.

                       specialize (HK false).
                       forward HK. constructor; reflexivity.
                       pclearbot.
                       rewrite <- VIS_HANDLED in HK.

                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
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
                       rewrite (itree_eta_ (k0 _)).

                       eapply CIH.
                       + specialize (K_RUTT false false).
                         forward K_RUTT; cbn; auto.
                         pclearbot.
                         repeat rewrite <- itree_eta_.
                         assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                         rewrite K0K3.

                         punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                         pstep; red; cbn; eauto.
                       + repeat rewrite <- itree_eta_.
                         eapply HK.
                   }

                   { (* Regular events *)
                     destruct b.
                     red in H0.
                     rewrite H0 in VIS_HANDLED.

                     setoid_rewrite bind_trigger in VIS_HANDLED.
                     punfold VIS_HANDLED. red in VIS_HANDLED.
                     cbn in VIS_HANDLED.
                     dependent induction VIS_HANDLED.
                     { rewrite <- x.

                       eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                            get_nat_tree' (k2 (if Nat.eqb n0 0 then false else if Nat.eqb n0 1 then true else false)))).
                       2: {
                         red.
                         reflexivity.
                       }
                       2: {
                         cbn.
                         setoid_rewrite bind_trigger.
                         pstep; red; cbn.

                         destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
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
                               left.
                               setoid_rewrite K0K2.
                               assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                               reflexivity.
                               eauto.
                         - constructor.
                           intros v.
                           red.
                           specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                           red in REL0.
                           pclearbot.
                           assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                           { eapply REL0.
                           }

                           setoid_rewrite H0 in HK.

                           destruct v; [| destruct v]; cbn in *.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK false).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                             reflexivity.
                             eauto.
                           + repeat (rewrite <- itree_eta_).
                             specialize (HK true).
                             forward HK.
                             { eapply ReturnsVis.
                               unfold ITree.trigger.
                               reflexivity.
                               constructor. reflexivity.
                             }
                             pclearbot.
                             left.
                             setoid_rewrite K0K2.
                             assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                             reflexivity.
                             eauto.
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
                               left.
                               setoid_rewrite K0K2.
                               assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                               reflexivity.
                               eauto.
                       }

                       intros a RET.
                       specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       forward K_RUTT.
                       cbn; auto.

                       specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                       rewrite H0 in HK.
                       forward HK.
                       { eapply ReturnsVis.
                         unfold ITree.trigger.
                         reflexivity.
                         cbn.
                         constructor.
                         reflexivity.
                       }

                       right.
                       rewrite (itree_eta_ (k0 a)).
                       rewrite (itree_eta_ (k2 _)).
                       pclearbot.
                       eapply CIH;
                         repeat rewrite <- itree_eta_.

                       repeat rewrite <- itree_eta_.
                       assert (k0 a ≈ k3 a) as K0K3 by apply REL.
                       rewrite K0K3.
                       eapply K_RUTT.
                       red.
                       eapply HK.
                     }

                     { rewrite <- x in EQ.
                       specialize (EQ t1).
                       contradiction.
                     }
                   }
               + constructor; auto.
                 eapply IHM1; eauto.
             - rewrite <- x in EQ.
               exfalso.
               eapply EQ; eauto.
           }
      + pstep; red; cbn.
        constructor.
        right.
        rewrite (itree_eta_ m1).
        rewrite (itree_eta_ t2).

        pclearbot.
        eapply CIH; repeat rewrite <- itree_eta_.
        eauto.

        red.
        rewrite <- (tau_eutt m2).

        pstep; red; cbn.
        auto.
    - rename H into EV_REL.
      destruct e1, e2; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.
      rename H0 into K_RUTT.
      subst.

      + (* NonDet events *)
        punfold RUN. red in RUN.
        cbn in RUN.
        dependent induction RUN.
        -- pstep; red; cbn.
           constructor; auto.
           rewrite (itree_eta_ t2).

           forward IHRUN; auto.
           specialize (IHRUN k2).
           forward IHRUN; auto.
           forward IHRUN; auto.
           punfold IHRUN.
        --
          red in H.
          { destruct H; subst; setoid_rewrite bind_ret_l in H0.
            - pstep; red; cbn.

              eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
              2: {
                left. reflexivity.
              }
              2: {
                setoid_rewrite bind_ret_l.
                reflexivity.
              }

              intros a RET.
              eapply Returns_Ret_ in RET; [| reflexivity]; subst.
              right.

              rewrite (itree_eta_ (k1 true)).
              eapply CIH; repeat rewrite <- itree_eta_.
              + specialize (K_RUTT true true).
                forward K_RUTT; cbn; auto.
                pclearbot.
                apply K_RUTT.
              + rewrite H0.
                specialize (HK true).
                forward HK.
                constructor; reflexivity.
                pclearbot.
                apply HK.
            - pstep; red; cbn.

              eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
              2: {
                right. reflexivity.
              }
              2: {
                setoid_rewrite bind_ret_l.
                reflexivity.
              }

              intros a RET.
              eapply Returns_Ret_ in RET; [| reflexivity]; subst.
              right.

              rewrite (itree_eta_ (k1 false)).
              eapply CIH; repeat rewrite <- itree_eta_.
              + specialize (K_RUTT false false).
                forward K_RUTT; cbn; auto.
                pclearbot.
                apply K_RUTT.
              + rewrite H0.
                specialize (HK false).
                forward HK.
                constructor; reflexivity.
                pclearbot.
                apply HK.
          }
      + { (* Regular events *)
          destruct b.
          rename EV_REL into NB.
          subst.
          punfold RUN. red in RUN. cbn in RUN.

          dependent induction RUN.
          - pstep; red; cbn.
            constructor; auto.

            forward IHRUN; auto.
            specialize (IHRUN _ k2 NB).
            forward IHRUN; auto.
            forward IHRUN; auto.
            punfold IHRUN.
          - red in H.
            rewrite H in H1.
            rename H0 into K_RUTT.

            setoid_rewrite bind_trigger in H1.
            punfold H1; red in H1; cbn in H1.
            dependent induction H1.
            { rewrite <- x.
              pstep; red; cbn.
              assert ((VisF (nat_ev (if b then 1 else 0))
                         (fun n0 : nat =>
                            get_nat_tree'
                              (if Nat.eqb n0 0
                               then k0 false
                               else if Nat.eqb n0 1 then k0 true else k0 false))) = observe (Vis (nat_ev (if b then 1 else 0))
                                                                                               (fun n0 : nat =>
                                                                                                  get_nat_tree'
                                                                                                    (if Nat.eqb n0 0
                                                                                                     then k0 false
                                                                                                     else if Nat.eqb n0 1 then k0 true else k0 false)))) as VIS by auto.

              rewrite VIS.
              clear VIS.
              { eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                     get_nat_tree'
                                                       (if Nat.eqb n0 0
                                                        then k0 false
                                                        else if Nat.eqb n0 1 then k0 true else k0 false))).
                2: {
                  red.
                  reflexivity.
                }
                2: {
                  setoid_rewrite bind_trigger.
                  destruct NB as [[R1 R3] | [R1 R3]]; subst; auto;
                    reflexivity.
                }

                intros a RET.
                right.
                rewrite (itree_eta_ (k1 _)).
                rewrite (itree_eta_ (if Nat.eqb a 0 then _ else _)).
                eapply CIH; repeat rewrite <- itree_eta_.

                specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                forward K_RUTT; cbn; auto.
                pclearbot.
                apply K_RUTT.

                setoid_rewrite H in HK.
                specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).

                destruct a; [| destruct a]; cbn in *.
                - forward HK.
                  { eapply ReturnsVis.
                    unfold ITree.trigger.
                    reflexivity.
                    constructor. reflexivity.
                  }
                  pclearbot.
                  assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                  rewrite K0K3.
                  eapply HK.
                - repeat (rewrite <- itree_eta_).
                  forward HK.
                  { eapply ReturnsVis.
                    unfold ITree.trigger.
                    reflexivity.
                    constructor. reflexivity.
                  }
                  pclearbot.
                  assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                  setoid_rewrite K0K3.
                  eapply HK.
                - (* Bogus case *)
                  repeat (rewrite <- itree_eta_).
                  forward HK.
                  { eapply ReturnsVis.
                    unfold ITree.trigger.
                    reflexivity.
                    constructor. reflexivity.
                  }
                  pclearbot.
                  assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                  setoid_rewrite K0K3.
                  eapply HK.
              }
            }

            { rewrite <- x.
              pstep; red; cbn.
              constructor; auto.

              specialize (IHeqitF b k3 t1 HK H eq_refl eq_refl).
              forward IHeqitF; auto.
              forward IHeqitF; auto.
              forward IHeqitF; auto.

              punfold IHeqitF.
            }
        }
    - pstep; red; cbn.
      constructor; auto.
      forward IHREL; auto.
      forward IHREL; auto.

      punfold IHREL.
    - eapply IHREL; eauto.
      red in RUN.
      setoid_rewrite tau_eutt in RUN.
      rewrite <- itree_eta_.
      apply RUN.
  }

  { apply get_nat_tree'_rutt.
  }
Qed.
