Require Coq.Lists.List.
Require Coq.Vectors.Vector.

Module Type VarSig.
    Parameter variable : Set.
    Axiom variables_dec : forall x y : variable, {x = y} + {x <> y}.
End VarSig.

Module Type Sig.
    Parameter pred_symb : nat -> Set.
    Parameter func_symb : nat -> Set.
    Axiom pred_dec : forall (n : nat)(x y : pred_symb n), {x = y} + {x <> y}.
    Axiom func_dec : forall (n : nat)(x y : func_symb n), {x = y} + {x <> y}.
End Sig.

Module Predicative (vars : VarSig)(symbs : Sig).
Import Coq.Vectors.Vector.
Import Coq.Lists.List.
Import ListNotations.
Import vars.
Import symbs.

Inductive term : Set :=
  | var : variable -> term
  | func {n : nat} : func_symb n -> t term n -> term.

Inductive formula : Set :=
  | predf {n : nat} : pred_symb n -> t term n -> formula
  | eqf : term -> term -> formula
  | negf : formula -> formula
  | implf : formula -> formula -> formula
  | forallf : variable -> formula -> formula.

Notation "' v" := (var v)
  (at level 10, no associativity).

Notation "f ` a b .. c" := (func f (a :: (b :: ( .. ( c :: [] ) .. ))))
  (at level 25, no associativity).

Notation "P ! a b .. c" := (predf P (a :: (b :: ( .. ( c :: [] ) .. ))))
  (at level 70, right associativity).

Notation "x == y" := (eqf x y)
  (at level 70, no associativity).

Notation "¬ P" := (negf P)
  (at level 75, right associativity).

Notation "P --> Q" := (implf P Q)
  (at level 90, right associativity).

Inductive Proves : list formula -> formula -> Prop :=
  | from_premise : forall (prem : list formula) (stmt : formula),
      (In stmt prem -> Proves prem stmt)
  | modus_ponens : forall (P Q : formula) (prem : list formula),
      (Proves prem P) -> (Proves prem (P --> Q)) ->
      (Proves prem Q)
  | universal_generalization : forall (P : formula) (v : variable) (prem : list formula),
      (Proves prem P) -> (Proves prem (forallf v P)).

Notation " Gamma |-0 P " := (Proves Gamma P)
  (at level 95, no associativity).

Example seq_id : forall P : formula, [P] |-0 P.
Proof.
  intros. apply from_premise. simpl. left. reflexivity.
Qed.

Lemma weaken : forall (prem prem' : list formula) (P : formula),
  incl prem prem' -> prem |-0 P -> prem' |-0 P.
Proof.
  intros. induction H0.
  - apply from_premise. apply H. assumption.
  - apply modus_ponens with P.
    + apply IHProves1. assumption.
    + apply IHProves2. assumption.
  - apply universal_generalization.
    + apply IHProves. assumption.
Qed.

Inductive FreeInTerm (v : variable) : term -> Prop :=
  | varft : FreeInTerm v (var v)
  | funcft {n : nat} (f : func_symb n) (ts : t term n) :
         FreeInTerms v ts
      -> FreeInTerm v (func f ts)
  with FreeInTerms (v : variable) : forall {n : nat}, t term n -> Prop := 
  | herefts {n : nat} (tm : term) (ts : t term n) :
        FreeInTerm v tm
      -> FreeInTerms v (Vector.cons _ tm _ ts)
  | consfts {n : nat} (tm : term) (ts : t term n) :
         FreeInTerms v ts
      -> FreeInTerms v (Vector.cons _ tm _ ts).

Inductive FreeInFormula (v : variable) : formula -> Prop :=
  | predff {n : nat} (P : pred_symb n) (ts : t term n) :
      FreeInTerms v ts -> FreeInFormula v (predf P ts)
  | eqff_left (t1 t2 : term) : FreeInTerm v t1 -> FreeInFormula v (t1 == t2)
  | eqff_right (t1 t2 : term) : FreeInTerm v t2 -> FreeInFormula v (t1 == t2)
  | negff (F : formula) : FreeInFormula v F -> FreeInFormula v (¬ F)
  | implff_left (P Q : formula) : FreeInFormula v P -> FreeInFormula v (P --> Q)
  | implff_right (P Q : formula) : FreeInFormula v Q -> FreeInFormula v (P --> Q)
  | forallff (w : variable) (P : formula) : v <> w -> FreeInFormula v P -> FreeInFormula v (forallf w P).

Notation closed P := (forall v : variable, ~ FreeInFormula v P).

Fixpoint subst_term (v : variable) (x : term) (tm : term) : term :=
  match tm with
  | var w => match variables_dec v w with
             | left _ => x
             | right _ => tm
             end
  | func f xs => func f (Vector.map (subst_term v x) xs)
  end.

Fixpoint subst_formula (v : variable) (x : term) (f : formula) : formula :=
  match f with
  | predf P tms => predf P (Vector.map (subst_term v x) tms)
  | eqf t1 t2 => eqf (subst_term v x t1) (subst_term v x t2)
  | negf f' => negf (subst_formula v x f')
  | implf P Q => implf (subst_formula v x P) (subst_formula v x Q)
  | forallf w P => match (variables_dec v w) with
                   | left _ => forallf w P
                   | right _ => forallf w (subst_formula v x P)
                   end
  end.

Notation "tm t[[ x // v ]]" := (subst_term v x tm)
  (at level 24, left associativity).

Notation "f f[[ x // v ]]" := (subst_formula v x f)
  (at level 65, left associativity).

Inductive FreeFor (v : variable) (x : term) : formula -> Prop :=
  | predfff {n : nat} (P : pred_symb n) (ts : t term n) :
      FreeFor v x (predf P ts)
  | eqfff (t1 t2 : term) : FreeFor v x (eqf t1 t2)
  | negfff (P : formula) : FreeFor v x P -> FreeFor v x (¬ P)
  | implfff (P Q : formula) : FreeFor v x P -> FreeFor v x Q -> FreeFor v x (P --> Q)
  | forallfff_not_occur (w : variable) (P : formula) :
      ~ (FreeInFormula v P) -> FreeFor v x (forallf w P)
  | forallfff_free (w : variable) (P : formula) :
      ~ (FreeInTerm w x) -> FreeFor v x P -> FreeFor v x (forallf w P).

Inductive ClassicalAxiom : formula -> Prop :=
  | axiomK : forall (P Q : formula), ClassicalAxiom (P --> Q --> P)
  | axiomS : forall (P Q R : formula),
      ClassicalAxiom ((P --> Q --> R) --> (P --> Q) --> (P --> R))
  | contraposition : forall (P Q : formula),
      ClassicalAxiom ((¬ P --> ¬ Q) --> (Q --> P))
  | universal_instantiation : forall (v : variable) (P : formula) (a : term),
      FreeFor v a P -> ClassicalAxiom ((forallf v P) --> P f[[ a // v ]])
  | universal_implication : forall (v : variable) (P Q : formula),
      ~ (FreeInFormula v P) -> ClassicalAxiom ((forallf v (P --> Q)) --> P --> forallf v Q).

Notation ClassicalAxioms ax := (forall F : formula, In F ax -> ClassicalAxiom F).

Definition ProvesClassically (prems : list formula) (concl : formula) :=
  exists ax : list formula, (forall F : formula, In F ax -> ClassicalAxiom F) /\
    (prems ++ ax |-0 concl).

Notation "G |-c concl" := (ProvesClassically G concl)
  (at level 95, no associativity).

Module ListManipulationTactics.
  Lemma nil_incl : forall {A : Set} (G : list A),
    incl [] G.
  Proof. intros A G a H. inversion H. Qed.

  Lemma app_incl : forall {A : Set} (l m n : list A),
    incl (l ++ m) n -> incl l n /\ incl m n.
  Proof.
    intros.
    assert (incl l (l++m)) by (apply incl_appl; apply incl_refl).
    assert (incl m (l++m)) by (apply incl_appr; apply incl_refl).
    split; apply incl_tran with (l++m); assumption; assumption.
  Qed.

  Lemma singleton : forall {A : Set} (l : list A) (a : A),
    [a] ++ l = a :: l.
  Proof. reflexivity. Qed.

  Ltac auto_in := progress repeat (
    repeat ( (* break the goal *)
      try assumption;
      match goal with
      | |- In ?A (?B ++ ?C) =>
        apply in_or_app;
        (try (left; auto_in));
        (right; auto_in)
      | |- In ?A (?B :: ?C) =>
        (try (left; reflexivity));
        (right; auto_in)
      end
    );
    repeat ( (* break the premises *)
      match goal with
      | H : In ?A (?B ++ ?C) |- _ =>
        destruct (in_app_or _ _ _ H); clear H
      | H : In ?A (?B :: ?C) |- _ =>
        let E := fresh H in
        let H' := fresh H in
          destruct (in_inv _ _ _ H) as [E | H']; [rewrite E | idtac]; clear H
      end
    )
  ).

  Ltac _search_for_incl := progress (
    repeat ( (* search for a solution *)
      try apply incl_refl; try assumption;
      match goal with
      | |- incl ?A (?B ++ ?C) =>
        (try (apply incl_appl; _search_for_incl));
        (apply incl_appr; _search_for_incl)
      | |- incl [?A] ?B => auto_in
      | |- incl [] _ => (apply nil_incl)
      end
    )
  ).
  (* Automatically solves problems of the form
   * A1 ++ A2 ++ a :: A3 `incl` B1 ++ a :: B2 ++ B3 ++ A2 etc. *)
  Ltac auto_incl := progress (
    repeat ( (* Destruct all the relevant premises *)
      match goal with
      | H : incl (?A ++ ?B) ?C |- _ =>
        destruct (app_incl A B C H); clear H
      | H : incl (?A :: nil) ?C |- _ => auto_in
      | H : incl (?A :: ?B) ?C |- _ =>
        let H0 := fresh H in
          assert (H0 : incl ([A] ++ B) C) by (simpl; assumption);
          destruct (app_incl [A] B C H0); clear H; clear H0
      end
    );
    repeat ( (* split *)
      match goal with
      | |- incl (?A ++ ?B) ?C => apply incl_app
      | |- incl (?A :: nil) ?C => 
        auto_in (* todo : use auto_in *)
      | |- incl (?A :: ?B) ?C =>
        rewrite <- singleton; apply incl_app
      end
    );
    _search_for_incl
  ).

  Lemma classical_nil : ClassicalAxioms [].
  Proof.
    intros. inversion H.
  Qed.

  Lemma classical_app : forall (G H : list formula),
    ClassicalAxioms G -> ClassicalAxioms H -> ClassicalAxioms (G ++ H).
  Proof.
    intros. rewrite in_app_iff in H2. destruct H2.
    apply H0. assumption. apply H1. assumption.
  Qed.

  Lemma classical_singleton : forall (P : formula)(G : list formula),
    ClassicalAxiom P -> ClassicalAxioms G -> ClassicalAxioms (P :: G).
  Proof.
    intros. inversion H1.
    rewrite <- H2. assumption.
    apply H0. assumption.
  Qed.

  Ltac auto_classical := repeat (
    try assumption;
    match goal with
    | |- ClassicalAxiom _ => constructor
    | |- ClassicalAxioms [] => apply classical_nil
    | |- ClassicalAxioms (?A :: ?G) => apply (classical_singleton A G)
    | |- ClassicalAxioms (?A ++ ?B) => apply (classical_app A B)
    end
  ).

End ListManipulationTactics.

Import ListManipulationTactics.

Theorem weaken_c : forall (G H : list formula) (P : formula),
  incl G H -> G |-c P -> H |-c P.
Proof.
  unfold ProvesClassically; intros G H P Hincl HGP.
  destruct HGP as  [axG [axGc HseqG] ].
  exists axG. split.
  auto_classical.
  apply weaken with (G ++ axG).
  auto_incl.
  assumption.
Qed.

(* We lift the inference rules to classical entailment *)

Lemma from_premise_c : forall (prem : list formula) (stmt : formula),
  (In stmt prem -> prem |-c stmt).
Proof.
  intros. exists [].
  split. auto_classical.
  apply from_premise.
  auto_in.
Qed.

Lemma modus_ponens_c : forall (prem : list formula) (P Q : formula),
  prem |-c P -> prem |-c (P --> Q) ->
  prem |-c Q.
Proof.
  unfold ProvesClassically. intros prem P Q HP HPQ.
  destruct HP as [axHP [axHPc HPseq] ].
  destruct HPQ as [axHPQ [axHPQc HPQseq] ].
  exists (axHP ++ axHPQ). split.
  - auto_classical.
  - apply modus_ponens with P.
    apply weaken with (prem ++ axHP).
    auto_incl.
    assumption.
    apply weaken with (prem ++ axHPQ).
    auto_incl.
    assumption.
Qed.

Lemma universal_generalization_c : forall (P : formula) (v : variable) (prem : list formula),
  (prem |-c P) -> (prem |-c (forallf v P)).
Proof.
  intros P v prem H.
  destruct H as [ Hax [ Haxc Hseq ] ].
  exists Hax. split.
  assumption.
  apply universal_generalization. assumption.
Qed.

Lemma from_axiom_c : forall (G : list formula) (P : formula),
  (ClassicalAxiom P) -> G |-c P.
Proof.
  intros. exists [P]. split.
  auto_classical.
  apply from_premise.
  auto_in.
Qed.

Theorem id_impl : forall (A : formula), [] |-c A --> A.
Proof.
  intros.
  exists [
        (A --> A --> A) ;
        (A --> (A --> A) --> A);
        ((A --> ((A --> A) --> A)) --> ((A --> (A --> A)) --> (A --> A)))
  ]. split.
  - auto_classical.
  - simpl. apply modus_ponens with (A --> A --> A).
    apply from_premise. auto_in.
    apply modus_ponens with (A --> (A --> A) --> A).
    apply from_premise. auto_in.
    apply from_premise. auto_in.
Qed.

Lemma from_axiom_d : forall (G : list formula) (P : formula) (A : formula),
  (ClassicalAxiom A) -> G |-c P --> A.
Proof.
  intros.
  apply modus_ponens_c with A.
  apply from_axiom_c. assumption.
  apply from_axiom_c. constructor.
Qed.

Lemma from_premise_d : forall (G : list formula) (P : formula) (A : formula),
  (In A G) -> G |-c P --> A.
Proof.
  intros.
  apply modus_ponens_c with A.
  apply from_premise_c. auto_in.
  apply from_axiom_c. constructor.
Qed.

Lemma modus_ponens_d : forall (G : list formula) (P : formula) (A B : formula),
  G |-c P --> A -> G |-c P --> A --> B ->
  G |-c P --> B.
Proof.
  intros. apply modus_ponens_c with (P --> A).
  assumption. apply modus_ponens_c with (P --> A --> B).
  assumption. apply from_axiom_c. constructor.
Qed.

Lemma universal_generalization_d : forall (G : list formula) (P : formula) (v : variable) (A : formula),
  (~ FreeInFormula v P) -> (G |-c P --> A) -> (G |-c P --> (forallf v A)).
Proof.
  intros.
  apply modus_ponens_c with (forallf v (P --> A)).
  apply universal_generalization_c. assumption.
  apply from_axiom_c. apply universal_implication. assumption.
Qed.

Theorem deduction : forall (P Q : formula) (G : list formula),
     closed P
  -> P :: G |-c Q -> G |-c P --> Q.
Proof.
  intros P Q G HClosed Hseq. (* Let's find out how Hseq is proved *)
  destruct Hseq as [Hseqax [Hax Hseqproof] ].
  simpl in Hseqproof. remember (P :: G ++ Hseqax) as prem.
  induction Hseqproof.
  - (* By premise or axiom, we find out which *)
    rewrite Heqprem in H. inversion H.
    (* it is by P itself *)
    rewrite H0. apply weaken_c with []. auto_incl. apply id_impl.
    (* It is either by some other premise or axiom *)
    clear H.
    rewrite in_app_iff in H0. destruct H0.
    (* It is by premise, we use axiom K *)
    apply from_premise_d. assumption.
    (* It is by axiom, we also use axiom K *)
    apply from_axiom_d. apply Hax. assumption.
  - (* by modus ponens, we use axiom S *)
    apply modus_ponens_d with P0.
    apply IHHseqproof1. assumption.
    apply IHHseqproof2. assumption.
  - (* by universal generalization, we use the quantifier axiom *)
    apply universal_generalization_d.
    apply HClosed. apply IHHseqproof. assumption.
Qed.

(* We introduce more connectives *)
Declare Scope predicative_calculus_scope.
Delimit Scope predicative_calculus_scope with predicative.
Open Scope predicative_calculus_scope.
Module PredicativeCalculusNotations.
Definition orf P Q := ¬ P --> Q.
Notation "P ||| Q" := (orf P Q)
  (at level 85, right associativity) : predicative_calculus_scope.

Definition andf P Q := ¬ (P --> ¬ Q).
Notation "P &&& Q" := (andf P Q)
  (at level 80, right associativity) : predicative_calculus_scope.

Definition equivf P Q := ((P --> Q) ||| (Q --> P)).
Notation "P === Q" := (equivf P Q)
  (at level 94, no associativity).

End PredicativeCalculusNotations.

Import PredicativeCalculusNotations.

(* Some theorems *)
Theorem hypothetical_syllogism : forall (P Q R : formula),
  [P --> Q ; Q --> R] |-c (P --> R).
Proof.
  intros.
  apply modus_ponens_c with (P --> Q).
  apply from_premise_c. left. reflexivity.
  apply modus_ponens_c with (P --> Q --> R).
  apply modus_ponens_c with (Q --> R).
  apply from_premise_c. right. left. reflexivity.
  apply from_axiom_c. constructor.
  apply from_axiom_c. constructor.
Qed.

Lemma contraposition_c : forall (G : list formula)(P Q : formula),
  G |-c (¬P --> ¬Q) -> G |-c (Q --> P).
Proof.
  intros.
  apply modus_ponens_c with (¬ P --> ¬ Q).
  assumption. apply from_axiom_c. constructor.
Qed.

Lemma contraposition_d : forall (G : list formula)(P A B : formula),
  G |-c P --> ¬A --> ¬B -> G |-c P --> B --> A.
Proof.
  intros.
  apply modus_ponens_d with (¬A --> ¬B).
  assumption. apply from_axiom_d. constructor.
Qed.

Theorem double_negation_elimination_seq : forall (P : formula),
  [¬¬ P] |-c P.
Proof.
  intros.
  apply modus_ponens_c with (¬¬P).
  apply from_premise_c. auto_in.
  apply contraposition_c. apply contraposition_c.
  apply modus_ponens_c with (¬¬P).
  apply from_premise_c. auto_in.
  apply from_axiom_c. constructor.
Qed.

Theorem double_negation_elimination : forall (P : formula),
  [] |-c (¬¬P --> P).
Proof.
  intros.
  apply modus_ponens_d with (¬¬P).
  apply id_impl.
  apply contraposition_d. apply contraposition_d.
  apply modus_ponens_d with (¬¬P).
  apply id_impl.
  apply from_axiom_d. constructor.
Qed.

(* See how that closely imitates the former version
 * the only difference is the from_premise part,
 * since the premise is the precedent formula,
 * it needs special translation. otherwise the two
 * proofs are completely the same. *)

(* TODO : more about other parts of the logic *)
