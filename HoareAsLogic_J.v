(** * HoareAsLogic: Hoare Logic as a Logic *)

(* $Date: 2011-04-16 14:56:54 -0400 (Sat, 16 Apr 2011) $ *)

Require Export Hoare_J.

(** The presentation of Hoare logic in [Hoare.v] could be described as
    "model-theoretic": the proof rules for each of the constructors
    were presented as _theorems_ about the evaluation behavior of
    programs, and proofs of program correctness (validity of Hoare
    triples) were constructed by combining these theorems directly in
    Coq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic. *)

Inductive hoare_proof : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      hoare_proof P (SKIP) P
  | H_Asgn : forall Q V a,
      hoare_proof (assn_sub V a Q) (V ::= a) Q
  | H_Seq  : forall P c Q d R,
      hoare_proof P c Q -> hoare_proof Q d R -> hoare_proof P (c;d) R
  | H_If : forall P Q b c1 c2,
    hoare_proof (fun st => P st /\ bassn b st) c1 Q ->
    hoare_proof (fun st => P st /\ ~(bassn b st)) c2 Q ->
    hoare_proof P (IFB b THEN c1 ELSE c2 FI) Q
  | H_While : forall P b c,
    hoare_proof (fun st => P st /\ bassn b st) c P ->
    hoare_proof P (WHILE b DO c END) (fun st => P st /\ ~ (bassn b st))
  | H_Consequence  : forall (P Q P' Q' : Assertion) c,
    hoare_proof P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q
  | H_Consequence_pre  : forall (P Q P' : Assertion) c,
    hoare_proof P' c Q ->
    (forall st, P st -> P' st) ->
    hoare_proof P c Q
  | H_Consequence_post  : forall (P Q Q' : Assertion) c,
    hoare_proof P c Q' ->
    (forall st, Q' st -> Q st) ->
    hoare_proof P c Q.

Tactic Notation "hoare_proof_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "H_Skip" | Case_aux c "H_Asgn" | Case_aux c "H_Seq"
  | Case_aux c "H_If" | Case_aux c "H_While" | Case_aux c "H_Consequence"
  | Case_aux c "H_Consequence_pre" | Case_aux c "H_Consequence_post" ].

(** For example, let's construct a proof object representing a
    derivation for the hoare triple
[[
      {{assn_sub X (X+1) (assn_sub X (X+2) (X=3))}} X::=X+1; X::=X+2 {{X=3}}.
]]
    We can use Coq's tactics to help us construct the proof object. *)

Example sample_proof
             : hoare_proof
                 (assn_sub X (APlus (AId X) (ANum 1))
                   (assn_sub X (APlus (AId X) (ANum 2))
                     (fun st => st X = VNat 3) ))
                 (X ::= APlus (AId X) (ANum 1); (X ::= APlus (AId X) (ANum 2)))
                 (fun st => st X = VNat 3).
Proof.
  apply H_Seq with (assn_sub X (APlus (AId X) (ANum 2))
                     (fun st => st X = VNat 3)).
  apply H_Asgn. apply H_Asgn.
Qed.

(*
Print sample_proof.
====>
  H_Seq
    (assn_sub X (APlus (AId X) (ANum 1))
       (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3)))
    (X ::= APlus (AId X) (ANum 1))
    (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3))
    (X ::= APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3)
    (H_Asgn
       (assn_sub X (APlus (AId X) (ANum 2)) (fun st : state => st X = VNat 3))
       X (APlus (AId X) (ANum 1)))
    (H_Asgn (fun st : state => st X = VNat 3) X (APlus (AId X) (ANum 2)))
*)

(** **** Exercise: 2 stars *)
(** Prove that such proof objects represent true claims. *)

Theorem hoare_proof_sound : forall P c Q,
  hoare_proof P c Q -> {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also use Coq's reasoning facilities to prove metatheorems
    about Hoare Logic.  For example, here are the analogs of two
    theorems we saw in [Hoare.v] -- this time expressed in terms of
    the syntax of Hoare Logic derivations (provability) rather than
    directly in terms of the semantics of Hoare triples.

    The first one says that, for every [P] and [c], the assertion
    [{{P}} c {{True}}] is _provable_ in Hoare Logic.  Note that the
    proof is more complex than the semantic proof in [Hoare.v]: we
    actually need to perform an induction over the structure of the
    command [c]. *)

Theorem H_Post_True_deriv:
  forall c P, hoare_proof P c (fun _ => True).
Proof.
  intro c.
  com_cases (induction c) Case; intro P.
  Case "SKIP".
    eapply H_Consequence_pre.
    apply H_Skip.
    (* Proof of True *)
    intros. apply I.
  Case "::=".
    eapply H_Consequence_pre.
    apply H_Asgn.
    intros. apply I.
  Case ";".
    eapply H_Consequence_pre.
    eapply H_Seq.
    apply (IHc1 (fun _ => True)).
    apply IHc2.
    intros. apply I.
  Case "IFB".
    apply H_Consequence_pre with (fun _ => True).
    apply H_If.
    apply IHc1.
    apply IHc2.
    intros. apply I.
  Case "WHILE".
    eapply H_Consequence.
    eapply H_While.
    eapply IHc.
    intros; apply I.
    intros; apply I.
Qed.

(** Similarly, we can show that [{{False}} c {{Q}}] is provable for
    any [c] and [Q]. *)

Lemma False_and_P_imp: forall P Q,
  False /\ P -> Q.
Proof.
  intros P Q [CONTRA HP].
  destruct CONTRA.
Qed.

Tactic Notation "pre_false_helper" constr(CONSTR) :=
  eapply H_Consequence_pre;
    [eapply CONSTR | intros ? CONTRA; destruct CONTRA].

Theorem H_Pre_False_deriv:
  forall c Q, hoare_proof (fun _ => False) c Q.
Proof.
  intros c.
  com_cases (induction c) Case; intro Q.
  Case "SKIP". pre_false_helper H_Skip.
  Case "::=". pre_false_helper H_Asgn.
  Case ";". pre_false_helper H_Seq. apply IHc1. apply IHc2.
  Case "IFB".
    apply H_If; eapply H_Consequence_pre.
    apply IHc1. intro. eapply False_and_P_imp.
    apply IHc2. intro. eapply False_and_P_imp.
  Case "WHILE".
    eapply H_Consequence_post.
    eapply H_While.
    eapply H_Consequence_pre.
      apply IHc.
      intro. eapply False_and_P_imp.
    intro. simpl. eapply False_and_P_imp.
Qed.

(** This style of presentation gives a clearer picture of what it
    means to "give a proof in Hoare logic."  However, it is not
    entirely satisfactory from the point of view of writing down such
    proofs in practice: it is quite verbose.  The section of [Hoare.v]
    on formalizing decorated programs shows how we can do even
    better. *)
