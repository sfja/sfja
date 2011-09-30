(** * Gen: Generalizing Induction Hypotheses *)

(* $Date: 2011-06-07 16:49:17 -0400 (Tue, 07 Jun 2011) $ *)

Require Export Poly_J.

(** In the previous chapter, we saw a proof that the [double] function
    is injective.  The way we _start_ this proof is a little bit
    delicate: if we begin it with
[[
      intros n. induction n.
]]
    all is well.  But if we begin it with
[[
      intros n m. induction n.
]]
    we get stuck in the middle of the inductive case... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
      (* Here we are stuck.  We need the assertion in order to
         rewrite the final goal (subgoal 2 at this point) to an
         identity.  But the induction hypothesis, [IHn'], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the assertion is not provable. *)
      Admitted.

(** What went wrong here?

    The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context
    -- intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _this particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]")

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we can prove

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.)

    To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)

(** The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective' : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for *every* [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O". inversion eq.  (* The 0 case is trivial *)
    SCase "m = S m'".
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity.  Qed.

(** So what we've learned is that we need to be careful about
    using induction to try to prove something too specific: If
    we're proving a property of [n] and [m] by induction on [n],
    we may need to leave [m] generic.

    However, this strategy doesn't always apply directly;
    sometimes a little rearrangement is needed.  Suppose, for
    example, that we had decided we wanted to prove
    [double_injective] by induction on [m] instead of [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        (* Here we are stuck again, just like before. *)
Admitted.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)  What can we do about this?

    One possibility is to rewrite the statement of the lemma so
    that [m] is quantified before [n].  This will work, but it's
    not nice: We don't want to have to mangle the statements of
    lemmas to fit the needs of a particular strategy for proving
    them -- we want to state them in the most clear and natural
    way.

    What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".
      assert (n' = m') as H.
      SSCase "Proof of assertion".
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity.  Qed.

(** Let's look at an informal proof of this theorem.  Note that the
    proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - First, suppose [m = 0], and suppose [n] is a number such
    that [double n = double m].  We must show that [n = 0].

    Since [m = 0], by the definition of [double] we have [double n =
    0].  There are two cases to consider for [n].  If [n = 0] we are
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].

    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by inversion that [double n' = double
    m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)

(** **** Exercise: 3 stars (gen_dep_practice) *)
(** Carry out this proof by induction on [m]. *)

Theorem plus_n_n_injective_take2 : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (index_after_last_informal) *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:

     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index (S n) l = None].

     _Proof_:
     (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (gen_dep_practice_opt) *)
(** Prove this by induction on [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (app_length_cons) *)
(** Prove this by induction on [l1], without using [app_length]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (app_length_twice) *)
(** Prove this by induction on [l], without using app_length. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
