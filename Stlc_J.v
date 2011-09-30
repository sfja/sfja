(** * Stlc: The Simply Typed Lambda-Calculus *)

(* $Date: 2011-06-09 16:11:42 -0400 (Thu, 09 Jun 2011) $ *)


Require Export Types_J.

(* ###################################################################### *)
(** * The Simply Typed Lambda-Calculus *)

(** The simply typed lambda-calculus (STLC) is a tiny core calculus
    embodying the key concept of _functional abstraction_, which shows
    up in pretty much every real-world programming language in some
    form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as above when formalizing
    of this calculus (syntax, small-step semantics, typing rules) and
    its main properties (progress and preservation).  The new
    technical challenges (which will take some work to deal with) all
    arise from the mechanisms of _variable binding_ and
    _substitution_. *)

(* ###################################################################### *)
(** ** Overview *)

(** The STLC is built on some collection of _base types_ -- booleans,
    numbers, strings, etc.  The exact choice of base types doesn't
    matter -- the construction of the language and its theoretical
    properties work out pretty much the same -- so for the sake of
    brevity let's take just [Bool] for the moment.  At the end of the
    chapter we'll see how to add more base types, and in later
    chapters we'll enrich the pure STLC with other useful constructs
    like pairs, records, subtyping, and mutable state.

    Starting from the booleans, we add three things:
        - variables
        - function abstractions
        - application

    This gives us the following collection of abstract syntax
    constructors (written out here in informal BNF notation -- we'll
    formalize it below):
<<<
       t ::= x                       variable
           | \x:T.t1                 abstraction
           | t1 t2                   application
           | true                    constant true
           | false                   constant false
           | if t1 then t2 else t3   conditional
>>
    The [\] symbol in a function abstraction [\x:T.t1] is often
    written as a greek "lambda" (hence the name of the calculus).  The
    variable [x] is called the _parameter_ to the function; the term
    [t1] is its _body_.  The annotation [:T] specifies the type of
    arguments that the function can be applied to.

    Some examples:

      - [\x:Bool. x]

        The identity function for booleans.

      - [(\x:Bool. x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool. if x then false else true]

        The boolean "not" function.

      - [\x:Bool. true]

        The constant function that takes every (boolean) argument to
        [true].

      - [\x:Bool. \y:Bool. x]

        A two-argument function that takes two booleans and returns
        the first one.  (Note that, as in Coq, a two-argument function
        is really a one-argument function whose body is also a
        one-argument function.)

      - [(\x:Bool. \y:Bool. x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true].
        Note that, as in Coq, application associates to the left --
        i.e., this expression is parsed as [((\x:Bool. \y:Bool. x)
        false) true].

      - [\f:Bool->Bool. f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)]

        The same higher-order function, applied to the constantly
        [false] function.

    As the last several examples show, the STLC is a language of
    _higher-order_ functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.

    Another point to note is that the STLC doesn't provide any
    primitive syntax for defining _named_ functions -- all functions
    are "anonymous."  We'll see in chapter [MoreStlc] that it is easy
    to add named functions to what we've got -- indeed, the
    fundamental naming and binding mechanisms are exactly the same.

    The _types_ of the STLC include [Bool], which classifies the
    boolean constants [true] and [false] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions.
<<
      T ::= Bool
          | T1 -> T2
>>
    For example:

      - [\x:Bool. false] has type [Bool->Bool]

      - [\x:Bool. x] has type [Bool->Bool]

      - [(\x:Bool. x) true] has type [Bool]

      - [\x:Bool. \y:Bool. x] has type [Bool->Bool->Bool] (i.e. [Bool -> (Bool->Bool)])

      - [(\x:Bool. \y:Bool. x) false] has type [Bool->Bool]

      - [(\x:Bool. \y:Bool. x) false true] has type [Bool]

      - [\f:Bool->Bool. f (f true)] has type [(Bool->Bool) -> Bool]

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)] has type [Bool]
*)

(* ###################################################################### *)
(** ** Syntax *)

Module STLC.

(* ################################### *)
(** *** Types *)

Inductive ty : Type :=
  | ty_Bool  : ty
  | ty_arrow : ty -> ty -> ty.

(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

(** Something to note here is that an abstraction [\x:T.t] (formally,
    [tm_abs x T t]) is always annotated with the type ([T]) of its
    parameter.  This is in contrast to Coq (and other functional
    languages like ML, Haskell, etc.), which use _type inference_ to
    fill in missing annotations. *)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
  | Case_aux c "tm_abs" | Case_aux c "tm_true"
  | Case_aux c "tm_false" | Case_aux c "tm_if" ].

(** Some examples... *)

Notation a := (Id 0).
Notation b := (Id 1).
Notation c := (Id 2).

(** [idB = \a:Bool. a] *)

Notation idB :=
  (tm_abs a ty_Bool (tm_var a)).

(** [idBB = \a:Bool->Bool. a] *)

Notation idBB :=
  (tm_abs a (ty_arrow ty_Bool ty_Bool) (tm_var a)).

(** [idBBBB = \a:(Bool->Bool)->(Bool->Bool). a] *)

Notation idBBBB :=
  (tm_abs a (ty_arrow (ty_arrow ty_Bool ty_Bool)
                      (ty_arrow ty_Bool ty_Bool))
    (tm_var a)).

(** [k = \a:Bool. \b:Bool. a] *)

Notation k := (tm_abs a ty_Bool (tm_abs b ty_Bool (tm_var a))).

(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)

(* ###################################################################### *)
(** ** Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin -- as
    always -- by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ################################### *)
(** *** Values *)

(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  (An [if]
    expression is never a value.)

    Second, an application is clearly not a value: It represents a
    function being invoked on some argument, which clearly still has
    work left to do.

    Third, for abstractions, we have a choice:

      - We can say that [\a:A.t1] is a value only when [t1] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\a:A.t1] is always a value, no matter
        whether [t1] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Coq makes the first choice -- for example,
[[
         Eval simpl in (fun a:bool => 3 + 4)
]]
    yields [fun a:bool => 7].  But most real functional
    programming languages make the second choice -- reduction of
    a function's body only begins when the function is actually
    applied to an argument.  We also make the second choice here.

    Finally, having made the choice not to reduce under abstractions,
    we don't need to worry about whether variables are values, since
    we'll always be reducing programs "from the outside in," and that
    means the [step] relation will always be working with closed
    terms (ones with no free variables).  *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t)
  | t_true :
      value tm_true
  | t_false :
      value tm_false.

Hint Constructors value.

(* ###################################################################### *)
(** *** Free Variables and Substitution *)

(** Now we come to the heart of the matter: the operation of
    substituting one term for a variable in another term.

    This operation will be used below to define the operational
    semantics of function application, where we will need to
    substitute the argument term for the function parameter in the
    function's body.  For example, we reduce
[[
       (\x:Bool. if x then true else x) false
]]
    to [false] by substituting [false] for the parameter [x] in the
    body of the function.  In general, we need to be able to
    substitute some given term [s] for occurrences of some variable
    [x] in another term [t].  In informal discussions, this is usually
    written [ [s/x]t ] and pronounced "substitute [s] for [x] in [t]."

    Here are some examples:

      - [[true / a] (if a then a else false)] yields [if true then true else false]

      - [[true / a] a] yields [true]

      - [[true / a] (if a then a else b)] yields [if true then true else b]

      - [[true / a] b] yields [b]

      - [[true / a] false] yields [false] (vacuous substitution)

      - [[true / a] (\y:Bool. if y then a else false)] yields [\y:Bool. if y then true else false]
      - [[true / a] (\y:Bool. a)] yields [\y:Bool. true]

      - [[true / a] (\y:Bool. y)] yields [\y:Bool. y]

      - [[true / a] (\a:Bool. a)] yields [\a:Bool. a]

    The last example is very important: substituting [true] for [a] in
    [\a:Bool. a] does _not_ yield [\a:Bool. true]!  The reason for
    this is that the [a] in the body of [\a:Bool. a] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [a].

    Here is the definition, informally...
[[
      [s/x]x = s
      [s/x]y = y                                     if x <> y
      [s/x](\x:T11.t12)   = \x:T11. t12
      [s/x](\y:T11.t12)   = \y:T11. [s/x]t12         if x <> y
      [s/x](t1 t2)        = ([s/x]t1) ([s/x]t2)
      [s/x]true           = true
      [s/x]false          = false
      [s/x](if t1 then t2 else t3) =
                          if [s/x]t1 then [s/x]t2 else [s/x]t3
]]
    ... and formally: *)

Fixpoint subst (s:tm) (x:id) (t:tm) : tm :=
  match t with
  | tm_var x' => if beq_id x x' then s else t
  | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1))
  | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
  end.

(** Technical note: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested in defining the [step] relation on
    closed terms here, we can avoid this extra complexity. *)

(* ################################### *)
(** *** Reduction *)

(** The small-step reduction relation for STLC follows the same
    pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side until it becomes a literal function; then we reduce its
    right-hand side (the argument) until it is also a value; and
    finally we substitute the argument for the bound variable in
    the body of the function.  This last rule, written informally
    as
[[
      (\a:T.t12) v2 ==> [v2/a]t12
]]
    is traditionally called "beta-reduction".

    Informally:
[[[
                     ---------------------------                    (ST_AppAbs)
                     (\a:T.t12) v2 ==> [v2/a]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              t2 ==> t2'
                           ----------------                        (ST_App2)
                           v1 t2 ==> v1 t2'
]]]
   (plus the usual rules for booleans).

   Formally:
*)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tm_app (tm_abs x T t12) v2) ==> (subst v2 x t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tm_app t1 t2 ==> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tm_app v1 t2 ==> tm_app v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(* ##################################### *)
(** *** Examples *)

Lemma step_example1 :
  (tm_app idBB idB) ==>* idB.
Proof.
  eapply rsc_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply rsc_refl.  Qed.

(* A more automatic proof *)
Lemma step_example1' :
  (tm_app idBB idB) ==>* idB.
Proof. normalize.  Qed.

Lemma step_example2 :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  eapply rsc_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply rsc_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply rsc_refl.  Qed.

(** Again, we can use the [normalize] tactic from above to simplify
    the proof. *)

Lemma step_example2' :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  normalize.
Qed.

(** **** Exercise: 2 stars (step_example3) *)
(** Try to do this one both with and without [normalize]. *)

Lemma step_example3 :
       (tm_app (tm_app idBBBB idBB) idB)
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

(** Question: What is the type of the term "[x y]"?

    Answer: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place "typing judgment", informally
    written [Gamma |- t : T], where [Gamma] is a "typing context"
    -- a mapping from variables to their types.

    We hide the definition of partial maps in a module since it is
    actually defined in SfLib. *)

Definition context := partial_map ty.

Module Context.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

End Context.

(* ################################### *)
(** *** Typing Relation *)

(** Informally:
[[[
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x : T

                      Gamma , x:T11 |- t12 : T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 : T11->T12

                        Gamma |- t1 : T11->T12
                          Gamma |- t2 : T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 : T12

                         --------------------                          (T_True)
                         Gamma |- true : Bool

                        ---------------------                         (T_False)
                        Gamma |- false : Bool

       Gamma |- t1 : Bool    Gamma |- t2 : T    Gamma |- t3 : T
       --------------------------------------------------------          (T_If)
                  Gamma |- if t1 then t2 else t3 : T
]]]
The notation [ Gamma , x:T ] means "extend the partial function [Gamma]
to also map [x] to [T]."
*)

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 ->
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T11 T12) ->
      has_type Gamma t2 T11 ->
      has_type Gamma (tm_app t1 t2) T12
  | T_True : forall Gamma,
       has_type Gamma tm_true ty_Bool
  | T_False : forall Gamma,
       has_type Gamma tm_false ty_Bool
  | T_If : forall t1 t2 t3 T Gamma,
       has_type Gamma t1 ty_Bool ->
       has_type Gamma t2 T ->
       has_type Gamma t3 T ->
       has_type Gamma (tm_if t1 t2 t3) T.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs"
  | Case_aux c "T_App" | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

(* ################################### *)
(** *** Examples *)

Example typing_example_1 :
  has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that since we added the has_type constructors to the
    hints database, auto can actually solve this one immediately.
    *)

Example typing_example_1' :
  has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
Proof. auto.  Qed.

Hint Unfold beq_id beq_nat extend.

(** Written informally, the next one is:
[[
     empty |- \a:A. \b:A->A. b (b a))
           : A -> (A->A) -> A.
]]
*)

Example typing_example_2 :
  has_type empty
    (tm_abs a ty_Bool
       (tm_abs b (ty_arrow ty_Bool ty_Bool)
          (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, optional *)
(** Prove the same result without using [auto], [eauto], or
    [eapply]. *)

Example typing_example_2_full :
  has_type empty
    (tm_abs a ty_Bool
       (tm_abs b (ty_arrow ty_Bool ty_Bool)
          (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (typing_example_3) *)
(** Formally prove the following typing derivation holds:
[[
   empty |- (\a:Bool->B. \b:Bool->Bool. \c:Bool.
               b (a c))
         : T.
]]
*)

Example typing_example_3 :
  exists T,
    has_type empty
      (tm_abs a (ty_arrow ty_Bool ty_Bool)
         (tm_abs b (ty_arrow ty_Bool ty_Bool)
            (tm_abs c ty_Bool
               (tm_app (tm_var b) (tm_app (tm_var a) (tm_var c))))))
      T.

Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\a:Bool. \b:Bool, a b] -- i.e.,
[[
    ~ exists T,
        empty |- (\a:Bool. \b:Bool, a b) : T.
]]
*)
Example typing_nonexample_1 :
  ~ exists T,
      has_type empty
        (tm_abs a ty_Bool
            (tm_abs b ty_Bool
               (tm_app (tm_var a) (tm_var b))))
        T.
Proof.
  intros C. destruct C.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(** **** Exercise: 3 stars (typing_nonexample_3) *)
(** Another nonexample:
[[
    ~ (exists S, exists T,
          empty |- (\a:S. a a) : T).
]]
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        has_type empty
          (tm_abs a S
             (tm_app (tm_var a) (tm_var a)))
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (typing_statements) *)

(** Which of the following propositions are provable?
       - [b:Bool |- \a:Bool.a : Bool->Bool]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. b a) : T]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. a b) : T]

       - [exists S, a:S |- (\b:Bool->Bool. b) a : S]

       - [exists S, exists T,  a:S |- (a a a) : T]

[]
*)

(** **** Exercise: 1 star, optional (more_typing_statements) *)

(** Which of the following propositions are provable?  For the
    ones that are, give witnesses for the existentially bound
    variables.
       - [exists T,  empty |- (\b:B->B->B. \a:B, b a) : T]

       - [exists T,  empty |- (\a:A->B, \b:B-->C, \c:A, b (a c)):T]

       - [exists S, exists U, exists T,  a:S, b:U |- \c:A. a (b c) : T]

       - [exists S, exists T,  a:S |- \b:A. a (a b) : T]

       - [exists S, exists U, exists T,  a:S |- a (\c:U. c a) : T]

[]
*)

(* ###################################################################### *)
(** ** Properties *)

(* ###################################################################### *)
(** *** Free Occurrences *)

(** A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].  For example:
      - [y] appears free, but [x] does not, in [\x:T->U. x y]
      - both [x] and [y] appear free in [(\x:T->U. x y) x]
      - no variables appear free in [\x:T->U. \y:T. x y]  *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tm_var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tm_abs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tm_if t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tm_if t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2"
  | Case_aux c "afi_abs"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

(** A term in which no variables appear free is said to be _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** *** Substitution *)

(** We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
      in [t], that, for all contexts [Gamma], if [t] is well typed
      under [Gamma], then [Gamma] assigns some type to [x].

      - If the last rule used was [afi_var], then [t = x], and from
        the assumption that [t] is well typed under [Gamma] we have
        immediately that [Gamma] assigns a type to [x].

      - If the last rule used was [afi_app1], then [t = t1 t2] and [x]
        appears free in [t1].  Since [t] is well typed under [Gamma],
        we can see from the typing rules that [t1] must also be, and
        the IH then tells us that [Gamma] assigns [x] a type.

      - Almost all the other cases are similar: [x] appears free in a
        subterm of [t], and since [t] is well typed under [Gamma], we
        know the subterm of [t] in which [x] appears is well typed
        under [Gamma] as well, and the IH gives us exactly the
        conclusion we want.

      - The only remaining case is [afi_abs].  In this case [t =
        \y:T11.t12], and [x] appears free in [t12]; we also know that
        [x] is different from [y].  The difference from the previous
        cases is that whereas [t] is well typed under [Gamma], its
        body [t12] is well typed under [(Gamma, y:T11)], so the IH
        allows us to conclude that [x] is assigned some type by the
        extended context [(Gamma, y:T11)].  To conclude that [Gamma]
        assigns a type to [x], we appeal to lemma [extend_neq], noting
        that [x] and [y] are different variables. *)

Proof.
  intros. generalize dependent Gamma. generalize dependent T.
  afi_cases (induction H) Case;
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    apply not_eq_beq_id_false in H.
    rewrite extend_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)

(** **** Exercise: 2 stars (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T,
    has_type empty t T  ->
    closed t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Sometimes, when we have a proof [Gamma |- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' t S.

(** _Proof_: By induction on a derivation of [Gamma |- t : T].

      - If the last rule in the derivation was [T_Var], then [t = x]
        and [Gamma x = T].  By assumption, [Gamma' x = T] as well, and
        hence [Gamma' |- t : T] by [T_Var].

      - If the last rule was [T_Abs], then [t = \y:T11. t12], with [T
        = T11 -> T12] and [Gamma, y:T11 |- t12 : T12].  The induction
        hypothesis is that for any context [Gamma''], if [Gamma,
        y:T11] and [Gamma''] assign the same types to all the free
        variables in [t12], then [t12] has type [T12] under [Gamma''].
        Let [Gamma'] be a context which agrees with [Gamma] on the
        free variables in [t]; we must show [Gamma' |- \y:T11. t12 :
        T11 -> T12].

        By [T_Abs], it suffices to show that [Gamma', y:T11 |- t12 :
        T12].  By the IH (setting [Gamma'' = Gamma', y:T11]), it
        suffices to show that [Gamma, y:T11] and [Gamma', y:T11] agree
        on all the variables that appear free in [t12].

        Any variable occurring free in [t12] must either be [y], or
        some other variable.  [Gamma, y:T11] and [Gamma', y:T11]
        clearly agree on [y].  Otherwise, we note that any variable
        other than [y] which occurs free in [t12] also occurs free in
        [t = \y:T11. t12], and by assumption [Gamma] and [Gamma']
        agree on all such variables, and hence so do [Gamma, y:T11]
        and [Gamma', y:T11].

      - If the last rule was [T_App], then [t = t1 t2], with [Gamma |-
        t1 : T2 -> T] and [Gamma |- t2 : T2].  One induction
        hypothesis states that for all contexts [Gamma'], if [Gamma']
        agrees with [Gamma] on the free variables in [t1], then [t1]
        has type [T2 -> T] under [Gamma']; there is a similar IH for
        [t2].  We must show that [t1 t2] also has type [T] under
        [Gamma'], given the assumption that [Gamma'] agrees with
        [Gamma] on all the free variables in [t1 t2].  By [T_App], it
        suffices to show that [t1] and [t2] each have the same type
        under [Gamma'] as under [Gamma].  However, we note that all
        free variables in [t1] are also free in [t1 t2], and similarly
        for free variables in [t2]; hence the desired result follows
        by the two IHs.
*)

Proof with eauto.
  intros.
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x0 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [extend Gamma x T11] *)
    unfold extend. remember (beq_id x x0) as e. destruct e...
  Case "T_App".
    apply T_App with T11...
Qed.

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types.

    Formally, the so-called _Substitution Lemma_ says this: suppose we
    have a term [t] with a free variable [x], and suppose we've been
    able to assign a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we should be
    able to substitute [v] for each of the occurrences of [x] in [t]
    and obtain a new term that still has type [T]. *)

(** _Lemma_: If [Gamma,x:U |- t : T] and [|- v : U], then [Gamma |-
    [v/x]t : T]. *)

Lemma substitution_preserves_typing : forall Gamma x U v t T,
     has_type (extend Gamma x U) t T ->
     has_type empty v U   ->
     has_type Gamma (subst v x t) T.

(** One technical subtlety in the statement of the lemma is that we
    assign [v] the type [U] in the _empty_ context -- in other words,
    we assume [v] is closed.  This assumption considerably simplifies
    the [T_Abs] case of the proof (compared to assuming [Gamma |- v :
    U], which would be the other reasonable assumption at this point)
    because the context invariance lemma then tells us that [v] has
    type [U] in any context at all -- we don't have to worry about
    free variables in [v] clashing with the variable being introduced
    into the context by [T-Abs].

    _Proof_: We prove, by induction on [t], that, for all [T] and
    [Gamma], if [Gamma,x:U |- t : T] and [|- v : U], then [Gamma |-
    [v/x]t : T].

      - If [t] is a variable, there are two cases to consider, depending
        on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [Gamma, x:U |- x : T] we
            conclude that [U = T].  We must show that [[v/x]x = v] has
            type [T] under [Gamma], given the assumption that [v] has
            type [U = T] under the empty context.  This follows from
            context invariance: if a closed term has type [T] in the
            empty context, it has that type in any context.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [Gamma,
            x:U] as under [Gamma].

      - If [t] is an abstraction [\y:T11. t12], then the IH tells us,
        for all [Gamma'] and [T'], that if [Gamma',x:U |- t12 : T']
        and [|- v : U], then [Gamma' |- [v/x]t12 : T'].  In
        particular, if [Gamma,y:T11,x:U |- t12 : T12] and [|- v : U],
        then [Gamma,y:T11 |- [v/x]t12 : T12].  There are again two
        cases to consider, depending on whether [x] and [y] are the
        same variable name.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[v/x]t = t], so we just need to show [Gamma |-
        t : T].  But we know [Gamma,x:U |- t : T], and since the
        variable [y] does not appear free in [\y:T11. t12], the
        context invariance lemma yields [Gamma |- t : T].

        Second, suppose [x <> y].  We know [Gamma,x:U,y:T11 |- t12 :
        T12] by inversion of the typing relation, and [Gamma,y:T11,x:U
        |- t12 : T12] follows from this by the context invariance
        lemma, so the IH applies, giving us [Gamma,y:T11 |- [v/x]t12 :
        T12].  By [T_Abs], [Gamma |- \y:T11. [v/x]t12 : T11->T12], and
        by the definition of substitution (noting that [x <> y]),
        [Gamma |- \y:T11. [v/x]t12 : T11->T12], as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case.

    Another technical note: This proof is a rare case where an
    induction on terms, rather than typing derivations, yields a
    simpler argument.  The reason for this is that the assumption
    [has_type (extend Gamma x U) t T] is not completely generic, in
    the sense that one of the "slots" in the typing relation -- namely
    the context -- is not just a variable, and this means that Coq's
    native induction tactic does not give us the induction hypothesis
    that we want.  It is possible to work around this, but the needed
    generalization is a little tricky.  The term [t], on the other
    hand, _is_ completely generic. *)

Proof with eauto.
  intros Gamma x U v t T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  tm_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tm_var".
    rename i into y. remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2...
  Case "tm_abs".
    rename i into y. apply T_Abs.
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
Qed.

(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [v/x] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** *** Preservation *)

(** We now have the tools we need to prove _preservation_: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.

(** _Proof_: by induction on the derivation of [|- t : T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [subst t2 x t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  has_type_cases (induction HT) Case;
     intros t' HE; subst Gamma; subst;
     try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [auto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

(** **** Exercise: 2 stars, recommended (subject_expansion_stlc) *)
(** An exercise earlier in this file asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That
    is, is it always the case that, if [t ==> t'] and [has_type
    t' T], then [has_type t T]?  If so, prove it.  If not, give a
    counter-example.

(* FILL IN HERE *)
[]
*)

(* ###################################################################### *)
(** *** Progress *)

(** Finally, the _progress_ theorem tells us that closed, well-typed
    terms are never stuck: either a well-typed term is a value, or
    else it can take an evaluation step.
*)

Theorem progress : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [|- t : T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 : T2 -> T] and [|- t2 : T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      is either a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).

*)

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.

  Case "T_App".
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...

    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        (* Since [t1] is a value and has an arrow type, it
           must be an abs. Sometimes this is proved separately
           and called a "canonical forms" lemma. *)
        inversion H; subst. exists (subst t2 x t)...
        solve by inversion. solve by inversion.
      SSCase "t2 steps".
        destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...

    SCase "t1 steps".
      destruct H as [t1' Hstp]. exists (tm_app t1' t2)...

  Case "T_If".
    right. destruct IHHt1...

    SCase "t1 is a value".
      (* Since [t1] is a value of boolean type, it must
         be true or false *)
      inversion H; subst. solve by inversion.
      SSCase "t1 = true". eauto.
      SSCase "t1 = false". eauto.

    SCase "t1 also steps".
      destruct H as [t1' Hstp]. exists (tm_if t1' t2 t3)...
Qed.

(** **** Exercise: 3 stars, optional (progress_from_term_ind) *)
(** Show that progress can also be proved by induction on terms
    instead of types. *)

Theorem progress' : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  tm_cases (induction t) Case; intros T Ht; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** *** Uniqueness of Types *)

(** **** Exercise: 3 stars (types_unique) *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** Formalize this statement and prove it. *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** ** Additional Exercises *)

(** **** Exercise: 1 star (progress_preservation_statement) *)
(** Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)
(** [] *)

(** **** Exercise: 2 stars, optional (stlc_variation1) *)
(** Suppose we add the following new rule to the evaluation
    relation of the STLC:
[[
      | T_Strange : forall x t,
           has_type empty (tm_abs x Bool t) Bool
]]
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinacy of [step]

      - Progress

      - Preservation

[]
*)

(** **** Exercise: 2 stars (stlc_variation2) *)
(** Suppose we remove the rule [ST_App1] from the [step]
    relation. Which of the three properties in the previous
    exercise become false in the absence of this rule? For each
    that becomes false, give a counterexample.

[]
*)

End STLC.

(* ###################################################################### *)
(* ###################################################################### *)
(** * Exercise: STLC with Arithmetic *)

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.

(* ###################################################################### *)
(** ** Syntax and Operational Semantics *)

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity) *)

Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_Nat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing... *)

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_nat  : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
  | Case_aux c "tm_abs" | Case_aux c "tm_nat"
  | Case_aux c "tm_succ" | Case_aux c "tm_pred"
  | Case_aux c "tm_mult" | Case_aux c "tm_if0" ].

(** **** Exercise: 4 stars, recommended (STLCArith) *)
(** Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties of the original STLC to deal
      with the new syntactic forms.  Make sure Coq accepts the whole file. *)

(* FILL IN HERE *)
(** [] *)

End STLCArith.

