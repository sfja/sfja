(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)

(* $Date: 2011-04-20 14:26:52 -0400 (Wed, 20 Apr 2011) $ *)

Require Export Stlc_J.
Require Import Relations.

(* ###################################################################### *)
(** * Simple Extensions to STLC *)

(** The simply typed lambda-calculus has enough structure to make its
    theoretical properties interesting, but it is not yet much of a
    programming language.  In this chapter, we begin to close the gap
    with real-world languages by introducing a number of familiar
    features that have straightforward treatments at the level of
    typing. *)

(** *** Numbers *)

(** Adding types, constants, and primitive operations for numbers is
    easy -- just a matter of combining the two halves of the [Stlc]
    chapter. *)

(** *** [let]-bindings *)

(** When writing a complex expression, it is often useful to give
    names to some of its subexpressions: this avoids repetition and
    often increases readability.  Most languages provide one or more
    ways of doing this.  In OCaml (and Coq), for example, we can write
    [let x=t1 in t2] to mean ``evaluate the expression [t1] and bind
    the name [x] to the resulting value while evaluating [t2].''

    Our [let]-binder follows OCaml's in choosing a call-by-value
    evaluation order, where the [let]-bound term must be fully
    evaluated before evaluation of the [let]-body can begin.  The
    typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body, which is then
    the type of the whole [let] expression.

    At this point in the course, it's probably easier simply to look
    at the rules defining this new feature as to wade through a lot of
    english text conveying the same information.  Here they are:

    Syntax:
<<
       t ::=                Terms
           | ...               (other terms same as before)
           | let x=t in t      let-binding
>>
    Reduction:
[[[
                                 t1 ==> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 ==> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 ==> [v1/x] t2
]]]
    Typing:
[[[
                Gamma |- t1 : T1      Gamma , x:T1 |- t2 : T2
                --------------------------------------------            (T_Let)
                        Gamma |- let x=t1 in t2 : T2
]]]
 *)

(** *** Pairs *)

(** Our functional programming examples have made frequent use of
    _pairs_ of values.  The type of such pairs is called a _product
    type_.

    The formalization of pairs is almost too simple to be worth
    discussing.  However, let's look briefly at the various parts of
    the definition to emphasize the common pattern.

    In Coq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative style is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our products this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:
<<
       \x:Nat*Nat.
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
>>

    Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term -- pairing, written [(t1,t2)], and
    projection, written [t.fst] for the first projection from [t] and
    [t.snd] for the second projection -- plus one new type constructor,
    [T1*T2], called the _product_ of [T1] and [T2].

    Syntax:
<<
       t ::=                Terms
           | ...
           | (t,t)             pair
           | t.fst             first projection
           | t.snd             second projection

       v ::=                Values
           | ...
           | (v,v)             pair value

       T ::=                Types
           | ...
           | T * T             product type
>>

   For evaluation, we need several new rules specifying how pairs and
   projection behave.
[[[
                              t1 ==> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) ==> (t1',t2)

                              t2 ==> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) ==> (v1,t2')

                              t1 ==> t1'
                          ------------------                          (ST_Fst1)
                          t1.fst ==> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst ==> v1

                              t1 ==> t1'
                          ------------------                          (ST_Snd1)
                          t1.snd ==> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd ==> v2
]]]
    Rules [ST_FstPair] and [ST_SndPair] specify that, when a fully
    evaluated pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules [ST_Fst1] and
    [ST_Snd1] allow reduction to proceed under projections, when the
    term being projected from has not yet been fully evaluated.
    [ST_Pair1] and [ST_Pair2] evaluate the parts of pairs: first the
    left part, and then -- when a value appears on the left -- the right
    part.  The ordering arising from the use of the metavariables [v]
    and [t] in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like [v] and [v1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that [(v1,v2)] is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully evaluated before the function
    body starts executing.

   The typing rules for pairs and projections are straightforward.
[[[
               Gamma |- t1 : T1       Gamma |- t2 : T2
               ---------------------------------------                 (T_Pair)
                       Gamma |- (t1,t2) : T1*T2

                        Gamma |- t1 : T11*T12
                        ---------------------                           (T_Fst)
                        Gamma |- t1.fst : T11

                        Gamma |- t1 : T11*T12
                        ---------------------                           (T_Snd)
                        Gamma |- t1.snd : T12
]]]
   The rule [T_Pair] says that [(t1,t2)] has type [T1*T2] if [t1] has
   type [T1] and [t2] has type [T2].  Conversely, the rules [T_Fst]
   and [T_Snd] tell us that, if [t1] has a product type
   [T11*T12] (i.e., if it will evaluate to a pair), then the types of
   the projections from this pair are [T11] and [T12]. *)

(** *** Sums *)

(** Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify employees in an accounting
   application using using _either_ their name _or_ their id number.
   A search function might return _either_ a matching value _or_ an
   error code.

   These are specific examples of a binary _sum type_,
   which describes a set of values drawn from exactly two given types, e.g.
<<
       Nat + Bool
>>
   We create elements of these types by _tagging_ elements of the
   component types.  For example, if [n] is a [Nat] then [inl v] is an
   element of [Nat+Bool]; similarly, if [b] is a [Bool] then [inr b]
   is a [Nat+Bool].  The names of the tags [inl] and [inr] arise from
   thinking of them as functions

<<
   inl : Nat -> Nat + Bool
   inr : Bool -> Nat + Bool
>>

   that "inject" elements of [Nat] or [Bool] into the left and right
   components of the sum type [Nat+Bool].  (But note that we don't
   actually treat them as functions in the way we formalize them:
   [inl] and [inr] are keywords, and [inl t] and [inr t] are primitive
   syntactic forms, not function applications.  This allows us to give
   them their own special typing rules.)

   In general, the elements of a type [T1 + T2] consist of the
   elements of [T1] tagged with the token [inl], plus the elements of
   [T2] tagged with [inr].

   To _use_ elements of sum types, we introduce a [case] construct (a
   very simplified form of Coq's [match]) to destruct them. For
   example, the following procedure converts a [Nat+Bool] into a
   [Nat]:

<<
    getNat =
      \x:Nat+Bool.
        case x of
          inl n => n
        | inr b => if b then 1 else 0
>>

    More formally...

    Syntax:
<<
       t ::=                Terms
           | ...
           | inl T t           tagging (left)
           | inr T t           tagging (right)
           | case t of         case
               inl x => t
             | inr x => t

       v ::=                Values
           | ...
           | inl T v           tagged value (left)
           | inr T v           tagged value (right)

       T ::=                Types
           | ...
           | T + T             sum type
>>

   Evaluation:

[[[
                              t1 ==> t1'
                        ----------------------                         (ST_Inl)
                        inl T t1 ==> inl T t1'

                              t1 ==> t1'
                        ----------------------                         (ST_Inr)
                        inr T t1 ==> inr T t1'

                              t0 ==> t0'
                   -------------------------------------------       (ST_Case)
                   case t0 of inl x1 => t1 | inr x2 => t2 ==>
                   case t0' of inl x1 => t1 | inr x2 => t2

            ----------------------------------------------         (ST_CaseInl)
            case (inl T v0) of inl x1 => t1 | inl x2 => t2
                           ==>  [v0/x1] t1

            ----------------------------------------------         (ST_CaseInr)
            case (inr T v0) of inl x1 => t1 | inl x2 => t2
                           ==>  [v0/x2] t2
]]]

Typing:
[[[
                          Gamma |- t1 :  T1
                     ----------------------------                       (T_Inl)
                     Gamma |- inl T2 t1 : T1 + T2

                           Gamma |- t1 : T2
                     ----------------------------                       (T_Inr)
                     Gamma |- inr T1 t1 : T1 + T2

                         Gamma |- t0 : T1+T2
                       Gamma , x1:T1 |- t1 : T
                       Gamma , x2:T2 |- t2 : T
         ---------------------------------------------------           (T_Case)
         Gamma |- case t0 of inl x1 => t1 | inr x2 => t2 : T
]]]

    The reason for the type annotation on the [inl] and [inr] forms
    has to do with uniqueness of types.  Without this extra
    information, the typinf rule [T_Inl], for example, would have to
    say that, once we have shown that [t1] is an element of type [T1],
    we can derive that [inl t1] is an element of [T1 + T2] for _any_
    type T2.  For example, we could derive both [inl 5 : Nat + Nat]
    and [inl 5 : Nat + Bool] (and infinitely many other types).
    This failure of uniqueness of types would mean that we cannot
    build a typechecking algorithm simply by "reading the rules from
    bottom to top" as we could for all the other features seen so far.

    There are various ways to deal with this difficulty.  One simple
    one -- which we've adopted here -- forces the programmer to
    explicitly annotate the "other side" of a sum type when performing
    an injection.  This is rather heavyweight for programmers (and so
    real languages adopt other solutions), but it is easy to
    understand and formalize. *)

(** *** Lists *)

(** The typing features we have seen can be classified into _base
    types_ like [Bool], and _type constructors_ like [->] and [*] that
    build new types from old ones.  Another useful type constructor is
    [List].  For every type [T], the type [List T] describes
    finite-length lists whose elements are drawn from [T].

    In principle, we could develop lists given facilities for defining
    variants and for defining _recursive_ types.  But we've skipped
    the details of the former, and giving semantics to the latter is
    non-trivial. Instead, we'll just discuss the special case of lists
    directly.

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on [nil] and cannot appear on [cons], these lists are essentially
    identical to those we built in Coq.  We use [lcase] to destruct
    lists, to avoid dealing with questions like "what is the [head] of
    the empty list?"  So, for example, here is a function that
    calculates the sum of the first two elements of a list of numbers:

<<
    \x:List Nat.
    lcase x of nil -> 0
       | a::x' -> lcase x' of nil -> a
                     | b::x'' -> a+b
>>

    While we say that [cons v1 v2] is a value, we really mean that
    [v2] should also be a list -- we'll have to enforce this in the
    formal definition of value. *)

(**
    Syntax:
<<
       t ::=                Terms
           | ...
           | nil T
           | cons t t
           | lcase t of nil -> t | x::x -> t

       v ::=                Values
           | ...
           | nil T             nil value
           | cons v v          cons value

       T ::=                Types
           | ...
           | List T            list of Ts
>>
   Reduction:
[[[
                                 t1 ==> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 ==> cons t1' t2

                                 t2 ==> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 ==> cons v1 t2'

                              t1 ==> t1'
                ----------------------------------------             (ST_Lcase1)
                (lcase t1 of nil -> t2 | h::t -> t3) ==>
                (lcase t1' of nil -> t2 | h::t -> t3)

               ---------------------------------------            (ST_LcaseNil)
               (lcase nil T of nil -> t2 | h::t -> t3)
                                ==> t2

            ----------------------------------------------       (ST_LcaseCons)
            (lcase (cons vh vt) of nil -> t2 | h::t -> t3)
                          ==> [vh/h,vt/t]t3
]]]

   Typing:
[[[
                          -----------------------                       (T_Nil)
                          Gamma |- nil T : List T

                Gamma |- t1 : T      Gamma |- t2 : List T
                -----------------------------------------              (T_Cons)
                       Gamma |- cons t1 t2: List T

                        Gamma |- t1 : List T1
                           Gamma |- t2 : T
                   Gamma , h:T1, t:List T1 |- t3 : T
          -------------------------------------------------           (T_Lcase)
          Gamma |- (lcase t1 of nil -> t2 | h::t -> t3) : T
]]]
*)


(** *** General Recursion *)

(** Another facility found in most programming languages (including
    Coq) is the ability to define recursive functions.  For example,
    we might like to be able to define the factorial function like
    this:
<<
   fact = \x:Nat.
             if x=0 then 1 else x * (fact (pred x)))
>>
   But this would require quite a bit of work to formalize: we'd have
   to introduce a notion of "function definitions" and carry around an
   "environment" of such definitions in the definition of the [step]
   relation.

   Here is another way that is straightforward to formalize: instead
   of writing recursive definitions where the right-hand side can
   contain the identifier being defined, we can define a _fixed-point
   operator_ that performs the "unfolding" of the recursive definition
   in the right-hand side lazily during reduction.
<<
   fact =
       fix
         (\f:Nat->Nat.
            \x:Nat.
               if x=0 then 1 else x * (f (pred x)))
>>
   The intuition is that the higher-order function [f] passed to [fix]
   is a _generator_ for the [fact] function: if [fact] is applied to a
   function that approximates the desired behavior of [fact] up to
   some number [n] (that is, a function that returns correct results
   on inputs less than or equal to [n]), then it returns a better
   approximation to [fact] -- a function that returns correct results
   for inputs up to [n+1].  Applying [fix] to this generator returns
   its _fixed point_ -- a function that gives the desired behavior for
   all inputs [n].

   (The term "fixed point" has exactly the same sense as in ordinary
   mathematics, where a fixed point of a function [f] is an input [x]
   such that [f(x) = x].  Here, a fixed point of a function [F] of
   type (say) [(Nat->Nat)->(Nat->Nat)] is a function [f] such that [F
   f] is behaviorally equivalent to [f].)

   Syntax:
<<
       t ::=                Terms
           | ...
           | fix t             fixed-point operator
>>
   Reduction:
[[[
                                 t1 ==> t1'
                             ------------------                       (ST_Fix1)
                             fix t1 ==> fix t1'

                -------------------------------------------         (ST_FixAbs)
                fix (\x:T1.t2) ==> [(fix(\x:T1.t2)) / x] t2
]]]
   Typing:
[[[
                            Gamma |- t1 : T1->T1
                            --------------------                        (T_Fix)
                            Gamma |- fix t1 : T1
]]]
 *)

(** **** Exercise: 1 star (halve_fix) *)
(** Translate this recursive definition into one using [fix]:
<<
   halve =
     \x:Nat.
        if x=0 then 0
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
(* FILL IN HERE *)
[]
*)

(** **** Exercise: 1 star, recommended (fact_steps) *)
(** Write down the sequence of steps that the term [fact 1] goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* FILL IN HERE *)
[]
*)

(** The ability to form the fixed point of a function of type [T->T]
    for any [T] has some surprising consequences.  In particular, it
    implies that _every_ type is inhabited by some term.  To see this,
    observe that, for every type [T], we can define the term
[[
    fix (\x:T.x)
]]
    By [T_Fix]  and [T_Abs], this term has type [T].  By [ST_FixAbs]
    it reduces to itself, over and over again.  Thus it is an
    _undefined element_ of [T].

    More usefully, here's an example using [fix] to define a
    two-argument recursive function:
<<
    equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
>>

    And finally, here is an example where [fix] is used to define a
    _pair_ of recursive functions (illustrating the fact that the type
    [T1] in the rule [T_Fix] need not be a function type):
<<
    evenodd =
      fix
        (\eo: (Nat->Bool * Nat->Bool).
           let e = \n:Nat. if n=0 then true  else eo.snd (pred n) in
           let o = \n:Nat. if n=0 then false else eo.fst (pred n) in
           (e,o))

    even = evenodd.fst
    odd  = evenodd.snd
>>

*)



(* ###################################################################### *)
(** ** Records and Variants (Optional) *)

(** As a final example of a basic extension of the STLC, let's look
    briefly at how to formalize _records_ and their types.  This
    extension is conceptually a straightforward generalization of
    pairs and product types, but notationally it becomes a little
    heavier; for this reason, we postpone its formal treatment to a
    separate chapter ([Records]).

    This material is not included in the extended exercise below.  It
    can be skipped or skimmed, if desired. *)

(* ################################# *)
(** *** The [Unit] Type *)

(** Another handy base type, found especially in languages in the ML
    family, is the singleton type [Unit].  It has a single element --
    the term constant [unit] (with a small [u]) -- and a typing rule
    making [unit] an element of [Unit].  We also add [unit] to the set
    of possible result values of computations -- indeed, [unit] is the
    _only_ possible result of evaluating an expression of type [Unit].

Syntax:
<<
       t ::=                Terms
           | ...
           | unit              unit value

       v ::=                Values
           | ...
           | unit              unit

       T ::=                Types
           | ...
           | Unit              Unit type
>>
    Typing:
[[[
                         --------------------                          (T_Unit)
                         Gamma |- unit : Unit
]]]

    It may seem a little strange to bother defining a type that has
    just one element -- after all, wouldn't every computation living
    in such a type be trivial?

    This is a fair question, and indeed in the STLC the [Unit] type is
    not especially critical (though we'll see one use for it a bit
    below).  Where [Unit] really comes in handy is in richer languages
    with various sorts of _side effects_ -- e.g., assignment
    statements that mutate variables or pointers, exceptions and other
    sorts of nonlocal control structures, etc.  In such languages, it
    is convenient to have a type for the (trivial) result of an
    expression that is evaluated only for its effect. *)

(* ###################################################################### *)
(** *** Records *)

(** Another familiar structure from everyday programming languages is
    _records_.  Intuitively, records can be obtained from pairs by two
    kinds of generalization:   they are n-ary products (rather than just binary)
    and their fields are accessed by _label_ (rather than position).

    Syntax:
<<
       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t.i                         projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
>>
   Intuitively, the generalization is pretty obvious.  But it's worth
   noticing that what we've actually written is rather informal: in
   particular, we've written "[...]" in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side-condition that the labels of a record should not contain
   repetitions.  It is possible to devise informal notations that are
   more precise, but these tend to be quite heavy and to obscure the
   main points of the definitions.  So we'll leave these a bit loose
   here (they are informal anyway, after all) and do the work of
   tightening things up elsewhere (in [Records.v]).

   Reduction:
[[[
                              ti ==> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti, ...}
                 ==> {i1=v1, ..., im=vm, in=ti', ...}

                              t1 ==> t1'
                            --------------                           (ST_Proj1)
                            t1.i ==> t1'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i ==> vi
]]]
   Again, these rules are a bit informal.  For example, the first rule
   is intended to be read "if [ti] is the leftmost field that is not a
   value and if [ti] steps to [ti'], then the whole record steps..."
   In the last rule, the intention is that there should only be one
   field called i, and that all the other fields must contain values.

   Typing:
[[[
            Gamma |- t1 : T1     ...     Gamma |- tn : Tn
          --------------------------------------------------            (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                    Gamma |- t : {..., i:Ti, ...}
                    -----------------------------                      (T_Proj)
                          Gamma |- t.i : Ti
]]]

*)

(* ###################################################################### *)
(** *** Encoding Records *)

(** There are several ways to make the above definitions precise.

      - We can directly formalize the syntactic forms and inference
        rules, staying as close as possible to the form we've given
        them above.  This is conceptually straightforward, and it's
        probably what we'd want to do if we were building a real
        compiler -- in particular, it will allow is to print error
        messages in the form that programmers will find easy to
        understand.  But the formal versions of the rules will not be
        pretty at all!

      - We could look for a smoother way of presenting records -- for
        example, a binary presentation with one constructor for the
        empty record and another constructor for adding a single field
        to an existing record, instead of a single monolithic
        constructor that builds a whole record at once.  This is the
        right way to go if we are primarily interested in studying the
        metatheory of the calculi with records, since it leads to
        clean and elegant definitions and proofs.  The file [Records.v]
        shows how this can be done.

      - Alternatively, if we like, we can avoid formalizing records
        altogether, by stipulating that record notations are just
        informal shorthands for more complex expressions involving
        pairs and product types.  We sketch this approach here.

    First, observe that we can encode arbitrary-size tuples using
    nested pairs and the [unit] value.  To avoid overloading the pair
    notation [(t1,t2)], we'll use curly braces without labels to write
    down tuples, so [{}] is the empty tuple, [{5}] is a singleton
    tuple, [{5,6}] is a 2-tuple (morally the same as a pair),
    [{5,6,7}] is a triple, etc.
<<
    {}                 ---->  unit
    {t1, t2, ..., tn}  ---->  (t1, trest)
                              where {t2, ..., tn} ----> trest
>>
    Similarly, we can encode tuple types using nested product types:
<<
    {}                 ---->  Unit
    {T1, T2, ..., Tn}  ---->  T1 * TRest
                              where {T2, ..., Tn} ----> TRest
>>
    The operation of projecting a field from a tuple can be encoded
    using a sequence of second projections followed by a first projection:
<<
    t.0        ---->  t.fst
    t.(n+1)    ---->  (t.snd).n
>>

    Next, suppose that there is some total ordering on record labels,
    so that we can associate each label with a unique natural number.
    This number is called the _position_ of the label.  For example,
    we might assign positions like this:
<<
      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      foo     1004
      ...     ...
      bar     10562
      ...     ...
>>

    We use these positions to encode record values as tuples (i.e., as
    nested pairs) by sorting the fields according to their positions.
    For example:
<<
      {a=5, b=6}      ---->   {5,6}
      {a=5, c=7}      ---->   {5,unit,7}
      {c=7, a=5}      ---->   {5,unit,7}
      {c=5, b=3}      ---->   {unit,3,5}
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}
>>
    Note that each field appears in the position associated with its
    label, that the size of the tuple is determined by the label with
    the highest position, and that we fill in unused positions with
    [unit].

    We do exactly the same thing with record types:
<<
      {a:Nat, b:Nat}      ---->   {Nat,Nat}
      {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}
>>

    Finally, record projection is encoded as a tuple projection from
    the appropriate position:
<<
      t.l  ---->  t.(position of l)
>>

    It is not hard to check that all the typing rules for the original
    "direct" presentation of records are validated by this
    encoding.  (The reduction rules are "almost validated" -- not
    quite, because the encoding reorders fields.) *)

(** Of course, this encoding will not be very efficient if we
    happen to use a record with label [bar]!  But things are not
    actually as bad as they might seem: for example, if we assume that
    our compiler can see the whole program at the same time, we can
    _choose_ the numbering of labels so that we assign small positions
    to the most frequently used labels.  Indeed, there are industrial
    compilers that essentially do this! *)

(** *** Variants *)

(** Just as products can be generalized to records, sums can be
    generalized to n-ary labeled types called _variants_.  Instead of
    [T1+T2], we can write something like [<l1:T1,l2:T2,...ln:Tn>]
    where [l1],[l2],... are field labels which are used both to build
    instances and as case arm labels.

    These n-ary variants give us almost enough mechanism to build
    arbitrary inductive data types like lists and trees from
    scratch -- the only thing missing is a way to allow _recursion_ in
    type definitions.  We won't cover this here, but detailed
    treatments can be found in many textbooks -- e.g., Types and
    Programming Languages. *)

(* ###################################################################### *)
(** * Formalizing the Extensions *)

(** **** Exercise: 4 stars, recommended (STLC_extensions) *)
(** Formalizing the extensions (not including the optional ones) is
    left to you.  We've provided the necessary extensions to the
    syntax of terms and types, and we've included a few examples that
    you can test your definitions with to make sure they are working
    as expected.  You'll fill in the rest of the definitions and
    extend all the proofs accordingly.

    A good strategy is to work on the extensions one at a time, in
    multiple passes, rather than trying to work through the file from
    start to finish in a single pass.  For each definition or proof,
    begin by reading carefully through the parts that are provided for
    you, referring to the text in the [Stlc] chapter for high-level
    intuitions and the embedded comments for detailed mechanics.

    A good order for attempting the extensions is:
      - numbers first (since they are both familiar and simple)
      - products
      - let (which involves binding)
      - sums (which involve slightly more complex binding)
      - lists (which involve yet more complex binding)
      - [fix] *)

Module STLCExtended.

(* ###################################################################### *)
(** *** Syntax and Operational Semantics *)

Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_prod  : ty -> ty -> ty
  | ty_sum   : ty -> ty -> ty
  | ty_List  : ty -> ty
  | ty_Nat   : ty.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ty_arrow"
  | Case_aux c "ty_prod" | Case_aux c "ty_sum"
  | Case_aux c "ty_List" | Case_aux c "ty_Nat" ].

Inductive tm : Type :=
  (* pure STLC *)
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
  (* sums *)
  | tm_inl : ty -> tm -> tm
  | tm_inr : ty -> tm -> tm
  | tm_case : tm -> id -> tm -> id -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
  (* lists *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> id -> id -> tm -> tm
          (* i.e., [lcase t1 of | nil -> t2 | x::y -> t3] *)
  (* numbers *)
  | tm_nat : nat -> tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* let *)
  | tm_let : id -> tm -> tm -> tm
          (* i.e., [let x = t1 in t2] *)
  (* fix *)
  | tm_fix  : tm -> tm.

(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing
<<
       if x = 0 then ... else ...
>>
    we'll write this:
<<
       if0 x then ... else ...
>>
*)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
  | Case_aux c "tm_pair" | Case_aux c "tm_fst" | Case_aux c "tm_snd"
  | Case_aux c "tm_inl" | Case_aux c "tm_inr" | Case_aux c "tm_case"
  | Case_aux c "tm_nil" | Case_aux c "tm_cons" | Case_aux c "tm_lcase"
  | Case_aux c "tm_nat" | Case_aux c "tm_succ" | Case_aux c "tm_pred"
  | Case_aux c "tm_mult" | Case_aux c "tm_if0"
  | Case_aux c "tm_let" | Case_aux c "tm_fix" ].

(* ###################################################################### *)
(** *** Substitution *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var y =>
      if beq_id x y then s else t
  | tm_abs y T t1 =>
      tm_abs y T (if beq_id x y then t1 else (subst x s t1))
  | tm_app t1 t2 =>
      tm_app (subst x s t1) (subst x s t2)
  (* FILL IN HERE *)
  | _ => t  (* ... and delete this line *)
  end.

(* ###################################################################### *)
(** *** Reduction *)

(** Next we define the values of our language. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tm_abs x T11 t12)
  (* FILL IN HERE *)
  .

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tm_app t1 t2) ==> (tm_app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tm_app v1 t2) ==> (tm_app v1 t2')
  (* FILL IN HERE *)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
    (* FILL IN HERE *)
  ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(* ###################################################################### *)
(** *** Typing *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 ->
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T1 T2) ->
      has_type Gamma t2 T1 ->
      has_type Gamma (tm_app t1 t2) T2
  (* FILL IN HERE *)
  .

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
    (* FILL IN HERE *)
].

(* ###################################################################### *)
(** ** Examples *)

(** This section presents formalized versions of the examples from
    above (plus several more).  The ones at the beginning focus on
    specific features; you can use these to make sure your definition
    of a given feature is reasonable before moving on to extending the
    proofs later in the file with the cases relating to this feature.
    The later examples require all the features together, so you'll
    need to come back to these when you've got all the definitions
    filled in. *)

Module Examples.

(** *** Preliminaries *)

(** First, let's define a few variable names: *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).
Notation x := (Id 9).
Notation y := (Id 10).
Notation processSum := (Id 11).
Notation n := (Id 12).
Notation eq := (Id 13).
Notation m := (Id 14).
Notation evenodd := (Id 15).
Notation even := (Id 16).
Notation odd := (Id 17).
Notation eo := (Id 18).

(** Next, a bit of Coq hackery to automate searching for typing
    derivations.  You don't need to understand this bit in detail --
    just have a look over it so that you'll know what to look for if
    you ever find yourself needing to make custom extensions to
    [auto].

    The following [Hint] declarations say that, whenever [auto]
    arrives at a goal of the form [(has_type G (tm_app e1 e1) T)], it
    should consider [eapply T_App], leaving an existential variable
    for the middle type T1, and similar for [lcase]. That variable
    will then be filled in during the search for type derivations for
    [e1] and [e2].  We also include a hint to "try harder" when
    solving equality goals; this is useful to automate uses of
    [T_Var] (which includes an equality as a precondition). *)

Hint Extern 2 (has_type _ (tm_app _ _) _) =>
  eapply T_App; auto.
(* You'll want to uncomment the following line once
   you've defined the [T_Lcase] constructor for the typing
   relation: *)
(*
Hint Extern 2 (has_type _ (tm_lcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.
*)
Hint Extern 2 (_ = _) => compute; reflexivity.

(** *** Numbers *)

Module Numtest.

(* if0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
Definition test :=
  tm_if0
    (tm_pred
      (tm_succ
        (tm_pred
          (tm_mult
            (tm_nat 2)
            (tm_nat 0)))))
    (tm_nat 5)
    (tm_nat 6).

(** Remove the comment braces once you've implemented enough of the
    definitions that you think this should work. *)

(*
Example typechecks :
  has_type (@empty ty) test ty_Nat.
Proof.
  unfold test.
  (* This typing derivation is quite deep, so we need to increase the
     max search depth of [auto] from the default 5 to 10. *)
  auto 10.
Qed.

Example numtest_reduces :
  test ==>* tm_nat 5.
Proof.
  unfold test. normalize.
Qed.
*)

End Numtest.

(** *** Products *)

Module Prodtest.

(* ((5,6),7).fst.snd *)
Definition test :=
  tm_snd
    (tm_fst
      (tm_pair
        (tm_pair
          (tm_nat 5)
          (tm_nat 6))
        (tm_nat 7))).

(*
Example typechecks :
  has_type (@empty ty) test ty_Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tm_nat 6.
Proof. unfold test. normalize. Qed.
*)

End Prodtest.

(** *** [let] *)

Module LetTest.

(* let x = pred 6 in succ x *)
Definition test :=
  tm_let
    x
    (tm_pred (tm_nat 6))
    (tm_succ (tm_var x)).

(*
Example typechecks :
  has_type (@empty ty) test ty_Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tm_nat 6.
Proof. unfold test. normalize. Qed.
*)

End LetTest.

(** *** Sums *)

Module Sumtest1.

(* case (inl Nat 5) of
     inl x => x
   | inr y => y *)

Definition test :=
  tm_case (tm_inl ty_Nat (tm_nat 5))
    x (tm_var x)
    y (tm_var y).

(*
Example typechecks :
  has_type (@empty ty) test ty_Nat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tm_nat 5).
Proof. unfold test. normalize. Qed.
*)

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => if0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)

Definition test :=
  tm_let
    processSum
    (tm_abs x (ty_sum ty_Nat ty_Nat)
      (tm_case (tm_var x)
         n (tm_var n)
         n (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))))
    (tm_pair
      (tm_app (tm_var processSum) (tm_inl ty_Nat (tm_nat 5)))
      (tm_app (tm_var processSum) (tm_inr ty_Nat (tm_nat 5)))).

(*
Example typechecks :
  has_type (@empty ty) test (ty_prod ty_Nat ty_Nat).
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tm_pair (tm_nat 5) (tm_nat 0)).
Proof. unfold test. normalize. Qed.
*)

End Sumtest2.

(** *** Lists *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of
     nil => 0
   | x::y => x*x *)

Definition test :=
  tm_let l
    (tm_cons (tm_nat 5) (tm_cons (tm_nat 6) (tm_nil ty_Nat)))
    (tm_lcase (tm_var l)
       (tm_nat 0)
       x y (tm_mult (tm_var x) (tm_var x))).

(*
Example typechecks :
  has_type (@empty ty) test ty_Nat.
Proof. unfold test. eauto 20. Qed.

Example reduces :
  test ==>* (tm_nat 25).
Proof. unfold test. normalize. Qed.
*)

End ListTest.

(** *** [fix] *)

Module FixTest1.

(* fact := fix
             (\f:nat->nat.
                \a:nat.
                   if a=0 then 1 else a * (f (pred a))) *)
Definition fact :=
  tm_fix
    (tm_abs f (ty_arrow ty_Nat ty_Nat)
      (tm_abs a ty_Nat
        (tm_if0
           (tm_var a)
           (tm_nat 1)
           (tm_mult
              (tm_var a)
              (tm_app (tm_var f) (tm_pred (tm_var a))))))).

(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)

(*
Example fact_typechecks :
  has_type (@empty ty) fact (ty_arrow ty_Nat ty_Nat).
Proof. unfold fact. auto 10.
Qed.
*)

(*
Example fact_example:
  (tm_app fact (tm_nat 4)) ==>* (tm_nat 24).
Proof. unfold fact. normalize. Qed.
*)

End FixTest1.

Module FixTest2.

(* map :=
     \g:nat->nat.
       fix
         (\f:[nat]->[nat].
            \l:[nat].
               case l of
               | [] -> []
               | x::l -> (g x)::(f l)) *)
Definition map :=
  tm_abs g (ty_arrow ty_Nat ty_Nat)
    (tm_fix
      (tm_abs f (ty_arrow (ty_List ty_Nat) (ty_List ty_Nat))
        (tm_abs l (ty_List ty_Nat)
          (tm_lcase (tm_var l)
            (tm_nil ty_Nat)
            a l (tm_cons (tm_app (tm_var g) (tm_var a))
                         (tm_app (tm_var f) (tm_var l))))))).

(*
(* Make sure you've uncommented the last [Hint Extern] above... *)
Example map_typechecks :
  has_type empty map
    (ty_arrow (ty_arrow ty_Nat ty_Nat)
      (ty_arrow (ty_List ty_Nat)
        (ty_List ty_Nat))).
Proof. unfold map. auto 10. Qed.

Example map_example :
  tm_app (tm_app map (tm_abs a ty_Nat (tm_succ (tm_var a))))
         (tm_cons (tm_nat 1) (tm_cons (tm_nat 2) (tm_nil ty_Nat)))
  ==>* (tm_cons (tm_nat 2) (tm_cons (tm_nat 3) (tm_nil ty_Nat))).
Proof. unfold map. normalize. Qed.
*)

End FixTest2.

Module FixTest3.

(* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if0 m then (if0 n then 1 else 0)
             else if0 n then 0
             else eq (pred m) (pred n))   *)

Definition equal :=
  tm_fix
    (tm_abs eq (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat))
      (tm_abs m ty_Nat
        (tm_abs n ty_Nat
          (tm_if0 (tm_var m)
            (tm_if0 (tm_var n) (tm_nat 1) (tm_nat 0))
            (tm_if0 (tm_var n)
              (tm_nat 0)
              (tm_app (tm_app (tm_var eq)
                              (tm_pred (tm_var m)))
                      (tm_pred (tm_var n)))))))).

(*
Example equal_typechecks :
  has_type (@empty ty) equal (ty_arrow ty_Nat (ty_arrow ty_Nat ty_Nat)).
Proof. unfold equal. auto 10.
Qed.
*)

(*
Example equal_example1:
  (tm_app (tm_app equal (tm_nat 4)) (tm_nat 4)) ==>* (tm_nat 1).
Proof. unfold equal. normalize. Qed.
*)

(*
Example equal_example2:
  (tm_app (tm_app equal (tm_nat 4)) (tm_nat 5)) ==>* (tm_nat 0).
Proof. unfold equal. normalize. Qed.
*)

End FixTest3.

Module FixTest4.

(* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. if0 n then 1 else eo.snd (pred n) in
              let o = \n:Nat. if0 n then 0 else eo.fst (pred n) in
              (e,o)) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)
*)

Definition eotest :=
  tm_let evenodd
    (tm_fix
      (tm_abs eo (ty_prod (ty_arrow ty_Nat ty_Nat) (ty_arrow ty_Nat ty_Nat))
        (tm_pair
          (tm_abs n ty_Nat
            (tm_if0 (tm_var n)
              (tm_nat 1)
              (tm_app (tm_snd (tm_var eo)) (tm_pred (tm_var n)))))
          (tm_abs n ty_Nat
            (tm_if0 (tm_var n)
              (tm_nat 0)
              (tm_app (tm_fst (tm_var eo)) (tm_pred (tm_var n))))))))
  (tm_let even (tm_fst (tm_var evenodd))
  (tm_let odd (tm_snd (tm_var evenodd))
  (tm_pair
    (tm_app (tm_var even) (tm_nat 3))
    (tm_app (tm_var even) (tm_nat 4))))).

(*
Example eotest_typechecks :
  has_type (@empty ty) eotest (ty_prod ty_Nat ty_Nat).
Proof. unfold eotest. eauto 30.
Qed.
*)

(*
Example eotest_example1:
  eotest ==>* (tm_pair (tm_nat 0) (tm_nat 1)).
Proof. unfold eotest. normalize. Qed.
*)

End FixTest4.

End Examples.

(* ###################################################################### *)
(** ** Properties of Typing *)

(** The proofs of progress and preservation for this system are
    essentially the same (though of course somewhat longer) as for the
    pure simply typed lambda-calculus. *)

(* ###################################################################### *)
(** *** Progress *)

Theorem progress : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    inversion H.
  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tm_abs x T11 t12],
       which is a value. *)
    left...
  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value
       or can take a step. *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that
         [t1 = tm_abs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But
         [(tm_abs x T11 t12) t2 ==> subst x t2 t12] by [ST_AppAbs]. *)
        inversion H; subst; try (solve by inversion).
        exists (subst x t2 t12)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2']
           by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
  (* FILL IN HERE *)
Qed.


(* ###################################################################### *)
(** *** Context Invariance *)

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
  (* FILL IN HERE *)
  .

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case;
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. remember (beq_id x y) as e.
    destruct e...
  (* FILL IN HERE *)
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx.
    apply not_eq_beq_id_false in H2. rewrite H2 in Hctx...
  (* FILL IN HERE *)
Qed.

(* ###################################################################### *)
(** *** Preservation *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma (subst x v t) S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then
     Gamma |- (subst x v t) S. *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tm_var and tm_abs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  tm_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tm_var".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- subst x v y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [subst x v y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      apply beq_id_eq in Heqe. subst.
      unfold extend in H1. rewrite <- beq_id_refl in H1.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite <- Heqe in H1...
  Case "tm_abs".
    rename i into y. rename t into T11.
    (* If [t = tm_abs y T11 t0], then we know that
         [Gamma,x:U |- tm_abs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma,
         [Gamma,x:U |- t0 : S -> Gamma |- subst x v t0 S].

       We can calculate that
         subst x v t = tm_abs y T11 (if beq_id x y
                                      then t0
                                      else subst x v t0)
       And we must show that [Gamma |- subst x v t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else subst x v t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- subst x v t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
  (* FILL IN HERE *)
Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  has_type_cases (induction HT) Case;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and
       [ST_AppAbs]. In the first two cases, the result follows directly from
       the IH. *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose
           [t1 = tm_abs x T11 t12]
         and
           [t2 = v2].
         We must show that [empty |- subst x v2 t12 : T2].
         We know by assumption that
             [empty |- tm_abs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  (* FILL IN HERE *)
Qed.
(** [] *)

End STLCExtended.

