(** * Types_J: 型システム *)
(* * Types: Type Systems *)

(* $Date: 2011-06-03 13:58:55 -0400 (Fri, 03 Jun 2011) $ *)


Require Export Smallstep_J.

(* Our next topic, a large one, is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of a very simple
    language with just booleans and numbers, to introduce the basic
    ideas of types, typing rules, and the fundamental theorems about
    type systems: _type preservation_ and _progress_.  Then we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq). *)
(**
   次に取り組むのは大きなもので、型システムです。型システムは、式をその評価結果の「かたち」で分類する静的解析手法です。まずは、ブール値と数のみから成る言語から始め、型に関する基本的な考え方や型付け規則、型保存（type preservation）や進行（progress）といった型システムに関する基礎的な定理を導入します。その次に単純型付きラムダ計算に移ります。単純型付きラムダ計算は（Coq を含む）近代的な関数型プログラミング言語すべての中心概念になっています。
*)

(* ###################################################################### *)
(* * More Automation *)
(** * さらに自動化 *)

(* Before we start, let's spend a little time learning to use
    some of Coq's more powerful automation features... *)
(**
   型システムの話を始める前に、 Coq の強力な自動化機能の勉強に時間を割くことにしましょう。
   *)

(* ###################################################################### *)
(* ** The [auto] and [eauto] Tactics *)
(** ** [auto] と [eauto] タクティック *)

(* The [auto] tactic solves goals that are solvable by any combination of
     - [intros],
     - [apply] (with a local hypothesis, by default), and
     - [reflexivity].

    The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]. *)
(**
   [auto] タクティックを使うと
   - [intros]
   - [apply] （特に指定しなければ、コンテキストにある補題のみを使う）
   - [reflexivity]
   を組み合わせて解くことのできるゴールを解くことができます。

   [eauto] タクティックは [auto] とほとんど同じですが、 [apply] の代わりに [eapply] を使います。
   *)

(* Using [auto] is always "safe" in the sense that it will never fail
    and will never change the proof state: either it completely solves
    the current goal, or it does nothing.

    Here is a contrived example: *)

(**
   [auto] は失敗することはなく、証明の状態を変更しない、すなわち、現在のゴールを完全に解くか、何もしない、という意味で常に「安全」です。

   わざとらしい例ですが試してみましょう。
   *)

Lemma auto_example_1 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(* When searching for potential proofs of the current goal, [auto]
    and [eauto] consider the hypotheses in the current context
    together with a _hint database_ of other lemmas and constructors.
    Some of the lemmas and constructors we've already seen -- e.g.,
    [conj], [or_introl], and [or_intror] -- are installed in this hint
    database by default. *)
(**
   現在のゴールに対して可能な証明を探索する場合、 [auto] や [eauto] は現在のコンテキストにある補題だけでなく、他の補題や構成子を登録したヒントデータベースを使います。これまでに出てきた補題や構成子のうち [conj] や [or_introl]、 [or_intror] といった、いくつかのものは特に設定しなくてもヒントデータベースに登録されています。
   *)

Lemma auto_example_2 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.

(* We can extend the hint database just for the purposes of one
    application of [auto] or [eauto] by writing [auto using ...].
    E.g., if [conj], [or_introl], and [or_intror] had _not_ already
    been in the hint database, we could have done this instead: *)
(**
   ある場所で [auto] や [eauto] を適用するとき、その時にだけヒントデータベースを拡張したい場合には [auto using ...] のようにして拡張することができます。例えば、 [conj] や [or_introl]、 [or_intror] がヒントデータベースに登録されていない場合でも、下のように書けば同じ意味になります。
   *)

Lemma auto_example_2a : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror.  Qed.

(* Of course, in any given development there will also be some of our
    own specific constructors and lemmas that are used very often in
    proofs.  We can add these to the global hint database by writing
[[
      Hint Resolve l.
]]
    at the top level, where [l] is a top-level lemma theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication).  As a shorthand, we can write
[[
      Hint Constructors c.
]]
    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add
[[
      Hint Unfold d.
]]
    where [d] is a defined symbol, so that [auto] knows to expand
    uses of [d] and enable further possibilities for applying
    lemmas that it knows about. *)
(**
   もちろん、それぞれの場合ごとに、自分で定義した構成子や補題のうちに証明で非常によく使うものがある、ということもあるでしょう。トップレベルに次のように書けば、そのような構成子や補題を大域的なヒントデータベースに登録することができます。
[[
      Hint Resolve l.
]]
   ここで、 [l] は、補題や定理、もしくは帰納的に定義された命題（すなわち、型が含意であるようなもの）です。略記法として
[[
      Hint Constructors c.
]]
   と書くと、 [c] の帰納的定義からすべての構成子を取り出し [Hint Resolve] します。

   また、
[[
      Hint Unfold d.
]]
   として（[d] は定義済みのシンボルです）、 [auto] で [d] を使っている部分を展開し、そこからさらに登録された補題を [apply] していけるようにしておく必要があることもあります。
   *)

(* Here are some [Hint]s we will find useful. *)
(** あとで役に立ちそうな [Hint] をいくつか登録しておきます。 *)

Hint Constructors refl_step_closure.
Hint Resolve beq_id_eq beq_id_false_not_eq.

(* Warning: Just as with Coq's other automation facilities, it is
    easy to overuse [auto] and [eauto] and wind up with proofs that
    are impossible to understand later!

    Also, overuse of [eauto] can make proof scripts very slow.  Get in
    the habit of using [auto] most of the time and [eauto] only when
    necessary.

    For much more detailed information about using [auto] and [eauto],
    see the chapter [UseAuto.v]. *)
(**
   注意: Coq の他の自動化機能と同じく、 [auto] や [eauto] を使い過ぎると、簡単に、後で読めないような証明になってしまいます！

   また、 [eauto] を使い過ぎると、証明スクリプトが非常に遅くなることがあります。 [auto] を使うのを常の習慣とし、 [eauto] は必要なときにだけ使うようにしましょう。

   [auto] や [eauto] の使い方について、より詳しくは [UseAuto_J.v] の章を参照してください。
   *)

(* ###################################################################### *)
(* ** The [Proof with] Tactic *)
(** ** [Proof with] タクティック *)

(* If you start a proof by saying [Proof with (tactic)] instead of
     just [Proof], then writing [...] instead of [.] after a tactic in
     the body of the proof will try to solve all generated subgoals
     with [tactic] (and fail if this doesn't work).

     One common use of this facility is "[Proof with auto]" (or
     [eauto]).  We'll see many examples of this later in the file. *)
(**
   証明の最初の部分を [Proof] ではなく [Proof with (tactic)]で始めると、証明の本体部分でタクティックの後に [.] の代わりに [...] と書くことで、そのタクティックで生成されたサブゴールすべてを [tactic] で解くようにすることができます（解けなかった場合には失敗します）。

   この機能の一般的な使い方は [Proof with auto] （または [eauto]）です。このファイルの後の方でこの使い方の例がいくつかあります。
   *)

(* ###################################################################### *)
(* ** The [solve by inversion] Tactic *)
(** ** [solve by inversion] タクティック *)

(* Here's another nice automation feature: it often arises that the
    context contains a contradictory assumption and we want to use
    [inversion] on it to solve the goal.  We'd like to be able to say
    to Coq, "find a contradictory assumption and invert it" without
    giving its name explicitly.

    Doing [solve by inversion] will find a hypothesis that can be
    inverted to solve the goal, if there is one.  The tactics [solve
    by inversion 2] and [solve by inversion 3] are slightly fancier
    versions which will perform two or three inversions in a row, if
    necessary, to solve the goal.

    (These tactics are not actually built into Coq -- their
    definitions are in [Sflib.v].)

    Caution: Overuse of [solve by inversion] can lead to slow proof
    scripts. *)
(** 他にも便利な自動化機能があります。コンテキストに矛盾する仮定があり、それを [inversion] することでサブゴールを解く、というのはよくあることです。このとき、 Coq に名前を指定せずに、「矛盾する仮定を見つけ、それを [inversion] しろ」と言いたいところです。

    [solve by intersion] すると、ゴールを解くために [inversion] できる補題がひとつある場合に、それを見つけてくれます。 [solve by inversion 2] や [solve by inversion 3] はもう少し気のきいたもので、ゴールを解くのに必要であれば 2 回、3 回と [inversion] を繰り返してくれます。

    （[solve by inversion] は Coq 組み込みのものではなく [Sflib_J.v] で定義されています。）

    注意: [solve by inversion] を使い過ぎると、証明スクリプトが遅くなることがあります。
    *)

(* ###################################################################### *)
(* ** The [try solve] Tactic *)
(** ** [try solve] タクティック *)

(* If [t] is a tactic, then [try solve [t]] is a tactic that
      - if [t] solves the goal, behaves just like [t], or
      - if [t] cannot completely solve the goal, does
        nothing.

    More generally, [try solve [t1 | t2 | ...]] will try to solve the
    goal by using [t1], [t2], etc.  If none of them succeeds in
    completely solving the goal, then [try solve [t1 | t2 | ...]] does
    nothing.

    The fact that it does nothing when it doesn't completely succeed
    in solving the goal means that there is no harm in using [try
    solve T] in situations where [T] might actually make no sense.  In
    particular, if we put it after a [;] it will solve as many
    subgoals as it can and leave the rest for us to solve by other
    methods.  It will not leave any of the subgoals in a partially
    solved state. *)
(** [t] がタクティックであるとき [try solve [t]] は以下のようなタクティックになります。
      - [t] がゴールを解けるとき [t] と同じように振る舞う。
      - [t] がゴールを完全に解けなかった場合には何もしない。

    より一般的には、 [try solve [t1 | t2 | ...]] は [t1]、 [t2]、……を使ってゴールを解こうとします。いずれを使ってもゴールを完全に解くことができなかった場合には何もしません。

    ゴールを完全に解くことができなかった場合には何もしないということは、 [T] が実際には何の意味もないような場合に [try solve T] しても何の害もないということです。特に、 [;] の後に [try solve T] すると [T] で解けるサブゴールをできるかぎり解き、残りは別の方法で解く、ということができます。このタクティックでは、サブゴールが解きかけの状態のまま残るということはありません。
    *)

(* ###################################################################### *)
(* ** The [f_equal] Tactic *)
(** ** [f_equal] タクティック *)

(* This handy tactic replaces a goal of the form [f x1 x2 ... xn = f
    y1 y2 ... yn], where [f] is some function, with the subgoals [x1 =
    y1], [x2 = y2],...,[xn = yn].  It is useful for avoiding explicit
    rewriting steps, and often the generated subgoals can be quickly
    cleared by [auto]. *)
(** [f_equal] タクティックを使うと、ある関数 [f] について、 [f x1 x2 ... xn = f y1 y2 ... yn] のかたちのサブゴールを [x1 = y1]、 [x2 = y2]、……、 [xn = yn] で置き換えます。こうすることで手でわざわざ書き換えをしなくて済みますし、多くの場合、こうして生成されたサブゴールは [auto] で片付けることができます。
   *)

(* ###################################################################### *)
(* ** The [normalize] Tactic *)
(** ** [normalize] タクティック *)

(* When experimenting with definitions of programming languages in
    Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are simple but repetitive to do by hand. Consider for
    example reducing an arithmetic expression using the small-step
    relation [astep] defined in the previous chapter: *)
(**
   Coq でプログラミング言語の定義を扱っていると、ある具体的な項がどのように簡約されるか知りたいことがよくあります。 [t ==>* t'] という形のゴールを、 [t] が具体的な項で [t'] が未知の場合に証明するときです。このような証明は単純ですが、手でやるには繰り返しが多過ぎます。例えば、前章で定義した、スモールステップ簡約の関係 [astep] を使って算術式を簡約することを考えてみてください。
   *)

Definition astep_many st := refl_step_closure (astep st).
Notation " t '/' st '==>a*' t' " := (astep_many st t t')
  (at level 40, st at level 39).

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  apply rsc_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply rsc_step with (ANum 15).
    apply AS_Plus.
  apply rsc_refl.
Qed.

(* We repeatedly applied [rsc_step] until we got to a normal
    form. The proofs that the intermediate steps are possible are
    simple enough that [auto], with appropriate hints, can solve
    them. *)
(**
   正規形になるまで [rsc_step] を繰り返し適用します。証明の途中に出てくる部分は、適切なヒントを与えてやれば [auto] で解けそうです。
   *)

Hint Constructors astep aval.
Example astep_example1' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  eapply rsc_step. auto. simpl.
  eapply rsc_step. auto. simpl.
  apply rsc_refl.
Qed.

(* The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each [rsc_step] we print out the
    current goal, so that the user can follow how the term is being
    evaluated. *)
(**
   下の [Tactic Notation] 定義はこのパターンを表現したものです。それに加えて、 [rsc_step] を実行する前にゴールを表示します。これは、項がどのように評価されるか利用者が追えるようにするためです。
   *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply rsc_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply rsc_refl.

Example astep_example1'' :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows
     a trace of how the expression evaluated. *)
  (* 証明スクリプトのこの部分で、 Coq は式の評価のトレースを表示する。
    *)
Qed.

(* Finally, this is also useful as a simple way to calculate what the normal
    form of a term is, by proving a goal with an existential variable in it. *)
(** またさらに、ゴールに存在量化された変数を入れて証明し、ある項の正規形を計算する、という使い方もあります。
   *)

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

(* ###################################################################### *)
(* * Typed Arithmetic Expressions *)
(** * 型付きの算術式 *)

(* To motivate the discussion of type systems, let's begin as usual
    with an extremely simple toy language.  We want it to have the
    potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in [Smallstep.v]:
    a single kind of data (just numbers) is too simple, but just two
    kinds (numbers and booleans) already gives us enough material to
    tell an interesting story.

    The language definition is completely routine.  The only thing to
    notice is that we are _not_ using the [asnum]/[aslist] trick that
    we used in [ImpList.v] to make all the operations total by
    forcibly coercing the arguments to [+] (for example) into numbers.
    Instead, we simply let terms get stuck if they try to use an
    operator with the wrong kind of operands: the [step] relation
    doesn't relate them to anything. *)
(**
   型システムについての議論を始めるために、例のごとく、ごく単純な言語から始めましょう。この言語は、実行時の型エラーで「まずいことが起きる」可能性のあるものであってほしいので、 [Smallstep_J.v] で使った、定数のと足し算だけの言語よりはもう少し複雑なものでなければなりません。データが一種類だけ（数のみ）では単純すぎますが、二種類（数とブール値）なら、実験のための材料はもう揃っています。

   言語の定義はいつも通り、お決まりの作業です。注意が必要なのは、 [ImpList.v] で [+] 等の引数を [asnum] や [aslist] を使って強制型変換してすべての操作を全射にしたようなテクニックは使わないということです。その代わりに、演算子をまちがった種類の被演算子に適用した場合には単にその項で行き詰まる（stuck）ことにします。すなわち、 [step] 関係では、そのような項を何とも関連づけません。
   *)

(* ###################################################################### *)
(* ** Syntax *)
(** ** 構文 *)

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

(* ###################################################################### *)
(* ** Small-Step Reduction *)
(** ** スモールステップ簡約 *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tm_succ t1) ==> (tm_succ t1')
  | ST_PredZero :
      (tm_pred tm_zero) ==> tm_zero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tm_pred (tm_succ t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tm_pred t1) ==> (tm_pred t1')
  | ST_IszeroZero :
      (tm_iszero tm_zero) ==> tm_true
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tm_iszero (tm_succ t1)) ==> tm_false
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tm_iszero t1) ==> (tm_iszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

(* Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  For example, the term [tm_succ tm_true] cannot take
    a step, but the almost-as-obviously-nonsensical term
[[
    tm_succ (tm_if tm_true tm_true tm_true)
]]
    can. *)
(**
   [step] 関係は式が大域的に意味を持つかは考慮せず、次の簡約が適切な種類の被演算子に適用されているかだけを確認していることに注意してください。例えば、 [tm_succ tm_true] は先に進むことはできませんが、ほぼ意味のないことが自明な項
[[
    tm_succ (tm_if tm_true tm_true tm_true)
]]
   は大丈夫なのです。
   *)

(* ###################################################################### *)
(* ** Normal Forms and Values *)
(** ** 正規形と値 *)

(* The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)
(**
   この言語の [step] 関係について、まず注目に値するのは、 [Smallstep_J.v] の章の strong progress theorem が成り立たないということです。すなわち、正規形ではあるのに（これ以上簡約できないのに）、値ではない項があるのです。（これは、そのような項を可能な「評価結果」と定義しなかったからです。）そのような項は [stuck] します。
   *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* **** Exercise: 2 stars, optional (some_tm_is_stuck) *)
(** **** 練習問題: ★★, optional (some_tm_is_stuck) *)
Example some_tm_is_stuck :
  exists t, stuck t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)
(**
   ただし、この言語では値の集合と正規形の集合は同一ではありませんが、値は正規形に含まれます。これは重要なことで、さらに簡約できる値を定義しまうことはできないことを表しています。
   *)

(* **** Exercise: 3 stars, optional (value_is_nf) *)
(** **** 練習問題: ★★★, optional (value_is_nf) *)
(* Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)
(**
   ヒント: 証明中で、数値であることがわかっている項に対して帰納的推論をしなければならないことになります。この帰納法は、その項自体にして適用することもできますし、その項が数値であるという事実に対して適用することもできます。どちらでも証明は進められますが、片方はもう片方よりもかなり短かくなります。練習として、ふたつの方法両方で証明を完成させなさい。
   *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, optional (step_deterministic) *)
(** **** 練習問題: ★★★, optional (step_deterministic) *)
(* Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)
(**
   [value_is_nf] を使うと、 [step] 関係もまた決定的であることが示せます。
   *)

Theorem step_deterministic:
  partial_function step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* ** Typing *)
(** ** 型付け *)

(* The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)
(** 次にこの言語から見て取れる非常に重要なことは、行き詰まる項があったとしても、そのような項は、我々としても意味を持ってほしくないようなブール値と数の取り混ぜ方をしたもので、すべて「意味がない」ということです。項とその評価結果の型（数かブール値）を関係づける型付け関係を定義することでそのような型の正しくない項を除くことができます。
   *)

Inductive ty : Type :=
  | ty_Bool : ty
  | ty_Nat : ty.

(* The typing relation: *)
(** 型付け関係: *)

(* In informal notation, the typing relation is often written [|- t :
    T], pronounced "[t] has type [T]."  The [|-] symbol is called a
    "turnstile".  (Below, we're going to see richer typing relations
    where an additional "context" argument is written to the left of
    the turnstile.  Here, the context is always empty.)
[[[
                            --------------                             (T_True)
                            |- true : Bool

                           ---------------                            (T_False)
                           |- false : Bool

                |- t1 : Bool    |- t2 : T    |- t3 : T
                --------------------------------------                   (T_If)
                     |- if t1 then t2 else t3 : T

                              ----------                               (T_Zero)
                              |- 0 : Nat

                             |- t1 : Nat
                           ----------------                            (T_Succ)
                           |- succ t1 : Nat

                             |- t1 : Nat
                           ----------------                            (T_Pred)
                           |- pred t1 : Nat

                             |- t1 : Nat
                         -------------------                         (T_IsZero)
                         |- iszero t1 : Bool
]]]
*)
(**
   非形式的な記法では、型付け関係は [|- t : T] と書き、「[t] の型は [T] である」と読みます。記号 [|-] は「ターンスタイル（turnstile）」の呼ばれます。（先の節ではターンスタイルの左側に追加の「コンテキスト」引数のある型付け関係もあります。ここでは、コンテキストは常に空です。）
[[
                            --------------                             (T_True)
                            |- true : Bool

                           ---------------                            (T_False)
                           |- false : Bool

                |- t1 : Bool    |- t2 : T    |- t3 : T
                --------------------------------------                   (T_If)
                     |- if t1 then t2 else t3 : T

                              ----------                               (T_Zero)
                              |- 0 : Nat

                             |- t1 : Nat
                           ----------------                            (T_Succ)
                           |- succ t1 : Nat

                             |- t1 : Nat
                           ----------------                            (T_Pred)
                           |- pred t1 : Nat

                             |- t1 : Nat
                         -------------------                         (T_IsZero)
                         |- iszero t1 : Bool
]]
*)

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       has_type tm_true ty_Bool
  | T_False :
       has_type tm_false ty_Bool
  | T_If : forall t1 t2 t3 T,
       has_type t1 ty_Bool ->
       has_type t2 T ->
       has_type t3 T ->
       has_type (tm_if t1 t2 t3) T
  | T_Zero :
       has_type tm_zero ty_Nat
  | T_Succ : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_succ t1) ty_Nat
  | T_Pred : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_pred t1) ty_Nat
  | T_Iszero : forall t1,
       has_type t1 ty_Nat ->
       has_type (tm_iszero t1) ty_Bool.


Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(* *** Examples *)
(** *** 例 *)

(* It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)
(**
   型付け関係というのは保守的な（または静的な）近似であり、項の正規形の型を計算しているわけではない、ということをよく理解しておいてください。
   *)

Example has_type_1 :
  has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_Nat.
Proof.
  apply T_If.
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.
Qed.
(* (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)
(**
   （型付け関係のすべての構成子をヒントデータベースに登録してあるので、実際には [auto] でこの証明を自動化することができます。）
   *)

Example has_type_not :
  ~ has_type (tm_if tm_false tm_zero tm_true) ty_Bool.
Proof.
  intros Contra. solve by inversion 2.  Qed.

(* **** Exercise: 1 star (succ_hastype_nat__hastype_nat) *)
(** **** 練習問題: ★ (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  has_type (tm_succ t) ty_Nat ->
  has_type t ty_Nat.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* ** Progress *)
(** ** 進行 *)

(* The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)
(**
   型付け関係には重要な性質かふたつあります。最初のものは、型のついた（well-typed）正規形は値である（行き詰まらない）、ということです。
   *)

(* **** Exercise: 3 stars, recommended (finish_progress_informal) *)
(** **** 練習問題: ★★★, recommended (finish_progress_informal) *)
(* Complete the following proof: *)
(** 次の証明を完成させなさい。 *)

(* _Theorem_: If [|- t : T], then either [t] is a value or else
    [t ==> t'] for some [t'].

    _Proof_: By induction on a derivation of [|- t : T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 : Bool], [|- t2 : T] and [|- t3
        : T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].

            - If [t1] is a value, then it is either an [nvalue] or a
              [bvalue].  But it cannot be an [nvalue], because we know
              [|- t1 : Bool] and there are no rules assigning type
              [Bool] to any term that could be an [nvalue].  So [t1]
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].

    (* FILL IN HERE *)
[]
*)
(** 定理: [|- t : T] であれば、 [t] は値であるか、さもなければある [t'] に対して [t ==> t'] である。

    証明: [|-t : T] の導出に関する帰納法で証明する。

      - 導出で直前に適用した規則が [T_If] である場合、 [t = if t1 then t2 else t3] かつ、 [|- t1 : Bool]、 [|- t2 : T] かつ [|- t3 : T] である。帰納法の仮定から、 [t1] が値であるか、さもなければ [t1] が何らかの [t1'] に簡約できる。

            - [t1] が値のとき、 [t1] は [nvalue] か [bvalue] である。だが、 [|- t1 : Bool] かつ、 [nvalue] なる項に [Bool] 型を割り当てる規則はないため、 [t1] は [nvalue] ではない。したがって、 [t1] は [bvalue] である。すなわち、 [true] または [false] である。 [t1 = true] のとき、 [ST_IfTrue] より [t] は [t2] に簡約され、 [t1 = false] のときは [ST_IfFalse] から [t] は [t3] に簡約される。どちらの場合も [t] の簡約は進められる。これが示そうとしていたことである。

            - [t1] 自体が [ST_If] で簡約できるとき、 [t] もまた簡約できる。

    (* FILL IN HERE *)
[]
*)

(* **** Exercise: 3 stars (finish_progress) *)
(** **** 練習問題: ★★★ (finish_progress) *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  (* T_True や T_False のような、値であることが明らかな場合は [auto] で片付けられる。
    *)
  Case "T_If".
    right. destruct IHHT1.
    SCase "t1 is a value". destruct H.
      SSCase "t1 is a bvalue". destruct H.
        SSSCase "t1 is tm_true".
          exists t2...
        SSSCase "t1 is tm_false".
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2.  (* on H and HT1 *)
    SCase "t1 can take a step".
      destruct H as [t1' H1].
      exists (tm_if t1' t2 t3)...
  (* FILL IN HERE *) Admitted.
(** [] *)

(* This is more interesting than the strong progress theorem that we
    saw in the Smallstep chapter, where _all_ normal forms were
    values.  Here, a term can be stuck, but only if it is ill
    typed. *)
(**
   この定理は [Smallstep_J.v] の章の強進行性定理よりも興味深いものです。 [Smallstep_J.v] のものは正規形はすべて値でしたが、本章では項は行き詰まることがありますが、行き詰まるようなものは型のつかないものだけです。
   *)

(* **** Exercise: 1 star (step_review) *)
(** **** 練習問題: ★ (step_review) *)
(* Quick review.  Answer _true_ or _false_.  (As usual, no need to
    hand these in.)
      - In this language, every well-typed normal form is a value.

      - Every value is a normal form.

      - The single-step evaluation relation is
        a partial function.

      - The single-step evaluation relation is a _total_ function.

*)
(** おさらい: 「はい」か「いいえ」（true か false）で答えなさい。（提出の必要はありません。）
      - この言語では、型のついた正規形はすべて値である。

      - 値はすべて正規形である。

      - ワンステップ評価関係は全域関数である。
   *)
(** [] *)

(* ###################################################################### *)
(* ** Type Preservation *)
(** ** 型保存 *)

(* The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)
(**
   型付けの第二の重要な性質は、型のついた項を一段階簡約すると、簡約結果もまた型のつく項である、ということです。

   この定理は subject reduction 性と呼ばれることが多々あります。これは、この定理が型付け関係の subject が簡約されるときに起こることについて言っているからです。この用語は型付けを文として見たことによるもので、項が主語（subject）、型が述語（predicate）に当たります。
   *)

(* **** Exercise: 3 stars, recommended (finish_preservation_informal) *)
(** **** 練習問題: ★★★, recommended (finish_preservation_informal) *)
(* Complete the following proof: *)
(** 以下の証明を完成させなさい。 *)

(* _Theorem_: If [|- t : T] and [t ==> t'], then [|- t' : T].

    _Proof_: By induction on a derivation of [|- t : T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 : Bool], [|- t2 : T] and [|- t3
        : T].

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 : T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 : T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 : Bool] so,
             by the IH, [|- t1' : Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 : T], as required.

    (* FILL IN HERE *)
[]
*)
(**
   定理: [|- t : T] かつ [t ==> t'] ならば [|- t' : T]

   証明: [|- t : T] の導出に関する帰納法で証明する。

      - 導出で直前に使った規則が [T_If] の場合、 [t = if t1 then t2 else t3]、かつ [|- t1 : Bool], [|- t2 : T] かつ [|- t3 : T] である。

        [t] が [if ...] の形式であることとスモールステップ簡約関係を見ると、 [t ==> t'] を示すために使えるのは [ST_IfTrue]、 [ST_IfFalse] または [ST_If] のみである。

           - 直前の規則が [ST_IfTrue] の場合、 [t' = t2] である。 [|- t2 : T] であるのでこれは求める結果である。

           - 直前の規則が [ST_IfFalse] の場合、 [t' = t3] である。 [|- t3 : T] であるのでこれは求める結果である。

           - 直前の規則が [ST_If] の場合、 [t' = if t1' then t2 else t3'] である。ここで、 [t1 ==> t1'] である。 [|- t1 : Bool] であるので、帰納法の仮定から [|- t1' : Bool] である。また、 [T_If] 規則から [|- if t1' then t2 else t3 : T] であり、これは求める結果である。
           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 : Bool] so,
             by the IH, [|- t1' : Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 : T], as required.

    (* FILL IN HERE *)
[]
*)

(* **** Exercise: 2 stars (finish_preservation) *)
(** **** 練習問題: ★★ (finish_preservation) *)
Theorem preservation : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (preservation_alternate_proof) *)
(** **** 練習問題: ★★★ (preservation_alternate_proof) *)
(* Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)
(**
   さらに、同一の性質を型付けの導出ではなく、評価の導出に関する帰納法で証明しなさい。先ほどの証明の最初数行を注意深く読んで考え、各行が何をしているのか理解することから始めましょう。この証明でも設定はよく似ていますが、まったく同じというわけではありません。
   *)

Theorem preservation' : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* ** Type Soundness *)
(** ** 型の健全性 *)

(* Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)
(**
   進行と型保存を合わせると、型のついた項は決して [stuck] 状態にはならないことを示せます。
   *)

Definition stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  has_type t T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.

(* Indeed, in the present -- extremely simple -- language,
    every well-typed term can be reduced to a normal form: this is the
    normalization property.  (The proof is straightforward, though
    somewhat tedious.) In richer languages, this property often fails,
    though there are some interesting languages (such as Coq's
    [Fixpoint] language, and the simply typed lambda-calculus, which
    we'll be looking at next) where all _well-typed_ terms can be
    reduced to normal forms.  *)
(* @TODO 訳語 *)
(**
   実際、現在の（本当に単純な）言語では、型のついた項はすべて正規形に簡約されます。これを normalization property と言います。（証明は単純ですが面倒です。）より言語機能の豊富な言語ではこの性質は満たされないことも多々ありますが、型のついた項がすべて正規形に簡約される言語もあります。（例えば、 Coq の [Fixpoint] 言語や、次の章で見る単純型付きラムダ計算等。）
   *)

(* ###################################################################### *)
(* ** Additional Exercises *)
(** ** 追加演習 *)

(* **** Exercise: 2 stars, recommended (subject_expansion) *)
(** **** 練習問題: ★, recommended (subject_expansion) *)
(* Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [has_type t' T], then [has_type t T]?  If so, prove it.  If
    not, give a counter-example.

    (* FILL IN HERE *)
[]
*)
(** subject reduction 性を見ると、その逆の性質、 subject expansion 性も成り立つかどうか考えるのが合理的でしょう。すなわち、 [t ==> t'] かつ [has_type t' T] ならば [has_type t T] は常に成り立つでしょうか。そうだと思うのなら、証明しなさい。そうでないと思うのなら、反例を挙げなさい。

    (* FILL IN HERE *)
[]
   *)

(* **** Exercise: 2 stars (variation1) *)
(** **** 練習問題: ★★ (variation1) *)
(* Suppose we add the following two new rules to the evaluation
    relation:
[[
      | ST_PredTrue :
           (tm_pred tm_true) ==> (tm_pred tm_false)
      | ST_PredFalse :
           (tm_pred tm_false) ==> (tm_pred tm_true)
]]
   Which of the following properties remain true in the presence
   of these rules?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)
(**
   評価関係に次のふたつの規則を追加するとします。
[[
      | ST_PredTrue :
           (tm_pred tm_true) ==> (tm_pred tm_false)
      | ST_PredFalse :
           (tm_pred tm_false) ==> (tm_pred tm_true)
]]
   以下の性質のうち、この規則を足しても依然として真であるのはどれでしょう。それぞれについて、「真のままである」か「偽になる」を書きなさい。性質が偽になる場合には反例を挙げなさい。
      - [step] の決定性

      - 型のついた項に対する [step] の正規形

      - 進行

      - 型保存

[]
*)

(* **** Exercise: 2 stars (variation2) *)
(** **** 練習問題: ★★ (variation2) *)
(* Suppose, instead, that we add this new rule to the typing relation:
[[
      | T_IfFunny : forall t2 t3,
           has_type t2 ty_Nat ->
           has_type (tm_if tm_true t2 t3) ty_Nat
]]
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)
(**
   先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
[[
      | T_IfFunny : forall t2 t3,
           has_type t2 ty_Nat ->
           has_type (tm_if tm_true t2 t3) ty_Nat
]]
   以下のうち、この規則を足しても依然として真であるのはどれでしょう。（上と同じスタイルで答えなさい。）

      - [step] の決定性

      - 型のついた項に対する [step] の正規形

      - 進行

      - 型保存
[]
*)

(* **** Exercise: 2 stars (variation3) *)
(** **** 練習問題: ★★ (variation3) *)
(* Suppose, instead, that we add this new rule to the typing relation:
[[
      | T_SuccBool : forall t,
           has_type t ty_Bool ->
           has_type (tm_succ t) ty_Bool
]]
   Which of the following properties remain true in the presence of
   this rule?  (Answer in the same style as above.)
      - Determinacy of [step]

      - Normalization of [step] for well-typed terms

      - Progress

      - Preservation

[]
*)
(**
   先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。
[[
      | T_SuccBool : forall t,
           has_type t ty_Bool ->
           has_type (tm_succ t) ty_Bool
]]
   以下のうち、この規則を足しても依然として真であるのはどれでしょう。（上と同じスタイルで答えなさい。）

      - [step] の決定性

      - 型のついた項に対する [step] の正規形

      - 進行

      - 型保存
[]
*)

(* **** Exercise: 2 stars (variation4) *)
(** **** 練習問題: ★★ (variation4) *)
(* Suppose, instead, that we add this new rule to the [step] relation:
[[
      | ST_Funny1 : forall t2 t3,
           (tm_if tm_true t2 t3) ==> t3
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
(**
   先程の問題とは別に、次の規則を [step] 関係に追加したとしましょう。
[[
      | ST_Funny1 : forall t2 t3,
           (tm_if tm_true t2 t3) ==> t3
]]
   上の性質のうち、この規則を足すと偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[]
*)

(* **** Exercise: 2 stars (variation5) *)
(** **** 練習問題: ★★ (variation5) *)
(* Suppose instead that we add this rule:
[[
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tm_if t1 t2 t3) ==> (tm_if t1 t2' t3)
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tm_if t1 t2 t3) ==> (tm_if t1 t2' t3)
]]
   上の性質のうち、この規則を足すと偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[]
*)

(* **** Exercise: 2 stars (variation6) *)
(** **** 練習問題: ★★ (variation6) *)
(* Suppose instead that we add this rule:
[[
      | ST_Funny3 :
          (tm_pred tm_false) ==> (tm_pred (tm_pred tm_false))
]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | ST_Funny3 :
          (tm_pred tm_false) ==> (tm_pred (tm_pred tm_false))
]]
   上の性質のうち、この規則を足すと偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[]
*)

(* **** Exercise: 2 stars (variation7) *)
(** **** 練習問題: ★★ (variation7) *)
(* Suppose instead that we add this rule:
   [[
      | T_Funny4 :
            has_type tm_zero ty_Bool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | T_Funny4 :
            has_type tm_zero ty_Bool
]]
   上の性質のうち、この規則を足すと偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[]
*)

(* **** Exercise: 2 stars (variation8) *)
(** **** 練習問題: ★★ (variation8) *)
(* Suppose instead that we add this rule:
   [[
      | T_Funny5 :
            has_type (tm_pred tm_zero) ty_Bool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
(**
   先程の問題とは別に、次の規則を追加したとしましょう。
[[
      | T_Funny5 :
            has_type (tm_pred tm_zero) ty_Bool
]]
   上の性質のうち、この規則を足すと偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

[]
*)

(* **** Exercise: 3 stars, optional (more_variations) *)
(** **** 練習問題: ★★★, optional (more_variations) *)
(* Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    []
*)
(**
   上の問題と同様の練習問題を自分で作りなさい。さらに、上の性質を選択的に成り立たなくする方法、すなわち、上の性質のうちひとつだけを成り立たなるするよう定義を変数する方法を探しなさい。
   []
   *)

(* **** Exercise: 1 star (remove_predzero) *)
(** **** 練習問題: ★ (remove_predzero) *)
(* The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of
    zero to be undefined, rather than being defined to be zero.
    Can we achieve this simply by removing the rule from the
    definition of [step]?

(* FILL IN HERE *)
[]
*)
(* [E_PredZero] には少し直感に反するところがあります。 0 の前者を 0 と定義するよりは、未定義であるとした方が意味があるように感じられるでしょう。これは [step] の定義から [E_PredZero] を取り除くだけで実現できるでしょうか？

(* FILL IN HERE *)
[]
*)

(* **** Exercise: 4 stars, optional (prog_pres_bigstep) *)
(** **** 練習問題: ★★★★, optional (prog_pres_bigstep) *)
(* Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?

(* FILL IN HERE *)
[]
*)
(**
   評価関係をビッグステップスタイルで定義したとしましょう。その場合、進行と型保存性に当たるものとしては何が適切でしょうか。

(* FILL IN HERE *)
[]
*)


