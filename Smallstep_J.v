(** * Smallstep_J: スモールステップ操作的意味論 *)
(* * Smallstep: Small-step Operational Semantics *)

(* $Date: 2011-05-07 16:41:12 -0400 (Sat, 07 May 2011) $ *)

Require Export Imp_J.
Require Import Relations.

(* The evaluators we have seen so far (e.g., the ones for [aexp]s,
    [bexp]s, and commands) have been formulated in a "big-step"
    style -- they specify how a given expression can be evaluated to
    its final value (or a command plus a store to a final store) "all
    in one big step."

    This style is simple and natural for many purposes (indeed, Gilles
    Kahn, who popularized its use, called it _natural semantics_), but
    there are some things it does not do well.  In particular, it
    does not give us a natural way of talking about _concurrent_
    programming languages, where the "semantics" of a program -- i.e.,
    the essence of how it behaves -- is not just which input states
    get mapped to which output states, but also includes the
    intermediate states that it passes through along the way, since
    these states can also be observed by concurrently executing code.

    Another shortcoming of the big-step style is more technical, but
    critical for some applications.  Consider the variant of Imp with
    lists that we introduced in ImpList.v.  We chose to define the
    meaning of programs like [0 + nil] by specifying that a list
    should be interpreted as [0] when it occurs in a context expecting
    a number, but this was a bit of a hack.  It would be better simply
    to say that the behavior of such a program is _undefined_ -- it
    doesn't evaluate to any result.  We could easily do this: we'd
    just have to use the formulations of [aeval] and [beval] as
    inductive propositions (rather than Fixpoints), so that we can
    make them partial functions instead of total ones.

    However, this way of defining Imp has a serious deficiency.  In
    this language, a command might _fail_ to map a given starting
    state to any ending state for two quite different reasons: either
    because the execution gets into an infinite loop or because, at
    some point, the program tries to do an operation that makes no
    sense, such as taking the successor of a boolean variable, and
    none of the evaluation rules can be applied.

    These two outcomes -- nontermination vs. getting stuck in an
    erroneous configuration -- are quite different.  In particular, we
    want to allow the first (permitting the possibility of infinite
    loops is the price we pay for the convenience of programming with
    general looping constructs like [while]) but prevent the
    second (which is just wrong), for example by adding some form of
    _typechecking_ to the language.  Indeed, this will be a major
    topic for the rest of the course.  As a first step, we need a
    different way of presenting the semantics that allows us to
    distinguish nontermination from erroneous "stuck states."

    So, for lots of reasons, we'd like to have a finer-grained way of
    defining and reasoning about program behaviors.  This is the topic
    of the present chapter.  We replace the "big-step" [eval] relation
    with a "small-step" relation that specifies, for a given program,
    how the "atomic steps" of computation are performed. *)
(** ここまで見てきた評価器(例えば[aexp]のもの、[bexp]のもの、コマンドのもの)
    はビッグステップスタイルで記述されてきました。
    つまり、与えられた式がどのように最終的な値になるか
    (またはコマンドと記憶状態(store)の組がどのように最終記憶状態になるか)を特定していました。
    「すべてが1つの大きなステップ」で行われました。

    このスタイルは単純で多くの目的のために自然な方法です(実際、Gilles Kahn は、
    この使用を広めた人ですが、彼はこれを自然意味論(_natural semantics_)と呼びました)。
    しかし、これではうまくいかないときもあります。
    特に、この方法は、並列プログラミング言語について話す自然な方法を提供してくれません。
    並列プログラミング言語の場合、プログラムの「意味」、つまり
    プログラムがどのように振る舞うかの本質は、
    入力状態が出力状態にどのように写像されるかだけではなく、途中で通過する状態も含みます。
    なぜなら、中間状態は並列実行されるコードからも観測されるからです。

    ビッグステップスタイルのもう1つの欠点は、より技術的なことですが、
    ある種のアプリケーションには致命的です。
    ImpList_J.v で導入した、リストを持つImpの変種を考えましょう。
    [0 + nil]のようなプログラムの意味を、数値が期待されるコンテキストでリストが現れたときには、
    それを[0]と解釈するものとして定義する方法をとりました。しかしこれはその場限りのものでした。
    単純に、
    そのようなプログラムの振る舞いは「未定義」(_undefined_)と言ってしまった方がよかったでしょう。
    つまりどのような結果にも評価されないということです。
    そうすることは簡単にできるでしょう。
    [aeval]と[beval]の定義方法として(Fixpoint ではなく)帰納的命題を使うだけです。
    すると、全関数(total function)ではなく部分関数(partial function)にすることができます。

    しかしながら、この方法で Imp を定義することには深刻な欠陥があります。
    この言語には、コマンドが初期状態を終了状態に写像するのに失敗するまったく異なる2種類の理由があります。
    1つは評価が無限ループに陥ることによるもの、もう1つは、どこかの地点でプログラムが、
    ブール値の次の値をとるなどの意味のない操作をしようとして、
    どの評価規則も適用できなくなることによるものです。

    この2つの結果、つまり「停止しないこと」と「間違った設定によって行き詰まること」は、まったく別物です。
    特に、1つ目は許容し(無限ループの可能性を許すことは、
    プログラミングに [while] のような一般的ループ構造を使う便利さの代償です)、
    2つ目(これはただの間違いです)は禁じたいのです。
    これは例えば言語に何らかの「型チェック」(_typechecking_)を追加することで実現できます。
    実のところ、これはこのコースの残りの部分の主要なトピックです。
    最初のステップとして、停止しないことと、
    間違いによる「行き詰まり状態」を区別することができる別の意味提示方法が必要です。

    このように、いろいろな理由で、
    プログラムの振る舞いを定義し推論するよりきめの細かい方法が欲しいのです。
    これがこの章のトピックです。
    与えられたプログラムに対して計算の「アトミックなステップ」
    がどのように行なわれるかを定める「スモールステップ」の関係によって、
    「ビッグステップ」の[eval]関係を置き換えます。*)

(* ########################################################### *)
(* * A Toy Language *)
(** * おもちゃの言語 *)

(* To save space in the discussion, let's go back to an
    incredibly simple language containing just constants and addition.
    At the end of the chapter, we'll see how to apply the same
    techniques to the full Imp language. *)
(** 無駄な議論を省くため、定数と足し算だけの極端に単純な言語に戻りましょう。
    この章の終わりには、同じテクニックをImp言語全体に適用する方法がわかるでしょう。*)

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_const" | Case_aux c "tm_plus" ].

Module SimpleArith0.

(* Here is a standard evaluator for this language, written in the
    same (big-step) style as we've been using up to this point. *)
(** 次がこの言語の標準的な評価器です。
    ここまでやってきたのと同じ(ビッグステップの)スタイルで記述されています。*)

Fixpoint eval (t : tm) : nat :=
  match t with
  | tm_const n => n
  | tm_plus a1 a2 => eval a1 + eval a2
  end.

End SimpleArith0.

Module SimpleArith1.

(* Now, here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.  Again,
    we use the notation [t || n] for "[t] evaluates to [n]." *)
(** 次は同じ評価器を、まったく同じスタイルながら、帰納的に定義された関係によって定式化したものです。
    再び、「[t]が[n]に評価される」を記法 [t || n] で表しています。*)
(*
[[[
                                ------                                (E_Const)
                                n || n

                               t1 || n1
                               t2 || n2
                        ---------------------                          (E_Plus)
                        t1 + t2 || plus n1 n2
]]]
    We write [plus n1 n2] in the second rule, rather than [n1 + n2],
    to emphasize the fact that the [+] on the left of the [||] is an
    abstract-syntax-tree node while the addition on the right of the
    [||] is the mathematical sum of the numbers [n1] and [n2].  The
    formal Coq version of the definition is more pedantic about this
    distinction: *)
(**
[[
                                ------                                (E_Const)
                                n || n

                               t1 || n1
                               t2 || n2
                        ---------------------                          (E_Plus)
                        t1 + t2 || plus n1 n2
]]
    2つ目の規則で [n1 + n2] ではなく [plus n1 n2] と書いています。
    これは、[||] の左側にある[+]が抽象構文木のノードであるのに対し、
    [||] の右側の加算は数値 [n1] と [n2] の数学的な和であることを強調するためです。
    形式的なCoqのバージョンではこの区別についてより堅苦しくなっています。*)

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      tm_const n || n
  | E_Plus : forall t1 t2 n1 n2,
      t1 || n1 ->
      t2 || n2 ->
      tm_plus t1 t2 || plus n1 n2

  where " t '||' n " := (eval t n).

End SimpleArith1.

(* Here is a slight variation, still in big-step style, where
    the final result of evaluating a term is also a term, rather than
    a bare number. *)
(** 次はわずかに変わっています。まだビッグステップスタイルですが、
    項の最終結果が数値そのものではなく、また項になっています。*)

Reserved Notation " t '||' t' " (at level 50, left associativity).

Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n1,
        tm_const n1 || tm_const n1
  | E_Plus : forall t1 n1 t2 n2,
        t1 || tm_const n1 ->
        t2 || tm_const n2 ->
        tm_plus t1 t2 || tm_const (plus n1 n2)

  where " t '||' t' " := (eval t t').

(* (Note that this doesn't change anything in the informal rules,
    where we are eliding the distinction between the constant _term_
    [n] and the bare _number_ [n].) *)
(** (非形式的な規則では、定数「項」[n]とそのままの「数値」[n]の区別を省いているので、
    何も変わらないことに注意します。) *)

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

Module SimpleArith2.

(* Now, here is a small-step version. *)
(** そして、次がスモールステップ版です。*)
(*
[[[
                        ----------------------              (ST_PlusConstConst)
                        n1 + n2 ==> plus n1 n2

                              t1 || t1'
                         -------------------                         (ST_Plus1)
                         t1 + t2 || t1' + t2

                              t2 || t2'
                         -------------------                         (ST_Plus2)
                         n1 + t2 || n1 + t2'
]]]
*)
(**
[[
                        ----------------------              (ST_PlusConstConst)
                        n1 + n2 ==> plus n1 n2

                              t1 || t1'
                         -------------------                         (ST_Plus1)
                         t1 + t2 || t1' + t2

                              t2 || t2'
                         -------------------                         (ST_Plus2)
                         n1 + t2 || n1 + t2'
]]
*)
(* Note that we're using variable names here to lighten the notation:
    by convention, [n1] and [n2] refer only to constants (constructed
    with [tm_const]), while [t1] and [t2] refer to arbitrary terms.
    In the formal rules, we use explicit constructors to make the same
    distinction. *)
(** なお、ここでは記法を簡単にするため変数名を使っています。慣習として、[n1]と[n2]は定数
    ([tm_const]で構成されるもの)のみを指します。一方[t1]と[t2]は任意の項を指します。
    形式的規則では明示的なコンストラクタを使ってこの区別をします。*)

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ==> t2' ->
      tm_plus (tm_const n1) t2 ==> tm_plus (tm_const n1) t2'

  where " t '==>' t' " := (step t t').

(* Things to notice:

    - We are defining just a single reduction step, in which
      one [tm_plus] node is replaced by its value.

    - Each step finds the _leftmost_ [tm_plus] node that is ready to
      go (both of its operands are constants) and rewrites it in
      place.  The first rule tells how to rewrite this [tm_plus] node
      itself; the other two rules tell how to find it.

    - A term that is just a constant cannot take a step. *)
(** 注目すること:

    - 定義しているのは簡約のちょうど1ステップです。
      そこでは1つの[tm_plus]ノードがその値に置き換えられます。

    - 各ステップでは「最左」の準備ができている(つまり、引数が両方とも定数である)
      [tm_plus]ノードを探して、それをその場で書き換えます。
      最初の規則は[tm_plus]ノードをどのように書き換えるかを定めます。
      残りの2つの規則は、それをどう探すかを定めます。

    - 定数の項は、ステップを進めません。*)

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

(* A couple of examples of reasoning with the [step]
    relation... *)
(** [step]関係を使った推論の例を2つ... *)

(* If [t1] can take a step to [t1'], then [tm_plus t1 t2] steps
    to [plus t1' t2]: *)
(** もし[t1]が1ステップで[t1']になるならば、
    [tm_plus t1 t2] は1ステップで [plus t1' t2] になります: *)

Example test_step_1 :
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
      ==>
      tm_plus
        (tm_const (plus 0 3))
        (tm_plus (tm_const 2) (tm_const 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(* **** Exercise: 2 stars (test_step_2) *)
(** **** 練習問題: ★★ (test_step_2) *)
(* Right-hand sides of sums can take a step only when the
    left-hand side is finished: if [t2] can take a step to [t2'],
    then [tm_plus (tm_const n) t2] steps to [tm_plus (tm_const n)
    t2']: *)
(** 和の右側がステップを進むことができるのは、左側が終了したときだけです:
    もし[t2]が1ステップで[t2']になるならば、
    [tm_plus (tm_const n) t2] は1ステップで [tm_plus (tm_const n) t2']
    になります。(次の証明を完成させなさい): *)
(* (訳注: 他のところと比べて、明示的な練習問題としての指示がなかったので、
   意を汲んで追記しました。) *)
    

Example test_step_2 :
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3)))
      ==>
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_const (plus 0 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* One interesting property of the [==>] relation is that, like the
    evaluation relation for our language of Imp programs, it is
    _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t ==> t'] is provable).  Formally, this is the
    same as saying that [==>] is a partial function.

    _Proof sketch_: We show that if [x] steps to both [y1] and [y2]
    then [y1] and [y2] are equal, by induction on a derivation of
    [step x y1].  There are several cases to consider, depending on
    the last rule used in this derivation and in the given derivation
    of [step x y2].

      - If both are [ST_PlusConstConst], the result is immediate.

      - The cases when both derivations end with [ST_Plus1] or
        [ST_Plus2] follow by the induction hypothesis.

      - It cannot happen that one is [ST_PlusConstConst] and the other
        is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
        the form [tm_plus t1 t2] where both [t1] and [t2] are
        constants (by [ST_PlusConstConst]) _and_ one of [t1] or [t2] has
        the form [tm_plus ...].

      - Similarly, it cannot happen that one is [ST_Plus1] and the other
        is [ST_Plus2], since this would imply that [x] has the form
        [tm_plus t1 t2] where [t1] has both the form [tm_plus t1 t2] and
        the form [tm_const n]. [] *)
(** 関係 [==>] のおもしろい性質の1つは、
    Imp プログラムの言語の評価関係と同様、決定性を持つ(_deterministic_)ということです。

    「定理」: 各[t]に対して、[t]が1ステップで[t']になる([t ==> t'] が証明可能な)
    [t']は高々1つである。
    形式的には、これは、[==>]が部分関数であるというのと同じです。

    「証明スケッチ」:[x]が1ステップで[y1]と[y2]のどちらにもなるとき、[y1]と[y2]
    が等しいことを、[step x y1] の導出についての帰納法で示す。
    この導出と [step x y2] の導出のそれぞれで使われた最後の規則によって、
    いくつかの場合がある。

      - もし両者とも [ST_PlusConstConst] ならば、一致は明らかである。

      - 導出が両者とも [ST_Plus1] または [ST_Plus2] で終わるならば、
        帰納法の仮定から成立する。

      - 一方が [ST_PlusConstConst] で、他方が [ST_Plus1] または [ST_Plus2]
        であることはあり得ない。なぜなら、そうなるためには、
        [x] が [tm_plus t1 t2] の形で([ST_PlusConstConst]より)
        [t1]と[t2]が両者とも定数であり、かつ[t1]または[t2]が [tm_plus ...] 
        の形でなければならない。

      - 同様に、一方が [ST_Plus1] で他方が [ST_Plus2] であることもあり得ない。
        なぜなら、そのためには、[x] は [tm_plus t1 t2] の形で、
        [t1] が [tm_plus t1 t2] の形でも [tm_const n] 
        の形でもなければならないからである。[] *)

Theorem step_deterministic:
  partial_function step.
Proof.
  unfold partial_function. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". reflexivity.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
      SCase "ST_Plus1".
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2".
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.  Qed.

End SimpleArith2.

(* ########################################################### *)
(* ** Values *)
(** ** 値 *)

(* Let's take a moment to slightly generalize the way we state the
    definition of single-step reduction.  *)
(** 定義した1ステップ簡約の定義をちょっとだけ一般化するために少し時間をとりましょう。*)

(* It is useful to think of the [==>] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done.

    We can then execute a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [==>] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)
(** 関係 [==>] を抽象機械(_abstract machine_)の定義と考えるのは便利です:

      - どの時点でも、機械の状態(_state_)は項です。

      - 機械のステップ(_step_)は、計算のアトミックな単位です。ここでは、1つの加算処理です。

      - 機械の停止状態(_halting states_)は、さらなる計算が存在しない状態です。

    このとき、項[t]は以下のように評価できます:

      - [t]を機械の開始状態としてとります。

      - 次のような機械の状態の列を見つけるために、[==>] 関係を繰り返し使います。
        見つけるのは、[t]から始まり、それぞれの状態から1ステップでその次の状態になる列です。

      - もう簡約ができなくなったとき、機械の最終状態を、実行結果として「読み出し」ます。*)

(* Intuitively, it is clear that the final states of the
    machine are always terms of the form [tm_const n] for some [n].
    We call such terms _values_. *)
(** 直観的には、機械の最終状態が常に、
    ある[n]についての [tm_const n] という形の項になることは明らかです。
    そのような項を「値」(_values_)と呼びます。*)

Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

(* Having introduced the idea of values, we can use it in the
    definition of the [==>] relation to write [ST_Plus2] rule in a
    slightly more intuitive way: *)
(** 値の概念を導入したので、これを [==>] 関係の定義に使うことで、
    [ST_Plus2] 規則をもう少しだけ直観的なものにできます: *)
(*
[[[
                        ----------------------              (ST_PlusConstConst)
                        n1 + n2 ==> plus n1 n2

                              t1 || t1'
                         -------------------                         (ST_Plus1)
                         t1 + t2 || t1' + t2

                              t2 || t2'
                         -------------------                         (ST_Plus2)
                         v1 + t2 || v1 + t2'
]]]
*)
(**
[[
                        ----------------------              (ST_PlusConstConst)
                        n1 + n2 ==> plus n1 n2

                              t1 || t1'
                         -------------------                         (ST_Plus1)
                         t1 + t2 || t1' + t2

                              t2 || t2'
                         -------------------                         (ST_Plus2)
                         v1 + t2 || v1 + t2'
]]
*)
(* Again, the variable names here carry important information:
    by convention, [v1] ranges only over values, while [t1] and [t2]
    range over arbitrary terms.  In the Coq version of the rules, we
    use an explicit [value] hypothesis for the same purpose. *)
(** 再び、変数名が重要な情報を担っています:
    慣習として、[v1]は値のみを変域とし、一方[t1]と[t2]は任意の項を変域とします。
    規則のCoqバージョンでは、同じ目的のために明示的な[value]仮定を使います。*)

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          tm_plus (tm_const n1) (tm_const n2)
      ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *)
        t2 ==> t2' ->
        tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

(* **** Exercise: 3 stars, recommended (redo_determinacy) *)
(** **** 練習問題: ★★★, recommended (redo_determinacy) *)
(* As a sanity check on this change, let's re-verify determinacy

    Proof sketch: We must show that if [x] steps to both [y1] and [y2]
    then [y1] and [y2] are equal.  Consider the final rules used in
    the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [tm_plus t1 t2] where both [t1] and [t2] are
      constants (by [ST_PlusConstConst]) AND one of [t1] or [t2] has
      the form [tm_plus ...].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form
      [tm_plus t1 t2] where [t1] both has the form [tm_plus t1 t2] and
      is a value (hence has the form [tm_const n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)
(** この変更のサニティチェックのため、決定性を再検証しましょう。

    証明スケッチ: もし[x]が1ステップで[y1]にも[y2]にも進むならば、
    [y1]と[y2]が等しいことを示さなければならない。
    [step x y1] と [step x y2] の導出の最後の規則を考える。

    - もし両者とも[ST_PlusConstConst]ならば、一致は明らかである。

    - 一方が [ST_PlusConstConst] で、他方が [ST_Plus1] または [ST_Plus2]
      であることはあり得ない。なぜなら、そうなるためには、
      [x] が [tm_plus t1 t2] の形で([ST_PlusConstConst]より)
      [t1]と[t2]が両者とも定数であり、かつ[t1]または[t2]が [tm_plus ...] 
      の形でなければならない。

    - 同様に、一方が [ST_Plus1] で他方が [ST_Plus2] であることもあり得ない。
      なぜなら、そのためには、[x] が [tm_plus t1 t2] の形で、
      [t1] は [tm_plus t1 t2] の形であり、かつ( [tm_const n] の形であるから)
      値でもなければならないからである。

    - 導出が両者とも [ST_Plus1] または [ST_Plus2] で終わるならば、
      帰納法の仮定から成立する。[] *)

(* Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write it from
    scratch and just use the earlier one if you get stuck. *)
(** 証明のほとんどは前のものと同じです。しかし、練習問題の効果を最大にするために、
    ゼロから証明を書き、前のものを見るのは行き詰まった時だけにしなさい。 *)

Theorem step_deterministic :
  partial_function step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################### *)
(* ** Strong Progress and Normal Forms *)
(** ** 強進行と正規形 *)

(* The definition of single-step reduction for our toy language is
    fairly simple, but for a larger language it would be pretty easy
    to forget one of the rules and create a situation where some term
    cannot take a step even though it has not been completely reduced
    to a value.  The following theorem shows that we did not, in fact,
    make such a mistake here. *)
(** おもちゃの言語に対する1ステップの簡約の定義はかなり単純です。
    しかし、より大きな言語に対しては、何か規則を忘れてしまうことは簡単に起き、
    項が完全に値に簡約されていないのにステップを進めなくなってしまうことが発生します。
    次の定理は、このような間違いをしていないことを示します。*)

(* _Theorem_ (_Strong Progress_): For all [t:tm], either [t] is a
    value, or there exists a term [t'] such that [t ==> t'].

    _Proof_: By induction on [t].

    - Suppose [t = tm_const n]. Then [t] is a [value].

    - Suppose [t = tm_plus t1 t2], where (by the IH) [t1] is either a
      value or can step to some [t1'], and where [t2] is either a
      value or can step to some [t2']. We must show [tm_plus t1 t2] is
      either a value or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PlusConstConst].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_Plus2].

      - If [t1] can take a step, then so can [t], by [ST_Plus1].  [] *)
(** 「定理(強進行)」(_Strong Progress_):すべての [t:tm] について
    [t]は値であるか、ある項[t']があって [t ==> t'] となる。

    「証明」: [t]についての帰納法で証明する。

    - [t = tm_const n] とする。すると、[t] は [value](値)である。

    - [t = tm_plus t1 t2] と仮定する。ここで(帰納仮定から)
      [t1]は値であるか、1ステップである[t1']になり、また、[t2]は値であるか、
      1ステップである[t2']になる。
      ここで必要なのは、[tm_plus t1 t2]が値であるか、
      ある[t']に1ステップで進むということを示すことである。

      - もし[t1]と[t2]がともに値なら、[ST_PlusConstConst]により
        [t]はステップを進むことができる。

      - もし[t1]が値で[t2]がステップを進むことができるならば、[ST_Plus2]により
        [t]もステップを進むことができる。

      - もし[t1]がステップを進むことができるならば、[ST_Plus1]により
        [t]もステップを進むことができる。  [] *)

(* This important property is called _strong progress_, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    simply "progress.") *)
(** この重要な性質は「強進行」(_strong progress_)と呼ばれます。
    これは、すべての項が値であるか、別の項に「進行できる」("make progress")
    ことからきた名称です。「強」("strong")という修飾句は、
    後の章のより細分されたバージョン(単に「進行」("progress")と呼ばれる)
    と区別するためのものです。*)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
    Case "tm_const". left. apply v_const.
    Case "tm_plus". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (tm_const (plus n n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (tm_plus t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0].
          exists (tm_plus t' t2).
          apply ST_Plus1. apply H0.  Qed.

(* The idea of "making progress" can be extended to tell us something
    interesting about [value]s: they are exactly the terms that
    _cannot_ make progress in this sense.  To state this fact, let's
    begin by giving a name to terms that cannot make progress: We'll
    call them _normal forms_. *)
(** 「進行する」という概念の拡張から、[value](値)についての興味深い性質がわかります:
    値とはこの意味で進行「できない」項のことに他なりません。
    この事実を述べるために、進行できない項に名前をつけましょう。そういう項を「正規形」
    (_normal form_)と呼びます。*)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

(* This definition actually specifies what it is to be a normal form
    for an _arbitrary_ relation [R] over an arbitrary set [X], not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. *)
(** この定義は実際には、任意の集合[X]の上の「任意の」関係[R]について、
    何が正規形であるかを定めています。
    今興味対象としている、項の上の特定の1ステップ簡約関係に限るものではありません。
    このコースで後に、別の関係の議論において同じ用語法を用います。*)

(* We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing. *)
(** 強進行定理の洞察を一般化するためにこの用語を使います。
    この言語では、正規形と値とは実質的に同じものです。*)

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  unfold normal_form. intros t H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(* Why is this interesting?  For two reasons:

    - Because [value] is a syntactic concept -- it is a defined by
      looking at the form of a term -- while [normal_form] is a
      semantic one -- it is defined by looking at how the term steps.
      It is not obvious that these concepts should coincide!

    - Indeed, there are lots of languages in which the concepts of
      normal form and value do _not_ coincide. *)
(** なぜこれが興味深いのでしょう？ 2つの理由があります:

    - なぜなら[value](値)は構文的概念です。つまり項の形を見ることで定義されます。
      一方[normal_form](正規形)は意味論的なものです。
      つまり項がどのようにステップを進むかによって定義されます。
      この2つの概念が一致することは自明ではないのです!

    - 実際、正規形と値の概念が一致「しない」言語はたくさん存在します。*)

(* Let's examine how this can happen... *)
(** これがどうして起こるのか調べてみましょう... *)

(* ##################################################### *)

(* We might, for example, mistakenly define [value] so that it
    includes some terms that are not finished reducing. *)
(** 例えば、[value](値)の定義を間違えていて、
    簡約が完了していない項を含んでいるかもしれません。*)

Module Temp1.
(* Open an inner module so we can redefine value and step. *)

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n)
| v_funny : forall t1 n2,                       (* <---- *)
              value (tm_plus t1 (tm_const n2)).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (step t t').

(* **** Exercise: 3 stars, recommended (value_not_same_as_normal_form) *)
(** **** 練習問題: ★★★, recommended (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp1.

(* ########################################################### *)

(* Alternatively, we might mistakenly define [step] so that it
    permits something designated as a value to reduce further. *)
(** あるいは、[step]の定義を間違えていて、
    値とされたものをさらに簡約するようになっているかもしれません。*)

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,                         (* <---- *)
      tm_const n ==> tm_plus (tm_const n) (tm_const 0)
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'

  where " t '==>' t' " := (step t t').

(* **** Exercise: 3 stars, recommended (value_not_same_as_normal_form) *)
(** **** 練習問題: ★★★, recommended (value_not_same_as_normal_form) *)
Lemma value_not_same_as_normal_form :
  exists t, value t /\ ~ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp2.

(* ########################################################### *)

(* Finally, we might mistakenly define [value] and [step] so that
    there is some term that is not a value but that cannot take a step
    in the [step] relation.  Such terms are said to be _stuck_. *)
(** 最後に、[value]と[step]の定義を間違えていて、ある項について、値でもなく、
    [step]関係で1ステップ進むこともできなくなっているかもしれません。
    そのような項は「行き詰まり」(_stuck_)と呼ぶべきでしょう。*)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2

  where " t '==>' t' " := (step t t').

(* (Note that [ST_Plus2] is missing.) *)
(** ([ST_Plus2] がないことに注意します。) *)

(* **** Exercise: 3 stars (value_not_same_as_normal_form') *)
(** **** 練習問題: ★★★ (value_not_same_as_normal_form') *)
Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Temp3.

(* ########################################################### *)
(* ** Exercises *)
(** ** 練習問題 *)

Module Temp4.

(* Here is another very simple language whose terms, instead of being
    just plus and numbers, are just the booleans true and false and a
    conditional expression... *)
(** 以下は、別の非常に簡単な言語です。項は、加算と数値の代わりに、
    真理値 true と false、および条件式です... *)

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3

  where " t '==>' t' " := (step t t').

(* **** Exercise: 1 star (smallstep_bools) *)
(** **** 練習問題: ★ (smallstep_bools) *)
(* Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Coq.) *)
(** 以下の命題のうち証明できるものはどれでしょう？
    (これは単に頭の体操です。
    しかしさらなるチャレンジとしてCoqで自分の答えを自由に証明してみなさい。) *)

Definition bool_step_prop1 :=
  tm_false ==> tm_false.

(* FILL IN HERE *)

Definition bool_step_prop2 :=
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_false tm_false tm_false)
  ==>
     tm_true.

(* FILL IN HERE *)

Definition bool_step_prop3 :=
     tm_if
       (tm_if tm_true tm_true tm_true)
       (tm_if tm_true tm_true tm_true)
       tm_false
   ==>
     tm_if
       tm_true
       (tm_if tm_true tm_true tm_true)
       tm_false.

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 3 stars, recommended (progress_bool) *)
(** **** 練習問題: ★★★, recommended (progress_bool) *)
(* Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well. *)
(** 加算式についてと同様に、ブール式についても進行定理が証明できます。
    (やってみなさい。) *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (step_deterministic) *)
(** **** 練習問題: ★★, optional (step_deterministic) *)
Theorem step_deterministic :
  partial_function step.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Module Temp5.

(* **** Exercise: 2 stars (smallstep_bool_shortcut) *)
(** **** 練習問題: ★★ (smallstep_bool_shortcut) *)
(* Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the [then] and
    [else] branches of a conditional are the same value (either
    [tm_true] or [tm_false]) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:
[[
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.
]]
*)
(** 条件式の[then]と[else]の枝が同じ値のとき(ともに[tm_true]であるか、
    ともに[tm_false]であるかのとき)、ガードが値に簡約されていなくても、
    条件式全体を枝の値に簡約するように、ステップ関係にバイパスを追加したいとします。
    例えば次の命題を証明できるようにしたいとします:
[[
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.
]]
*)

(* Write an extra clause for the step relation that achieves this
    effect and prove [bool_step_prop4]. *)
(** ステップ関係にこのための追加の節を記述し、[bool_step_prop4]を証明しなさい。*)

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3
(* FILL IN HERE *)

  where " t '==>' t' " := (step t t').
(** [] *)

Definition bool_step_prop4 :=
         tm_if
            (tm_if tm_true tm_true tm_true)
            tm_false
            tm_false
     ==>
         tm_false.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (properties_of_altered_step) *)
(** **** 練習問題: ★★★ (properties_of_altered_step) *)
(* It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    [ST_ShortCircuit]...

    - Is the [step] relation still deterministic?  Write yes or no and
      briefly (1 sentence) explain your answer.

      Optional: prove your answer correct in Coq.
*)
(** 講義ノートのステップ関係についての決定性定理と強進行定理が、
    上記のステップの定義についても証明できます。
    [ST_ShortCircuit]節を追加した後で...

    - [step]関係はそれでも決定性を持つでしょうか？
      yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

      Optional: Coq でその答えが正しいことを証明しなさい。
*)

(* FILL IN HERE *)

(*
   - Does a strong progress theorem hold? Write yes or no and
     briefly (1 sentence) explain your answer.

     Optional: prove your answer correct in Coq.
*)
(**
   - 強進行定理は成立するでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

      Optional: Coq でその答えが正しいことを証明しなさい。
*)

(* FILL IN HERE *)

(*
   - In general, is there any way we could cause strong progress to
     fail if we took away one or more constructors from the original
     step relation? Write yes or no and briefly (1 sentence) explain
     your answer.

  (* FILL IN HERE *)
*)
(**
   - 一般に、オリジナルのステップ関係から1つ以上のコンストラクタを取り除いて、
     強進行性を持たなくする方法はあるでしょうか？
     yes または no と書き、簡潔に(1文で)その答えを説明しなさい。

  (* FILL IN HERE *)
*)
(** [] *)

End Temp5.
End Temp4.

(* ########################################################### *)
(* * Multi-Step Reduction *)
(** * マルチステップ簡約 *)

(* Until now, we've been working with the _single-step reduction_
    relation [==>], which formalizes the individual steps of an
    _abstract machine_ for executing programs.

    It is also interesting to use this machine to reduce programs to
    completion -- to find out what final result they yield.  This can
    be formalized as follows:

    - First, we define a _multi-step reduction relation_ [==>*], which
      relates terms [t] and [t'] if [t] can reach [t'] by any number
      of single reduction steps.

    - Then we define a "result" of a term [t] as a normal form that
      [t] can reach by multi-step reduction. *)
(** ここまでは、1ステップ簡約関係 [==>] に取り組んできました。
    これは、プログラムを実行する抽象機械の1つのステップを形式化したものです。

    この機械を使って、プログラムを完全に簡約してみるのもおもしろいでしょう。
    つまり、その最後の結果がどうなるかを調べることです。
    これは以下のように形式化できます:
  
    - 最初に、「マルチステップ簡約関係」(_multi-step reduction relation_)
      [==>*] を定義します。
      この関係は、[t]から1ステップ簡約を何らかの回数回行うことで[t']に到達できるとき、
      [t]と[t']を関係づけるものです。

    - 次に項[t]の結果("result")を、
      [t]がマルチステップ簡約で到達できる正規形[t]として定義します。*)

(* ########################################################### *)
(* ** Multi-Step Reduction *)
(** ** マルチステップ簡約 *)

(* The _multi-step reduction_ relation [==>*] is the reflexive,
    transitive closure of the single-step relation [==>]. *)
(** マルチステップ簡約(_multi-step reduction_)関係 [==>*] は1ステップ関係
    [==>]の反射推移閉包です。*)

Definition stepmany := refl_step_closure step.

Notation " t '==>*' t' " := (stepmany t t') (at level 40).

(* For example... *)
(** 例えば... *)

Lemma test_stepmany_1:
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
   ==>*
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  apply rsc_step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_plus (tm_const 2) (tm_const 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply rsc_step with
            (tm_plus
                (tm_const (plus 0 3))
                (tm_const (plus 2 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply rsc_R.
  apply ST_PlusConstConst.  Qed.

(* Here's an alternate proof that uses [eapply] to avoid explicitly
    constructing all the intermediate terms. *)
(** 以下は別証です。
    [eapply]を使うことで、すべての中間的な項を明示的に構成する必要をなくしたものです。*)

Lemma test_stepmany_1':
      tm_plus
        (tm_plus (tm_const 0) (tm_const 3))
        (tm_plus (tm_const 2) (tm_const 4))
  ==>*
      tm_const (plus (plus 0 3) (plus 2 4)).
Proof.
  eapply rsc_step. apply ST_Plus1. apply ST_PlusConstConst.
  eapply rsc_step. apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  eapply rsc_step. apply ST_PlusConstConst.
  apply rsc_refl.  Qed.

(* **** Exercise: 1 star (test_stepmany_2) *)
(** **** 練習問題: ★ (test_stepmany_2) *)
Lemma test_stepmany_2:
  tm_const 3 ==>* tm_const 3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star (test_stepmany_3) *)
(** **** 練習問題: ★ (test_stepmany_3) *)
Lemma test_stepmany_3:
      tm_plus (tm_const 0) (tm_const 3)
   ==>*
      tm_plus (tm_const 0) (tm_const 3).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars (test_stepmany_4) *)
(** **** 練習問題: ★★ (test_stepmany_4) *)
Lemma test_stepmany_4:
      tm_plus
        (tm_const 0)
        (tm_plus
          (tm_const 2)
          (tm_plus (tm_const 0) (tm_const 3)))
  ==>*
      tm_plus
        (tm_const 0)
        (tm_const (plus 2 (plus 0 3))).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################### *)
(* ** Normal Forms Again *)
(** ** 正規形再び *)

(* If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)
(** [t]が0以上のステップで[t']に簡約され、[t']が正規形のとき、
    「[t']は[t]の正規形である」と言います。*)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

(* We have already seen that single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if [t] can reach
    a normal form, then this normal form is unique -- i.e.,
    [normal_form_of] is a partial function.  In other words, we
    can actually pronounce [normal_form t t'] as "[t'] is _the_
    normal form of [t]." *)
(** 1ステップ簡約が決定性を持つことを既に見ました。
    つまり、項が1ステップ進む方法は高々1種類だということです。
    このことから、[t]が正規形に到達するならば、その正規形は1つに決まることになります。
    つまり、[normal_form_of] は部分関数です。言い換えると、
    [normal_form t t'] を、
    (「[t']は[t]の正規形である」と読む以外に)
    「[t]の正規形は[t']である」と読んでよいということです。
    (訳注：原文では "_the_ normal form of [t]" 
    と定冠詞を使ってよいことと記述されています。) *)

(* **** Exercise: 3 stars, optional (test_stepmany_3) *)
(** **** 練習問題: ★★★, optional (test_stepmany_3) *)
Theorem normal_forms_unique:
  partial_function normal_form_of.
Proof.
  unfold partial_function. unfold normal_form_of.  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12]. destruct P2 as [P21 P22].
  generalize dependent y2.
  (* We recommend using this initial setup as-is! *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Indeed, something stronger is true for this language (though not
    for all languages): the reduction of _any_ term [t] will
    eventually reach a normal form -- i.e., [normal_form_of] is a
    _total_ function.  Formally, we say the [step] relation is
    _normalizing_. *)
(** 実のところ、この言語については、より強いことが成立します
    (これは他のすべての言語で成立することではありません):
    「任意の」項[t]はいつかは正規形に到達する、ということです。
    つまり [normal_form_of] は全関数です。
    形式的には、[step]関係は正規化性を持つ(_normalizing_)と言います。 *)

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.

(* To prove that [step] is normalizing, we need a couple of lemmas.

    First, we observe that, if [t] reduces to [t'] in many steps, then
    the same sequence of reduction steps within [t] is also possible
    when [t] appears as the left-hand child of a [tm_plus] node, and
    similarly when [t] appears as the right-hand child of a [tm_plus]
    node (whose left-hand child is a value). *)
(** [step]が正規化性を持つことを証明するため、二つの補題を必要とします。

    一つは、[t]が[t']に何ステップかで簡約されるならば、
    [t]が [tm_plus] ノードの左側の子ノードとして現れるときには、
    [t]内で同じ簡約ステップ列が可能である、ということ、
    そしてまた同様のことが、
    [t]が(左側の子ノードが値である)[tm_plus]
    の右側の子ノードとして現れるときにも言える、ということです。*)

Lemma stepmany_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     tm_plus t1 t2 ==>* tm_plus t1' t2.
Proof.
  intros t1 t1' t2 H. rsc_cases (induction H) Case.
    Case "rsc_refl". apply rsc_refl.
    Case "rsc_step". apply rsc_step with (tm_plus y t2).
        apply ST_Plus1. apply H.
        apply IHrefl_step_closure.  Qed.

(* **** Exercise: 2 stars *)
(** **** 練習問題: ★★ *)
Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     tm_plus t1 t2 ==>* tm_plus t1 t2'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* _Theorem_: The [step] function is normalizing -- i.e., for every
    [t] there exists some [t'] such that [t] steps to [t'] and [t'] is
    a normal form.

    _Proof sketch_: By induction on terms.  There are two cases to
    consider:

    - [t = tm_const n] for some [n].  Here [t] doesn't take a step,
      and we have [t' = t].  We can derive the left-hand side by
      reflexivity and the right-hand side by observing (a) that values
      are normal forms (by [nf_same_as_value]) and (b) that [t] is a
      value (by [v_const]).

    - [t = tm_plus t1 t2] for some [t1] and [t2].  By the IH, [t1] and
      [t2] have normal forms [t1'] and [t2'].  Recall that normal
      forms are values (by [nf_same_as_value]); we know that [t1' =
      tm_const n1] and [t2' = tm_const n2], for some [n1] and [n2].
      We can combine the [==>*] derivations for [t1] and [t2] to prove
      that [tm_plus t1 t2] reduces in many steps to [tm_const (plus n1
      n2)].

      It is clear that our choice of [t' = tm_const (plus n1 n2)] is a
      value, which is in turn a normal form. [] *)
(** 「定理」: [step] 関数は正規化性を持つ。つまり、
    任意の[t]に対して、ある[t']があって、[t]からステップを進めると[t']に到達し、
    かつ[t']は正規形である、が成立する。

    「証明スケッチ」:項についての帰納法を使う。考える対象は2つの場合である:

    - ある[n]について [t = tm_const n] である場合。
      このとき、[t]はステップを進めることができないことから、
      [t' = t] である。左辺は反射性から導出され、
      右辺は、(a)([nf_same_as_value]より)値は正規形であること、
      (b)([v_const]より)[t]は値であること、から導出される。

    - ある[t1]、[t2]について、[t = tm_plus t1 t2] である場合。
      帰納仮定より[t1]と[t2]はそれぞれ正規形[t1']と[t2']を持つ。
      ([nf_same_as_value]より)正規形は値であったから、
      ある [n1]、[n2]について、[t1' = tm_const n1] かつ [t2' = tm_const n2]
      である。[t1]と[t2]についての [==>*] 導出を組合せると、
      [tm_plus t1 t2] が幾つかのステップで [tm_const (plus n1 n2)] 
      に簡約されることを証明できる。

      [t' = tm_const (plus n1 n2)] が値であることは明らかなので、これは正規形である。*)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  tm_cases (induction t) Case.
    Case "tm_const".
      exists (tm_const n).
      split.
      SCase "l". apply rsc_refl.
      SCase "r".
        (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
        rewrite nf_same_as_value. apply v_const.
    Case "tm_plus".
      destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
      destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
      rewrite nf_same_as_value in H12. rewrite nf_same_as_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2].
      rewrite <- H in H11.
      rewrite <- H0 in H21.
      exists (tm_const (plus n1 n2)).
      split.
        SCase "l".
          apply rsc_trans with (tm_plus (tm_const n1) t2).
          apply stepmany_congr_1. apply H11.
          apply rsc_trans with
             (tm_plus (tm_const n1) (tm_const n2)).
          apply stepmany_congr_2. apply v_const. apply H21.
          apply rsc_R. apply ST_PlusConstConst.
        SCase "r".
          rewrite nf_same_as_value. apply v_const.  Qed.

(* ########################################################### *)
(* ** Equivalence of Big-Step and Small-Step Reduction *)
(** ** ビッグステップ簡約とスモールステップ簡約の同値性 *)

(* Having defined the operational semantics of our tiny programming
    language in two different styles, it makes sense to ask whether
    these definitions actually define the same thing!  They do, but it
    is not completely straightforward to show this -- or even to see
    how to state it exactly, since one of the relations only goes a
    small step at a time while the other proceeds in large chunks. *)
(** 小さなプログラミング言語に対して2つの異なったスタイルで操作的意味論を定義したので、
    その2つの定義が本当に同じものを定義しているのかを考えるのは意味があります!
    実際に定義は一致しているのですが、それを示すことはそれほど簡単にはできません。
    というより、それを正確に主張することが難しいのです。
    なぜなら、一方は1回で進むのが小さなステップだけですが、
    もう一方は大きなまとまりで進むからです。*)

Lemma eval__value : forall t1 t2,
     eval t1 t2 ->
     value t2.
Proof.
  intros t1 t2 HE.
  eval_cases (inversion HE) Case; apply v_const.  Qed.

(* **** Exercise: 3 stars (eval__stepmany) *)
(** **** 練習問題: ★★★ (eval__stepmany) *)
(* You'll want to use the congruences and some properties of
    [rsc] for this. *)
(** この証明のために合同と[rsc]のいくつかの性質を使うのが良いでしょう。*)

Theorem eval__stepmany : forall t v,
  eval t v -> t ==>* v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (eval__stepmany_inf) *)
(** **** 練習問題: ★★★ (eval__stepmany_inf) *)
(* Write an informal version of the proof of eval__stepmany.

(* FILL IN HERE *)
[]
*)
(** eval__stepmany の証明の非形式版を記述しなさい。

(* ここを埋めなさい *)
[]
*)

(* **** Exercise: 3 stars (step__eval) *)
(** **** 練習問題: ★★★ (step__eval) *)
Theorem step__eval : forall t t' v,
     t ==> t' ->
     t' || v ->
     t || v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem stepmany__eval : forall t v,
  normal_form_of t v -> t || v.
Proof.
  intros t v Hnorm.
  unfold normal_form_of in Hnorm.
  inversion Hnorm as [Hs Hnf]; clear Hnorm.
  (* v is a normal form -> v = tm_const n for some n *)
  rewrite nf_same_as_value in Hnf. inversion Hnf. clear Hnf.
  rsc_cases (induction Hs) Case; subst.
  Case "rsc_refl".
    apply E_Const.
  Case "rsc_step".
    eapply step__eval. eassumption. apply IHHs. reflexivity.  Qed.

(* Bringing it all together, we can crisply say that the [v] is the
    normal form of [t] iff [t] evaluates to [v]. *)
(** 全部まとめることで、[v]が[t]の正規形であるのは、[t]が[v]に評価されるのと同値である、
    とはっきりと言うことができます。*)    

Corollary stepmany_iff_eval : forall t v,
  normal_form_of t v <-> t || v.
Proof.
  split.
  Case "->". apply stepmany__eval.
  Case "<-". unfold normal_form_of. intros E. split. apply eval__stepmany.
    assumption. rewrite nf_same_as_value. eapply eval__value. eassumption.  Qed.

(* ########################################################### *)
(* ** Additional Exercises *)
(** ** さらなる練習問題 *)

(* **** Exercise: 4 stars (combined_properties) *)
(** **** 練習問題: ★★★★ (combined_properties) *)
(* We've considered the arithmetic and conditional expressions
    separately.  This exercise explores how the two interact. *)
(** ここまでに算術式と条件式を別々に考えてきました。
    この練習問題ではこの2つがどのように相互作用するかを調べます。*)

Module Combined.

Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_const" | Case_aux c "tm_plus"
  | Case_aux c "tm_true" | Case_aux c "tm_false" | Case_aux c "tm_if" ].

Inductive value : tm -> Prop :=
  | v_const : forall n, value (tm_const n)
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tm_plus v1 t2 ==> tm_plus v1 t2'
  | ST_IfTrue : forall t1 t2,
      tm_if tm_true t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tm_if tm_false t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tm_if t1 t2 t3 ==> tm_if t1' t2 t3

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

(* Earlier, we separately proved for both plus- and if-expressions...

    - that the step relation was a partial function (i.e., it was
      deterministic), and

    - a strong progress lemma, stating that every term is either a
      value or can take a step.

    Prove or disprove these for the combined language. *)
(** 前には、plus式とif式について、以下のことを別々に証明しました...

    - ステップ関係が部分関数であること(つまり、決定性を持つこと)。

    - すべての項が値であるか、1ステップ進むことができるかを主張する強進行補題。

    結合した言語について、これらの性質を証明、または反証しなさい。*)

(* FILL IN HERE *)
(** [] *)
End Combined.


(* ########################################################### *)
(* * Small-Step Imp *)
(** * スモールステップ Imp *)

(* For a more serious example, here is the small-step version of the
    Imp operational semantics.  Although the definitions are bigger,
    the basic ideas are exactly the same as what we've seen above. *)
(** より本気の例として、Impの操作的意味論のスモールステップ版を示します。
    定義はより大きくなりますが、基本的な考え方は上述のものとまったく同じです。*)

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
    AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
    APlus (ANum n1) (ANum n2) / st ==>a ANum (plus n1 n2)
  | AS_Plus1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
    (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
    (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (AMult (a1) (a2)) / st ==>a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (AMult v1 a2) / st ==>a (AMult v1 a2')

  where " t '/' st '==>a' t' " := (astep st t t').

Reserved Notation " t '/' st '==>b' t' " (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st ==>b
    (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BEq a1 a2) / st ==>b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BEq v1 a2) / st ==>b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st ==>b
             (if (ble_nat n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
    a1 / st ==>a a1' ->
    (BLe a1 a2) / st ==>b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ==>a a2' ->
    (BLe v1 a2) / st ==>b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
    (BNot BTrue) / st ==>b BFalse
  | BS_NotFalse : forall st,
    (BNot BFalse) / st ==>b BTrue
  | BS_NotStep : forall st b1 b1',
    b1 / st ==>b b1' ->
    (BNot b1) / st ==>b (BNot b1')
  | BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st ==>b BTrue
  | BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st ==>b BFalse
  | BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st ==>b BFalse
  | BS_AndTrueStep : forall st b2 b2',
    b2 / st ==>b b2' ->
    (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
    b1 / st ==>b b1' ->
    (BAnd b1 b2) / st ==>b (BAnd b1' b2)

  where " t '/' st '==>b' t' " := (bstep st t t').

(* Notice that we didn't actually bother to define boolean values --
    they aren't needed in the definition of [==>b] (why?), though
    they might be if our language were a bit larger. *)
(** 実際にはブール値の定義にかかずらってはいなかったことに注意します。
    [==>b] の定義にはブール値の定義は必要ありません(なぜでしょう？)。
    言語がちょっと大きかったら必要になったかもしれませんが。*)

(* The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [SKIP] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [SKIP] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [SKIP], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [WHILE] command by transforming it into a
         conditional followed by the same [WHILE].

         (There are other ways of achieving the desired effect, but
         they all share the feature that the original [WHILE] command
         needs to be saved somewhere while a single copy of the loop
         body is being evaluated.) *)
(** コマンドの意味論は興味深い部分です。
    うまくやるために2つの小さなトリックを使います:

       - [SKIP] を「コマンド値」("command value")として使います。
         つまり、正規形に逹したコマンドです。

            - 代入コマンドは[SKIP]に簡約されます(その際に状態を更新します)。

            - コマンド合成は、左側の部分コマンドが[SKIP]に簡約されるのを待って、
              それを捨ててしまいます。そして続けて右側の部分コマンドの簡約をします。

       - [WHILE]コマンドの簡約は、条件文とそれに続く同じ[WHILE]コマンドになります。

         (求められる効果を得るために他にもいろいろな方法はありますが、
          いずれも、
          もとの[WHILE]コマンドをどこかに保存して、
          ループ本体の1コピーを評価することには変わりありません。) *)

Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st ==>a a' ->
    (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
    (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st ==> c1' / st' ->
    (c1 ; c2) / st ==> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
    IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
    IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b / st ==>b b' ->
    IFB b THEN c1 ELSE c2 FI / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
        (WHILE b DO c1 END) / st
    ==> (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

(* ########################################################### *)
(* * Concurrent Imp *)
(** * 並列実行 Imp *)

(* Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)
(** 最後に、この定義スタイルの力を示すために、Imp に平行動作のコマンドを拡張しましょう。
    このコマンドは2つのサブコマンドを平行実行し、両者が終了した時点で終了します。
    スケジューリングの予測不能性を反映して、
    サブコマンドのアクションは任意の順序でインターリーブします。
    しかし、同じメモリをシェアし、同じ変数を読み書きすることでコミュニケーションできます。*)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "PAR" ].

Notation "'SKIP'" :=
  CSkip.
Notation "l '::=' a" :=
  (CAss l a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
    a / st ==>a a' ->
    (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
    (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
    c1 / st ==> c1' / st' ->
    (c1 ; c2) / st ==> (c1' ; c2) / st'
  | CS_SeqFinish : forall st c2,
    (SKIP ; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
    (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
    (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
    b /st ==>b b' ->
    (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
    (WHILE b DO c1 END) / st ==>
             (IFB b THEN (c1; (WHILE b DO c1 END)) ELSE SKIP FI) / st
  (* New: *)
  | CS_Par1 : forall st c1 c1' c2 st',
    c1 / st ==> c1' / st' ->
    (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
    c2 / st ==> c2' / st' ->
    (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
    (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cstepmany := refl_step_closure cstep.

Notation " t '/' st '==>*' t' '/' st' " :=
   (refl_step_closure cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(* Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value... *)
(** この言語のいろいろな興味深い性質の中でも格別なものは、次のプログラムが、
    変数[X]にどのような値を入れても停止するという事実です... *)

Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

(* In particular, it can terminate with [X] set to [0]: *)
(** 特に、[X]を[0]にしても停止できます: *)

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  ==>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply rsc_step. apply CS_Par1.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  eapply rsc_refl.
  reflexivity. Qed.

(* It can also terminate with [X] set to [2]: *)
(** [X]を[2]にしても停止します: *)

Example par_loop_example_2:
  exists st',
       par_loop / empty_state ==>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.

  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfTrue.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply rsc_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_SeqFinish.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  eapply rsc_refl.
  reflexivity. Qed.

(* More generally... *)
(** より一般に... *)

(* **** Exercise: 3 stars, optional *)
(** **** 練習問題: ★★★, optional *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>* par_loop / (update st X (S n)).
Proof.
  (* FILL IN HERE *) Admitted.

(* **** Exercise: 3 stars, optional *)
(** **** 練習問題: ★★★, optional *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.

(* ... the above loop can exit with [X] having any value
    whatsoever. *)
(** ... 上のループは[X]がどんな値をとっても抜け出せます。 *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ==>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_state).
    split; unfold update; reflexivity.

  rename x into st.
  destruct H as [H' [HX HY]].
  exists (update st Y 1). split.
  eapply rsc_trans with (par_loop,st). apply H'.
  eapply rsc_step. apply CS_Par1. apply CS_Ass.
  eapply rsc_step. apply CS_Par2. apply CS_While.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply rsc_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply rsc_step. apply CS_Par2. apply CS_IfFalse.
  eapply rsc_step. apply CS_ParDone.
  apply rsc_refl.

  rewrite update_neq. assumption. reflexivity.
Qed.

End CImp.

