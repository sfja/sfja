(** * UseTactics_J:Coq用タクティックライブラリのご紹介 *)
(* * UseTactics: Tactic Library for Coq: a gentle introduction *)

(* $Date: 2011-04-20 14:26:52 -0400 (Wed, 20 Apr 2011) $ *)
(* Chapter maintained by Arthur Chargueraud *)

(* Coq comes with a set of builtin tactics, such as [reflexivity],
    [intros], [inversion] and so on. While it is possible to conduct
    proofs using only those tactics, you can significantly increase
    your productivity by working with a set of more powerful tactics.
    This chapter describes a number of such very useful tactics, which,
    for various reasons, are not yet available by default in Coq.
    These tactics are defined in the [LibTactics.v] file. *)
(** Coqはビルトインのタクティックの集合を持っています。[reflexivity]、[intros]、
    [inversion]などです。これらのタクティックだけで証明を構成することは可能ですが、
    より強力なタクティックの集合を使うことで、生産性を飛躍的に上げることができます。
    この章では、とても便利なのに、
    いろいろな理由でデフォルトのCoqでは用意されていないたくさんのタクティックを説明します。
    それらのタクティックは、[LibTactics_J.v]ファイルに定義されています。 *)

Require Import LibTactics_J.

(* Remark: SSReflect is another package providing powerful tactics.
    The library "LibTactics" differs from "SSReflect" in two respects:
        - "SSReflect" was primarily developed for proving mathematical
          theorems, whereas "LibTactics" was primarily developed for proving
          theorems on programming languages. In particular, "LibTactics"
          provides a number of useful tactics that have no counterpart in the
          "SSReflect" package.
        - "SSReflect" entirely rethinks the presentation of tactics,
          whereas "LibTactics" mostly stick to the traditional
          presentation of Coq tactics, simply providing a number of
          additional tactics.  For this reason, "LibTactics" is
          probably easier to get started with than "SSReflect". *)
(** 注記: SSReflect は強力なタクティックを提供する別のパッケージです。
    ライブラリ"LibTactics"は"SSReflect"と次の2点で異なります:
        - "SSReflect"は主として数学の定理を証明するために開発されました。
          一方、"LibTactics"は主としてプログラミング言語の定理の証明のために開発されました。
          特に"LibTactics"は、"SSReflect"パッケージには対応するものがない、
          いくつもの有用なタクティックを提供します。
        - "SSReflect"はタクティックの提示方法を根底から考え直しています。
          一方、"LibTactics"はCoqタクティックの伝統的提示方法をほとんど崩していません。
          このことからおそらく"LibTactics"の方が"SSReflect"よりとっつきやすいと思われます。*)

(* This chapter is a tutorial focusing on the most useful features
    from the "LibTactics" library. It does not aim at presenting all
    the features of "LibTactics". The complete documentation of the
    tactics can be found in the source file [LibTactics.v]. Moreover,
    demos illustrating the working of all the tactics can be found in
    the file [LibTacticsDemos.v]. *)
(** この章は"LibTactics"ライブラリの最も便利な機能に焦点を当てたチュートリアルです。
    "LibTactics"のすべての機能を示すことを狙ってはいません。
    タクティックの完全なドキュメンテーションはソースファイル[LibTactics_J.v]にあります。
    さらに、タクティックのはたらきを見せるデモは、ファイル[LibTacticsDemos_J.v]にあります。
    (訳注:原文ファイル群にも LibTacticsDemos.v は含まれていません。
    このファイル名でネット検索してみてください。) *)

(* The tactics are illustrated mostly through examples taken from the
    core chapters of the "Software Foundations" course. To illustrate
    the various ways in which a given tactic can be used, we'll use a
    tactic that duplicates a given goal. More precisely, [dup] produces
    two copies of the current goal, and [dup n] produces [n] copies of it. *)
(** タクティックの説明にはほとんど、「ソフトウェアの基礎」
    ("Software Foundations")のコースの主要な章から抽出した例を使います。
    タクティックのいろいろな使い方を説明するために、ゴールを複製するタクティックを使います。
    より詳しく言うと、[dup]は現在のゴールを2つにコピーします。
    また[dup n]はゴールのn個のコピーを作ります。*)


(* ####################################################### *)
(* * Tactics for introduction and case analysis *)
(** * 導入と場合分けについてのタクティック *)

(* This section presents the following tactics:
    - [introv], for saving time in the naming of hypotheses,
    - [inverts], for improving the [inversion] tactic,
    - [cases], for performing a case analysis without losing information,
    - [cases_if], for automating case analysis on the argument of [if]. *)
(** この節では、以下のタクティックを説明します:
    - [introv] :仮定に名前をつける時間を省くのに使います
    - [inverts] :[inversion]タクティックの改良です
    - [cases] :情報を失わずに場合分けします
    - [cases_if] :[if]の引数について自動的に場合分けします *)


(* ####################################################### *)
(* ** The tactic [introv] *)
(** ** タクティック[introv] *)

Module IntrovExamples.
  Require Import Stlc_J.
  Import Imp_J STLC.

(* The tactic [introv] allows to automatically introduce the
    variables of a theorem and explicitly name the hypotheses
    involved. In the example shown next, the variables [c],
    [st], [st1] and [st2] involved in the statement of determinacy
    need not be named explicitly, because their name where already
    given in the statement of the lemma. On the contrary, it is
    useful to provide names for the two hypotheses, [E1] and [E2]. *)
(** タクティック[introv]は、定理の変数を自動的に導入し、生成される仮定に明示的に名前を付けます。
    次の例では、決定性の主張に関する変数[c]、[st]、[st1]、[st2]
    には明示的に命名する必要はありません。これらは補題の主張の中で既に名前が付けられているからです。
    これに対して、2つの仮定[E1]と[E2]には名前をつけると便利です。 *)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  introv E1 E2. (* was [intros c st st1 st2 E1 E2] *)
Admitted.

(* When there is no hypothesis to be named, one can call
    [introv] without any argument. *)
(** 仮定に名前をつける必要がない場合には、引数なしで[introv]を呼ぶことができます。*)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  introv. (* was [intros c st st'] *)
Admitted.


(* The tactic [introv] also applies to statements in which
    [forall] and [->] are interleaved. *)
(** タクティック[introv]は[forall]と[->]が交互に現れる主張にも適用できます。 *)

Theorem ceval_deterministic': forall c st st1,
  (c / st || st1) -> forall st2, (c / st || st2) -> st1 = st2.
Proof.
  introv E1 E2. (* was [intros c st st1 E1 st2 E2] *)
Admitted.

(* Like the arguments of [intros], the arguments of [introv]
    can be structured patterns. *)
(** [intros]と同様、[introv]も、構造化パターンを引数にとることができます。*)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  introv [i E].
  (* was [intros c st st' [i E].], which is itself short
     for [intros c st st' H. destruct H as [i E].] *)
Admitted.

(* Remark: the tactic [introv] works even when definitions
    need to be unfolded in order to reveal hypotheses. *)
(** 注記: タクティック[introv]は、
    定義をunfoldしないと仮定が出てこない場合にも使うことができます。 *)

End IntrovExamples.


(* ####################################################### *)
(* ** The tactic [inverts] *)
(** ** タクティック[inverts] *)

Module InvertsExamples.
  Require Import Stlc_J Equiv_J Imp_J.
  Import STLC.

(* The [inversion] tactic of Coq is not very satisfying for
    three reasons. First, it produces a bunch of equalities
    which one typically wants to substitute away, using [subst].
    Second, it introduces meaningless names for hypotheses.
    Third, a call to [inversion H] does not remove [H] from the
    context, even though in most cases an hypothesis is no longer
    needed after being inverted. The tactic [inverts] address all
    of these three issues. It is intented to be used in place of
    the tactic [inversion]. *)
(** Coqの[inversion]タクティックは3つの点で十分なものだと言えません。
    1つ目は、[inversion]は、[subst]で置換して消してしまいたいような、
    たくさんの等式を生成することです。
    2つ目は、仮定に意味のない名前を付けることです。
    3つ目は、[inversion H]は、ほとんどの場合[H]を後で使うことはないにもかかわらず、
    コンテキストから[H]を消去しないことです。
    タクティック[inverts]はこの3つの問題すべてを扱います。
    このタクティックは、タクティック[inversion]にとって代わることを意図したものです。*)

(* The following example illustrates how the tactic [inverts H]
    behaves mostly like [inversion H] except that it performs the
    appropriate substitutions. *)
(** 次の例は、タクティック[inverts H]が、
    置換を適切に行う以外は[inversion H]と同様にはたらくことを示しています。*)

Theorem skip_left: forall c,
  cequiv (SKIP; c) c.
Proof.
  introv. split; intros H.
  dup. (* duplicate the goal for comparison *)
  (* was: *)
  inversion H. subst. inversion H2. subst. assumption.
  (* now: *)
  inverts H. inverts H2. assumption.
Admitted.

(* A slightly more interesting example appears next. *)
(** 次にもう少し興味深い例を見てみましょう。*)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1  ->
  c / st || st2 ->
  st1 = st2.
Proof.
  introv E1 E2. generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2.
  admit. admit. (* skip some basic cases *)
  dup. (* duplicate the goal for comparison *)
  (* was: *) inversion E2. subst. admit.
  (* now: *) inverts E2. admit.
Admitted.

(* The tactic [inverts H as.] is like [inverts H] except that the
    variables and hypotheses being produced are placed in the goal
    rather than in the context. This strategy allows naming those
    new variables and hypotheses explicitly, using either [intros]
    or [introv]. *)
(** タクティック[inverts H as.]は[inverts H]と同様ですが、次の点が違います。
    [inverts H as.]では、生成される変数と仮定がコンテキストではなくゴールに置かれます。
    この戦略により、
    これらの変数と仮定に[intros]や[introv]を使って明示的に名前を付けることができるようになります。
 *)

Theorem ceval_deterministic': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  introv E1 E2. generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2;
    inverts E2 as.
  Case "E_Skip". reflexivity.
  Case "E_Ass".
    (* Observe that the variable [n] is not automatically
       substituted because, contrary to [inversion E2; subst],
       the tactic [inverts E2] does not substitute the equalities
       that exist before running the inversion. *)
    (* new: *) subst n.
    reflexivity.
  Case "E_Seq".
    (* Here, the newly created variables can be introduced
       using intros, so they can be assigned meaningful names,
       for example [st3] instead of [st'0]. *)
    (* new: *) intros st3 Red1 Red2.
    assert (st' = st3) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st3.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      (* In an easy case like this one, there is no need to
         provide meaningful names, so we can just use [intros] *)
      (* new: *) intros.
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      (* new: *) intros.
      rewrite H in H5. inversion H5.
  (* The other cases are similiar *)
Admitted.

(* In the particular case where a call to [inversion] produces
    a single subgoal, one can use the syntax [inverts H as H1 H2 H3]
    for calling [inverts] and naming the new hypotheses [H1], [H2]
    and [H3]. In other words, the tactic [inverts H as H1 H2 H3] is
    equivalent to [invert H; introv H1 H2 H3]. An example follows. *)
(** [inversion]を使ったとするとゴールが1つだけできる場合に、[inverts]を
    [inverts H as H1 H2 H3]の形で呼ぶことができます。このとき新しい仮定は
    [H1]、[H2]、[H3]と名付けられます。言い換えると、タクティック[inverts H as H1 H2 H3]
    は、[invert H; introv H1 H2 H3]と同じです。例を示します。*)

Theorem skip_left': forall c,
  cequiv (SKIP; c) c.
Proof.
  introv. split; intros H.
  inverts H as U V. (* new hypotheses are named [U] and [V] *)
  inverts U. assumption.
Admitted.

(* A more involved example follows. In particular, it shows that
    the name of an inverted hypothesis can be reused. *)
(** より複雑な例です。特に、invertされた仮定の名前を再利用できることを示しています。*)

Example typing_nonexample_1 :
  ~ exists T,
      has_type empty
        (tm_abs a ty_Bool
            (tm_abs b ty_Bool
               (tm_app (tm_var a) (tm_var b))))
        T.
Proof.
  dup 3.

  (* The old proof: *)
  intros C. destruct C.
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.

  (* The new proof: *)
  intros C. destruct C.
  inverts H as H1.
  inverts H1 as H2.
  inverts H2 as H3.
  inverts H3 as H4.
  inverts H4.

  (* The new proof, alternative: *)
  intros C. destruct C.
  inverts H as H.
  inverts H as H.
  inverts H as H.
  inverts H as H.
  inverts H.
Qed.

End InvertsExamples.

(* Note: in the rare cases where one need to perform an inversion
    on an hypothesis [H] without clearing [H] from the context,
    one can use the tactic [inverts keep H], where the keyword [keep]
    indicates that the hypothesis should be kept in the context. *)
(** 注意: 稀に、仮定[H]をinvertするときに[H]をコンテキストから除去したくない場合があります。
    その場合には、タクティック[inverts keep H]を使うことができます。
    キーワード[keep]は仮定をコンテキストに残せということを示しています。*)


(* ####################################################### *)
(* ** The tactics [cases] and [cases_if] *)
(** ** タクティック[cases]と[cases_if] *)

Module CasesExample.
  Require Import Stlc_J.
  Import STLC.

(* The tactic [cases E] is a shorthand for [remember E as x; destruct x],
    with the difference that it generates the symmetric of the
    equality produced by [remember]. For example, [cases] would
    produce the equality [beq_id k1 k2 = true] rather than the
    equality [true = beq_id k1 k2], the latter being fairly awkward
    to read. The tactics [cases E as H] allows specifying the name
    to be used for the generated equality.

    Remark: [cases] is quite similar to [case_eq]. For the sake of
    compatibility with [remember] and [case_eq], the library
    "LibTactics" provides a tactic called [cases'] that generates exactly
    the same equalities as [remember] or [case_eq] would, i.e., producing
    an equality in the form [true = beq_id k1 k2] rather than
    [beq_id k1 k2 = true]. The following examples illustrate the
    behavior of the tactic [cases' E as H]. *)
(** タクティック[cases E]は、[remember E as x; destruct x] の略記法です。
    しかしそれだけでなく、[remember]が生成する等式の右辺と左辺を逆にしたものを生成します。
    例えば、[cases]は、等式 [true = beq_id k1 k2] ではなく等式 [beq_id k1 k2 = true]
    を作ります。なぜなら、[true = beq_id k1 k2] は読むのにかなり不自然な形だからです。
    タクティック [cases E as H] の形にすると、生成された等式に名前を付けることができます。

    注記: [cases] は [case_eq] にかなり近いです。
    [remember] および [case_eq] との互換性のために、ライブラリ"LibTactics"には
    [cases'] というタクティックが用意されています。
    [cases'] は [remember] および [case_eq] とまったく同じ等式を生成します。
    つまり、[beq_id k1 k2 = true] ではなく [true = beq_id k1 k2] という形の等式です。
    次の例は、タクティック[cases' E as H]の振る舞いを表しています。*)

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.
  dup.

  (* The old proof: *)
  remember (beq_id k1 k2) as b. destruct b.
    apply beq_id_eq in Heqb. subst. reflexivity.
    reflexivity.

  (* The new proof: *)
  cases' (beq_id k1 k2) as E.
    apply beq_id_eq in E. subst. reflexivity.
    reflexivity.
Qed.

(* The tactic [cases_if] calls [cases E] on the first expression [E]
    that appears in the goal or in the context as argument of a [if].
    So, the tactic [cases_if] saves the need to copy-past an expression
    that already occurs in the goal.
    Here again, for compatibility reasons, the library provides a tactic
    called [cases_if'], and the syntax [cases_if' as H] allows specifying
    the name of the generated equalities. *)
(** タクティック[cases_if]はゴールまたはコンテキストの[if]の引数として現れる式[E]に対して
    [cases E]を呼びます。このため、タクティック[cases_if]を使うと、
    ゴールに既に現れている式をコピーする必要がなくなります。
    先と同様、互換性のため、ライブラリには [cases_if'] というタクティックが用意されています。
    また [cases_if' as H] という形で、生成される等式に名前をつけることができます。*)

Theorem update_same' : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.

  (* The new proof: *)
  cases_if' as E.
    apply beq_id_eq in E. subst. reflexivity.
    reflexivity.
Qed.

End CasesExample.



(* ####################################################### *)
(* * Tactics for n-ary connectives *)
(** * n-引数論理演算のためのタクティック *)

(* Because Coq encodes conjunctions and disjunctions using binary
    constructors [/\] and [\/], working with a conjunction or a
    disjunction of [N] facts can turn out to be quite cumbursome.
    For this reason, "LibTactics" provides tactics offering direct
    support for n-ary conjunctions and disjunctions. It also provides
    direct support for n-ary existententials. *)
(** Coqは and と or を2引数コンストラクタ[/\]および[\/]でコード化するため、
    [N]個の事実についての and や or の扱いがとても面倒なものになります。
    このため、"LibTactics"では n個の and と or を直接サポートするタクティックを提供します。
    さらに、n個の存在限量に対する直接的サポートも提供します。*)

(* This section presents the following tactics:
    - [splits] for decomposing n-ary conjunctions,
    - [branch] for decomposing n-ary disjunctions,
    - [exists] for proving n-ary existentials. *)
(** この節では以下のタクティックを説明します:
    - [splits] :n個の and を分解します
    - [branch] :n個の or を分解します
    - [exists] :n個の存在限量の証明をします。 *)

Module NaryExamples.
  Require Import References_J SfLib_J.
  Import STLCRef.


(* ####################################################### *)
(* ** The tactic [splits] *)
(** ** タクティック [splits] *)

(* The tactic [splits] applies to a goal made of a conjunction 
    of [n] propositions and it produces [n] subgoals. For example,
    it decomposes the goal [G1 /\ G2 /\ G3] into the three subgoals
    [G1], [G2] and [G3]. *)
(** タクティック[splits]は、[n]個の命題の and に適用され、[n]個のサブゴールを作ります。
    例えば、ゴール[G1 /\ G2 /\ G3]を3つのサブゴール[G1]、[G2]、[G3]に分解します。 *)

Lemma demo_splits : forall n m,
  n > 0 /\ n < m /\ m < n+10 /\ m <> 3.
Proof.
  intros. splits.
Admitted.


(* ####################################################### *)
(* ** The tactic [branch] *)
(** ** タクティック [branch] *)

(* The tactic [branch k] can be used to proved a n-ary disjunction.
    For example, if the goal takes the form [G1 \/ G2 \/ G3],
    the tactic [branch 2] leaves only [G2] as subgoal. The following
    example illustrates the behavior of the [branch] tactic. *)
(** タクティック [branch k] は n個の or の証明に使うことができます。
    例えば、ゴールが [G1 \/ G2 \/ G3] という形のとき、
    タクティック [branch 2] は [G2] だけをサブゴールとします。
    次の例は[branch]タクティックの振る舞いを表しています。*)

Lemma demo_branch : forall n m,
  n < m \/ n = m \/ m < n.
Proof.
  intros.
  destruct (lt_eq_lt_dec n m) as [[H1|H2]|H3].
  branch 1. apply H1.
  branch 2. apply H2.
  branch 3. apply H3.
Qed.


(* ####################################################### *)
(* ** The tactic [exists] *)
(** ** タクティック [exists] *)

(* The library "LibTactics" introduces a notation for n-ary
    existentials. For example, one can write [exists x y z, H]
    instead of [exists x, exists y, exists z, H]. Similarly,
    the library provides a n-ary tactic [exists a b c], which is a
    shorthand for [exists a; exists b; exists c]. The following
    example illustrates both the notation and the tactic for
    dealing with n-ary existentials. *)
(** ライブラリ "LibTactics" は n個の存在限量についての記法を用意しています。
    例えば、[exists x, exists y, exists z, H] と書く代わりに
    [exists x y z, H] と書くことができます。
    同様に、ライブラリはn引数のタクティック[exists a b c]を提供します。
    これは、[exists a; exists b; exists c]の略記法です。
    次の例はn個の存在限量についての記法とタクティックを表しています。*)

Theorem progress : forall ST t T st,
  has_type empty ST t T ->
  store_well_typed ST st ->
  value t \/ exists t' st', t / st ==> t' / st'.
  (* was: [value t \/ exists t', exists st', t / st ==> t' / st'] *)
Proof with eauto.
  intros ST t T st Ht HST. remember (@empty ty) as Gamma.
  (has_type_cases (induction Ht) Case); subst; try solve by inversion...
  Case "T_App".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve by inversion.
      destruct IHHt2 as [Ht2p | Ht2p]...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tm_app (tm_abs x T t) t2') st'...
        (* was: [exists (tm_app (tm_abs x T t) t2'). exists st'...] *)
Admitted.

(* Remark: a similar facility for n-ary existentials is provided
    by the module [Coq.Program.Syntax] from the standard library,
    except that this facility only works up to arity 4, whereas
    [LibTactics] supports arities up to 10. *)
(** 注記: n個の存在限量についての同様の機能が標準ライブラリのモジュール
    [Coq.Program.Syntax]で提供されています。ただ、
    このモジュールのものは限量対象が4つまでしか対応していませんが、
    [LibTactics]は10個までサポートしています。*)

End NaryExamples.


(* ####################################################### *)
(* * Tactics for working with equality *)
(** * 等式を扱うタクティック *)

(* One of the major weakness of Coq compared with other interactive
    proof assistants is its relatively poor support for reasoning
    with equalities. The tactics described next aims at simplifying
    pieces of proof scripts manipulating equalities. *)
(** 他の対話的証明支援器と比べたCoqの大きな弱点の一つは、
    等式に関する推論のサポートが比較的貧弱なことです。
    次に説明するタクティックは、等式を扱う証明記述を簡単にすることを狙ったものです。*)

(* This section presents the following tactics:
    - [asserts_rewrite] for introducing an equality to rewrite with,
    - [cuts_rewrite], which is similar except subgoals are swapped,
    - [substs] for improving the [subst] tactic,
    - [fequals] for improving the [f_equal] tactic,
    - [applys_eq] for proving [P x y] using an hypothesis [P x z],
      automatically generating the equality [y = z]. *)
(** この節で説明するタクティックは次のものです:
    - [asserts_rewrite] : 書き換えのための等式を導入します
    - [cuts_rewrite] : サブゴールが交換される以外は同じです
    - [substs] : [subst] タクティックを改良します
    - [fequals] : [f_equal] タクティックを改良します
    - [applys_eq] : 仮定 [P x z] を使って、等式 [y = z] を自動生成し、
      [P x y] を証明します *)

Module EqualityExamples.


(* ####################################################### *)
(* ** The tactics [asserts_rewrite] and [cuts_rewrite] *)
(** ** タクティック [asserts_rewrite] と [cuts_rewrite] *)

(* The tactic [asserts_rewrite (E1 = E2)] replaces [E1] with [E2] in
    the goal, and produces the goal [E1 = E2]. *)
(** タクティック [asserts_rewrite (E1 = E2)] はゴール内の [E1] を [E2] で置換し、
    ゴール [E1 = E2] を生成します。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.
  (* The old proof: *)
  intros n m.
  assert (H: 0 + n = n). reflexivity. rewrite -> H.
  reflexivity.

  (* The new proof: *)
  intros n m.
  asserts_rewrite (0 + n = n).
    reflexivity. (* subgoal [0+n = n] *)
    reflexivity. (* subgoal [n*m = m*n] *)
Qed.

(* Remark: the syntax [asserts_rewrite (E1 = E2) in H] allows
     rewriting in the hypothesis [H] rather than in the goal. *)
(*** 注記: [asserts_rewrite (E1 = E2) in H] と書いた場合、
     ゴールの代わりに仮定 [H] を書き換えます。 *)

(* The tactic [cuts_rewrite (E1 = E2)] is like
    [asserts_rewrite (E1 = E2)], except that the equality [E1 = E2]
    appears as first subgoal. *)
(** タクティック [cuts_rewrite (E1 = E2)] は
    [asserts_rewrite (E1 = E2)] と同様ですが、
    等式 [E1 = E2] が最初のサブゴールになります。*)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  cuts_rewrite (0 + n = n).
    reflexivity. (* subgoal [n*m = m*n] *)
    reflexivity. (* subgoal [0+n = n] *)
Qed.

(* More generally, the tactics [asserts_rewrite] and [cuts_rewrite]
    can be provided a lemma as argument. For example, one can write
    [asserts_rewrite (forall a b, a*(S b) = a*b+a)].
    This formulation is useful when [a] and [b] are big terms,
    since there is no need to repeat their statements. *)
(** より一般には、タクティック [asserts_rewrite] と [cuts_rewrite] 
    は補題を引数としてとることができます。
    例えば 
    [asserts_rewrite (forall a b, a*(S b) = a*b+a)] と書くことができます。
    この記法は[a]や[b]が大きな項であるとき便利です。
    その大きな項を繰り返さずに済むからです。*)

Theorem mult_0_plus'' : forall u v w x y z: nat,
  (u + v) * (S (w * x + y)) = z.
Proof.
  intros. asserts_rewrite (forall a b, a*(S b) = a*b+a).
    (* first subgoal:  [forall a b, a*(S b) = a*b+a] *)
    (* second subgoal: [(u + v) * (w * x + y) + (u + v) = z] *)
Admitted.


(* ####################################################### *)
(* ** The tactic [substs] *)
(** ** タクティック [substs] *)

(* The tactic [substs] is similar to [subst] except that it
    does not fail when the goal contains "circular equalities",
    such as [x = f x]. *)
(** タクティック [substs] は [subst] と同様ですが、[subst] と違い、
    ゴールが [x = f x] のような「循環する等式」を含むときも失敗しません。*)

Lemma demo_substs : forall x y (f:nat->nat),
  x = f x -> y = x -> y = f x.
Proof.
  intros. substs. (* [subst] would fail here *)
  assumption.
Qed.


(* ####################################################### *)
(* ** The tactic [fequals] *)
(** ** タクティック [fequals] *)

(* The tactic [fequals] is similar to [f_equal] except that it
    directly discharges all the trivial subgoals produced. Moreover,
    the tactic [fequals] features an enhanced treatment of equalities
    between tuples. *)
(** タクティック [fequals] は [f_equal] と同様ですが、
    生成される自明なサブゴールを直接解決してしまう点が違います。
    さらに、タクティック [fequals] はタプル間の等式の扱いが強化されています。*)

Lemma demo_fequals : forall (a b c d e : nat) (f : nat->nat->nat->nat->nat),
  a = 1 -> b = e -> e = 2 ->
  f a b c d = f 1 2 c 4.
Proof.
  intros. fequals.
  (* subgoals [a = 1], [b = 2] and [c = c] are proved, [d = 4] remains *)
Admitted.


(* ####################################################### *)
(* ** The tactic [applys_eq] *)
(** ** タクティック [applys_eq] *)

(* The tactic [applys_eq] is a variant of [eapply] that introduces
    equalities for subterms that do not unify. For example, assume
    the goal is the proposition [P x y] and assume we have the
    assumption [H] asserting that [P x z] holds. We know that we can
    prove [y] to be equal to [z]. So, we could call the tactic
    [assert_rewrite (y = z)] and change the goal to [P x z], but
    this would require copy-pasting the values of [y] and [z].
    With the tactic [applys_eq], we can call [applys_eq H 1], which
    proves the goal and leaves only the subgoal [y = z]. The value [1]
    given as argument to [applys_eq] indicates that we want an equality
    to be introduced for the first argument of [P x y] counting from
    the right. The three following examples illustrate the behavior
    of a call to [applys_eq H 1], a call to [applys_eq H 2], and a
    call to [applys_eq H 1 2]. *)
(** タクティック [applys_eq] は [eapply] の変種で、
    単一化できない部分項間の等式を導入します。
    例えば、ゴールが命題 [P x y] で、[P x z] が成立するという仮定[H]があるとします。
    また[y]と[z]が等しいことが証明できることはわかっているとします。
    すると、タクティック [assert_rewrite (y = z)] を呼び、ゴールを [P x z] 
    に変えることができます。
    しかしこれには、[y]と[z]の値のコピー&ペーストが必要になります。
    タクティック[applys_eq]を使うと、この場合 [applys_eq H 1] とできます。
    すると、ゴールは証明され、サブゴール [y = z] が残ります。
    [applys_eq]の引数の値[1]は、
    [P x y] の右から1番目の引数についての等式を導入したいことを表します。
    以下の3つの例は、それぞれ [applys_eq H 1]、[applys_eq H 2]、[applys_eq H 1 2]
    を呼んだときの振る舞いを示します。 *)

Axiom big_expression_using : nat->nat. (* Used in the example *)

Lemma demo_applys_eq_1 : forall (P:nat->nat->Prop) x y z,
  P x (big_expression_using z) ->
  P x (big_expression_using y).
Proof.
  introv H. dup.

  (* The old proof: *)
  assert (Eq: big_expression_using y = big_expression_using z).
    admit. (* Assume we can prove this equality somehow. *)
  rewrite Eq. apply H.

  (* The new proof: *)
  applys_eq H 1.
    admit. (* Assume we can prove this equality somehow. *)
Qed.

(* If the mismatch was on the first argument of [P] instead of
    the second, we would have written [applys_eq H 2]. Recall
    that the occurences are counted from the right. *)
(** もしミスマッチが[P]の第2引数ではなく第1引数だった場合には、
    [applys_eq H 2]と書きます。
    出現は右からカウントされることを思い出してください。*)

Lemma demo_applys_eq_2 : forall (P:nat->nat->Prop) x y z,
  P (big_expression_using z) x ->
  P (big_expression_using y) x.
Proof.
  introv H. applys_eq H 2.
Admitted.

(* When we have a mismatch on two arguments, we want to produce
    two equalities. To achieve this, we may call [applys_eq H 1 2].
    More generally, the tactic [applys_eq] expects a lemma and a
    sequence of natural numbers as arguments. *)
(** 2つの引数にミスマッチがある場合、2つの等式が欲しくなります。
    そのためには、[applys_eq H 1 2] とできます。
    より一般に、タクティック[applys_eq]は1つの補題と自然数の列を引数としてとります。*)

Lemma demo_applys_eq_3 : forall (P:nat->nat->Prop) x1 x2 y1 y2,
  P (big_expression_using x2) (big_expression_using y2) ->
  P (big_expression_using x1) (big_expression_using y1).
Proof.
  introv H. applys_eq H 1 2.
  (* produces two subgoals:
     [big_expression_using x1 = big_expression_using x2]
     [big_expression_using y1 = big_expression_using y2] *)
Admitted.

End EqualityExamples.


(* ####################################################### *)
(* * Some convenient shorthands *)
(** * 便利な略記法をいくつか *)

(* This section of the tutorial introduces a few tactics
    that help make proof scripts shorter and more readable:
    - [unfolds] (without argument) for unfolding the head definition,
    - [false] for replacing the goal with [False],
    - [gen] as a shorthand for [dependent generalize],
    - [skip] for skipping a subgoal (works with existential variables),
    - [sort] for moving propositions at the bottom of the proof context. *)
(** チュートリアルのこの節では、証明記述をより短かく、
    より読みやすくするのに役立つタクティックをいくつか紹介します:
    - [unfolds] (引数なし): 先頭の定義を unfold します
    - [false] : ゴールを [False] で置換します
    - [gen] : [dependent generalize] の略記法です
    - [skip] : サブゴールをスキップします(存在変数と組み合わせて使います)
    - [sort] : 証明コンテキストの下の命題を動かします *)


(* ####################################################### *)
(* ** The tactic [unfolds] *)
(** ** タクティック [unfolds] *)

Module UnfoldsExample.
  Require Import Hoare_J.

(* The tactic [unfolds] (without any argument) unfolds the
    head constant of the goal. This tactic saves the need to
    name the constant explicitly. *)
(** タクティック [unfolds] (引数なし) はゴールの先頭の定数を unfold します。
    このタクティックは定数を明示的に指名する手間を省きます。*)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe. dup.

  (* The old proof: *)
  unfold bassn. assumption.

  (* The new proof: *)
  unfolds. assumption.
Qed.

(* Remark: contrary to the tactic [hnf], which unfolds all the
    head constants, [unfolds] performs only a single unfolding. *)
(** 注記: タクティック[hnf]はすべての先頭の定数をunfoldしますが、
    これと対照的に[unfolds]は1つだけunfoldします。*)

(* Remark: the tactic [unfolds in H] can be used to unfold the
    head definition of the hypothesis [H]. *)
(** 注記: タクティック [unfolds in H] は仮定[H]の先頭の定義をunfoldします。*)

End UnfoldsExample.


(* ####################################################### *)
(* ** The tactics [false] and [tryfalse] *)
(** ** タクティック[false]と[tryfalse] *)

(* The tactic [false] can be used to replace any goal with [False].
    In short, it is a shorthand for [apply ex_falso_quodlibet].
    Moreover, [false] proves the goal if it contains an absurd
    assumption, such as [False] or [0 = S n], or if it contains
    contradictory assumptions, such as [x = true] and [x = false]. *)
(** タクティック[false]は任意のゴールを[False]に置換します。
    簡単に言うと、[apply ex_falso_quodlibet]の略記法です。
    さらに[false]は、不条理な仮定([False]や[0 = S n]など)
    や矛盾した仮定([x = true]と[x = false]など)を含むゴールを証明します。*)

Lemma demo_false :
  forall n, S n = 1 -> n = 0.
Proof.
  intros. destruct n. reflexivity. false.
Qed.

(* The tactic [tryfalse] is a shorthand for [try solve [false]]:
    it tries to find a contradiction in the goal. The tactic
    [tryfalse] is generally called after a case analysis. *)
(** タクティック[tryfalse]は [try solve [false]] の略記法です。
    このタクティックはゴールの矛盾を探します。
    タクティック[tryfalse]は一般に場合分けの後で呼ばれます。*)

Lemma demo_tryfalse :
  forall n, S n = 1 -> n = 0.
Proof.
  intros. destruct n; tryfalse. reflexivity.
Qed.


(* ####################################################### *)
(* ** The tactic [gen] *)
(** ** タクティック [gen] *)

(* The tactic [gen] is a shortand for [generalize dependent]
    that accepts several arguments at once. An invokation of
    this tactic takes the form [gen x y z]. *)
(** タクティック[gen]は [generalize dependent] の略記法です。
    たくさんの引数を一度に受けます。このタクティックは [gen x y z] という形で呼びます。*)

Module GenExample.
  Require Import Stlc_J.
  Import STLC.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S ->
     has_type empty v U ->
     has_type Gamma (subst v x t) S.
Proof.
  dup.

  (* The old proof: *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.

  (* The new proof: *)
  introv Htypt Htypv. gen S Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.
Qed.

End GenExample.


(* ####################################################### *)
(* ** The tactics [skip], [skip_rewrite] and [skip_goal] *)
(** ** タクティック[skip]、[skip_rewrite]、[skip_goal] *)

(* The ability to admit a given subgoal is very useful when
    constructing proofs. It gives the ability to focus first
    on the most interesting cases of a proof. The tactic [skip]
    is like [admit] except that it also works when the proof
    includes existential variables. Recall that existential
    variables are those whose name starts with a question mark,
    e.g. [?24], and which are typically introduced by [eapply]. *)
(** サブゴールをadmitできることは証明を構成するうえでとても便利です。
    証明の一番興味深いケースに最初にフォーカスできるようになるからです。
    タクティック[skip]は[admit]と似ていますが、
    証明が存在変数を含む場合にも機能します。
    存在変数とは、[?24]のように名前がクエスチョンマークから始まる変数で、
    典型的には[eapply]によって導入されるものであったことを思い出してください。*)

Module SkipExample.
  Require Import Stlc_J.
  Import STLC.

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
Proof.
  eapply rsc_step. skip. (* [admit] would not work here *)
  eapply rsc_step. skip. skip.
  (* Note that because some unification variables have
     not been instantiated, we still need to write
     [Admitted] instead of [Qed] at the end of the proof. *)
Admitted.

(* The tactic [skip H: P] adds the hypothesis [H: P] to the context,
    without checking whether the proposition [P] is true.
    It is useful for exploiting a fact and postponing its proof.
    Note: [skip H: P] is simply a shorthand for [assert (H:P). skip.] *)
(** タクティック [skip H: P] は仮定 [H: P] をコンテキストに追加します。
    このときに命題[P]が真かどうかのチェックはしません。
    このタクティックは、事実を、証明を後回しにして利用するのに便利です。
    注意: [skip H: P] は単に [assert (H:P). skip.] の略記法です。*)

Theorem demo_skipH : True.
Proof.
  skip H: (forall n m : nat, (0 + n) * m = n * m).
Admitted.

(* The tactic [skip_rewrite (E1 = E2)] replaces [E1] with [E2] in
    the goal, without checking that [E1] is actually equal to [E2]. *)
(** タクティック [skip_rewrite (E1 = E2)] はゴールの[E1]を[E2]で置換します。
    このときに[E1]が実際に[E2]と等しいかはチェックしません。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.

  (* The old proof: *)
  intros n m.
  assert (H: 0 + n = n). skip. rewrite -> H.
  reflexivity.

  (* The new proof: *)
  intros n m.
  skip_rewrite (0 + n = n).
  reflexivity.
Qed.

(* Remark: the tactic [skip_rewrite] can in fact be given a lemma
    statement as argument, in the same way as [asserts_rewrite]. *)
(** 注記: タクティック[skip_rewrite]は実際は[asserts_rewrite]
    と同じように補題を引数としてとることができます。*)

(* The tactic [skip_goal] adds the current goal as hypothesis.
    This cheat is useful to set up the structure of a proof by
    induction without having to worry about the induction hypothesis
    being applied only to smaller arguments. Using [skip_goal], one
    can construct a proof in two steps: first, check that the main
    arguments go through without waisting time on fixing the details
    of the induction hypotheses, and then focus on fixing the
    invokations of the induction hypothesis. *)
(** タクティック[skip_goal]は現在のゴールを仮定として追加します。
    このごまかしは帰納法による証明の構造の構成の際に、
    帰納法の仮定がより小さい引数だけに適用されるかを心配しないで済むため有用です。
    [skip_goal]を使うことで、証明を次の2ステップで構成できます：
    最初に、帰納法の仮定の細部の調整に時間を浪費せずに、主要な議論が通るかをチェックし、
    その後、帰納法の仮定の呼び出しの調整にフォーカスするというステップです。*)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  (* [skip_goal] creates an hypothesis called [IH] asserting
     that the statment of [ceval_deterministic] is true. *)
  skip_goal.
  (* Of course, if we call [assumption] here, then the goal is solved
     right away, but the point is to do the proof and use [IH]
     only at the places where we need an induction hypothesis. *)
  introv E1 E2. gen st2.
  (ceval_cases (induction E1) Case); introv E2; inverts E2 as.
  Case "E_Skip". reflexivity.
  Case "E_Ass".
    subst n.
    reflexivity.
  Case "E_Seq".
    intros st3 Red1 Red2.
    assert (st' = st3) as EQ1.
      SCase "Proof of assertion".
        (* was: [apply IHE1_1; assumption.] *)
        (* new: *) eapply IH. eapply E1_1. eapply Red1.
    subst st3.
    (* was: apply IHE1_2. assumption.] *)
    (* new: *) eapply IH. eapply E1_2. eapply Red2.
  (* The other cases are similiar. *)
Admitted.

End SkipExample.


(* ####################################################### *)
(* ** The tactic [sort] *)
(** ** タクティック [sort] *)

Module SortExamples.
  Require Import Imp_J.

(* The tactic [sort] reorganizes the proof context by placing
    all the variables at the top and all the hypotheses at the
    bottom, thereby making the proof context more readable. *)
(** タクティック[sort]は証明コンテキストを再構成し、変数が上に仮定が下になるようにします。
    これにより、証明コンテキストはより読みやすくなります。*)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2; inverts E2.
  admit. admit. (* Skipping some trivial cases *)
  sort. (* Observe how the context is reorganized *)
Admitted.

End SortExamples.


(* ####################################################### *)
(* * Tactics for advanced lemma instantiation *)
(** * 高度な補題具体化のためのタクティック *)

(* This last section describes a mechanism for instantiating a lemma
    by providing some of its arguments and leaving other implicit.
    Variables whose instantiation is not provided are turned into
    existentential variables, and facts whose instantiation is not
    provided are turned into subgoals.

    Remark: this instantion mechanism goes far beyond the abilities of
    the "Implicit Arguments" mechanism. The point of the instantiation
    mechanism described in this section is that you will no longer need
    to spend time figuring out how many underscore symbols you need to
    write. *)
(** この最後の節では、補題に引数のいくつかを与え、他の引数は明示化しないままで、
    補題を具体化するメカニズムについて記述します。
    具体値を与えられない変数は存在変数となり、具体化が与えられない事実はサブゴールになります。

    注記: この具体化メカニズムは「暗黙の引数」メカニズムをはるかに超越する能力を提供します。
    この節で記述する具体化メカニズムのポイントは、どれだけの '_' 
    記号を書かなければならないかの計算に時間を使わなくてよくなることです。*)

(* In this section, we'll use a useful feature of Coq for decomposing
    conjunctions and existentials. In short, a tactic like [intros] or
    [destruct] can be provided with a pattern [(H1 & H2 & H3 & H4 & H5)],
    which is a shorthand for [[H1 [H2 [H3 [H4 H5]]]]]]. For example,
    [destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].]
    can be rewritten in the form
    [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).] *)
(** この節では、Coq の便利な連言(and)と存在限量の分解機構を使います。
    簡単に言うと、[intros]や[destruct]は [[H1 [H2 [H3 [H4 H5]]]]]
    の略記法としてパターン [(H1 & H2 & H3 & H4 & H5)] をとることができます。
    例えば [destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].]
    は [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).] 
    と書くことができます。*)


(* ####################################################### *)
(* ** Working of [lets] *)
(** ** [lets]のはたらき *)

(* When we have a lemma (or an assumption) that we want to exploit,
    we often need to explicitly provide arguments to this lemma,
    writing something like:
    [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).]
    The need to write several times the "underscore" symbol is tedious.
    Not only we need to figure out how many of them to write down, but
    it also makes the proof scripts look prettly ugly. With the tactic
    [lets], one can simply write:
    [lets (T & Hctx & Hsub): typing_inversion_var Htypt.]

    In short, this tactic [lets] allows to specialize a lemma on a bunch
    of variables and hypotheses. The syntax is [lets I: E0 E1 .. EN],
    for building an hypothesis named [I] by applying the fact [E0] to the
    arguments [E1] to [EN]. Not all the arguments need to be provided,
    however the arguments that are provided need to be provided in the
    correct order. The tactic relies on a first-match algorithm based on
    types in order to figure out how the to instantiate the lemma with
    the arguments provided. *)
(** 利用したい補題(または仮定)がある場合、大抵、この補題に明示的に引数を与える必要があります。
    例えば次のような形です:
    [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).]
    何回も'_'記号を書かなければならないのは面倒です。
    何回書くかを計算しなければならないだけでなく、このことで証明記述がかなり汚なくもなります。
    タクティック[lets]を使うことで、次のように簡単に書くことができます:
    [lets (T & Hctx & Hsub): typing_inversion_var Htypt.]

    簡単に言うと、このタクティック[lets]は補題のたくさんの変数や仮定を特定します。
    記法は [lets I: E0 E1 .. EN] という形です。
    そうすると事実[E0]に引数[E1]から[EN]を与えて[I]という名前の仮定を作ります。
    すべての引数を与えなければならないわけではありませんが、
    与えなければならない引数は、正しい順番で与えなければなりません。
    このタクティックは、与えられた引数を使って補題をどうしたら具体化できるかを計算するために、
    型の上の first-match アルゴリズムを使います。*)

Module ExamplesLets.
  Require Import Subtyping_J.

(* To illustrate the working of [lets], assume that we want to
   exploit the following lemma. *)

Axiom typing_inversion_var : forall (G:context) (x:id) (T:ty),
  has_type G (tm_var x) T ->
  exists S, G x = Some S /\ subtype S T.

(* First, assume we have an assumption [H] with the type of the form
    [has_type G (tm_var x) T]. We can obtain the conclusion of the
    lemma [typing_inversion_var] by invoking the tactics
    [lets K: typing_inversion_var H], as shown next. *)
(** 最初に、型が [has_type G (tm_var x) T] である仮定[H]を持つとします。
    タクティック [lets K: typing_inversion_var H] 
    を呼ぶことで補題[typing_inversion_var]を結論として得ることができます。
    以下の通りです。*)

Lemma demo_lets_1 : forall (G:context) (x:id) (T:ty),
  has_type G (tm_var x) T -> True.
Proof.
  intros G x T H. dup.

  (* step-by-step: *)
  lets K: typing_inversion_var H.
  destruct K as (S & Eq & Sub).
  admit.

  (* all-at-once: *)
  lets (S & Eq & Sub): typing_inversion_var H.
  admit.

Qed.

(* Assume now that we know the values of [G], [x] and [T] and we
    want to obtain [S], and have [has_type G (tm_var x) T] be produced
    as a subgoal. To indicate that we want all the remaining arguments
    of [typing_inversion_var] to be produced as subgoals, we use a
    triple-underscore symbol [___]. (We'll later introduce a shorthand
    tactic called [forwards] to avoid writing triple underscores.) *)
(** 今、[G]、[x]、[T]の値を知っていて、[S]を得たいとします。
    また、サブゴールとして [has_type G (tm_var x) T] が生成されていたとします。
    [typing_inversion_var]
    の残った引数のすべてをサブゴールとして生成したいことを示すために、
    '_'を三連した記号[___]を使います。
    (後に、[___]を書くのを避けるために[forwards]という略記用タクティックを導入します。) *)

Lemma demo_lets_2 : forall (G:context) (x:id) (T:ty), True.
Proof.
  intros G x T.
  lets (S & Eq & Sub): typing_inversion_var G x T ___.
Admitted.

(* Usually, there is only one context [G] and one type [T] that are
    going to be suitable for proving [has_type G (tm_var x) T], so
    we don't really need to bother giving [G] and [T] explicitly.
    It suffices to call [lets (S & Eq & Sub): typing_inversion_var x].
    The variables [G] and [T] are then instantiated using existential
    variables. *)
(** 通常、[has_type G (tm_var x) T] を証明するのに適したコンテキスト
    [G]と型[T]は1つだけしかないので、
    実は[G]と[T]を明示的に与えることに煩わされる必要はありません。
    [lets (S & Eq & Sub): typing_inversion_var x] とすれば十分です。
    このとき、変数[G]と[T]は存在変数を使って具体化されます。*)

Lemma demo_lets_3 : forall (x:id), True.
Proof.
  intros x.
  lets (S & Eq & Sub): typing_inversion_var x ___.
Admitted.

(* We could be even more extreme and not give any argument to
    instantiate [typing_inversion_var]. In this case, three unification
    variables are introduced. *)
(** より極端に、[typing_inversion_var]の具体化のために引数をまったく与えないこともできます。
    この場合、3つの単一化変数が導入されます。*)

Lemma demo_lets_4 : True.
Proof.
  lets (S & Eq & Sub): typing_inversion_var ___.
Admitted.

(* Note: if we provide [lets] with only the name of the lemma as
    argument, it simply adds this lemma in the proof context, without
    trying to instantiate any of its arguments. *)
(** 注意: [lets]に補題の名前だけを引数として与えた場合、
    その補題が証明コンテキストに追加されるだけで、
    その引数を具体化しようとすることは行いません。*)

Lemma demo_lets_5 : True.
Proof.
  lets H: typing_inversion_var.
Admitted.

(* A last useful feature of [lets] is the double-underscore symbol,
    which allows skipping an argument when several arguments have
    the same type. In the following example, we want [m] to be
    instantiated as the value [3], but we want [n] to be instantiated
    using an existential variable. *)
(** [lets]の最後の便利な機能は '_' を2つ続けた記号[__]です。
    これを使うと、いくつかの引数が同じ型を持つとき引数を1つスキップできます。
    以下の例は、[m]を値[3]に具体化したい一方、[n]は存在変数を使って具体化したい場面です。*)

Lemma demo_lets_underscore :
  (forall n m, n <= m -> n < m+1) -> True.
Proof.
  intros H.

  (* If we do not use a double underscore, the first argument,
     which is [n], gets instantiated as 3. *)
  lets K: H 3. (* gives [K] of type [forall m, 3 <= m -> 3 < m+1] *)
    clear K.

  (* The double underscore preceeding [3] indicates that we want
     to skip a value that has the type [nat] (because [3] has
     the type [nat]). So, the variable [m] gets instiated as [3]. *)
  lets K: H __ 3. (* gives [K] of type [?X <= 3 -> ?X < 3+1] *)
    clear K.
Admitted.


(* Note: one can write [lets: E0 E1 E2] in place of [lets H: E0 E1 E2]
    when the name [H] needs not be mentioned in the proof script.

    Note: the tactics [lets] accepts up to five arguments. Another
    syntax if available for providing more than five arguments.
    It consists in using a list introduced with the keyword [>>],
    for example [lets H: (>> E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 10)]. *)
(** 注意: 証明記述の中で[H]の名前を言う必要がないとき、[lets H: E0 E1 E2] の代わりに
    [lets: E0 E1 E2] と書くことができます。

    注意: タクティック[lets]は5つまでの引数をとることができます。
    5個を越える引数を与えることができる場合に、別の構文があります。
    キーワード[>>]から始まるリストを使ったものです。
    例えば [lets H: (>> E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 10)] と書きます。 *)    

End ExamplesLets.


(* ####################################################### *)
(* ** Working of [applys], [forwards] and [specializes] *)
(** ** [applys]、[forwards]、[specializes]のはたらき *)

(* The tactics [applys], [forwards] and [specializes] are
    shorthand that may be used in place of [lets] to perform
    specific tasks.

    -- [forwards] is a shorthand for instantiating all the arguments
    of a lemma. More precisely, [forwards H: E0 E1 E2 E3] is the
    same as [lets H: E0 E1 E2 E3 ___], where the triple-underscore
    has the same meaning as explained earlier on.

    -- [applys] allows building a lemma using the advanced instantion
    mode of [lets], and then apply that lemma right away. So,
    [applys E0 E1 E2 E3] is the same as [lets H: E0 E1 E2 E3]
    followed with [eapply H] and then [clear H].

    -- [specializes] is a shorthand for instantiating in-place
    an assumption from the context with particular arguments.
    More precisely, [specializes H E0 E1] is the same as
    [lets H': H E0 E1] followed with [clear H] and [rename H' into H].

    Examples of use of [applys] appear further on. Several examples
    of use of [specializes] and [forwards] can be found in the
    tutorial file [UseAuto.v]. *)
(** タクティック[applys]、[forwards]、[specializes]は
    [lets]を特定の用途に使う場面での略記法です。

    - [forwards]は補題のすべての引数を具体化する略記法です。
      より詳しくは、[forwards H: E0 E1 E2 E3] は [lets H: E0 E1 E2 E3 ___]
      と同じです。ここで [___] の意味は前に説明した通りです。

    - [applys]は、[lets]の高度な具体化モードにより補題を構築し、
      それをすぐに使うことにあたります。
      これから、[applys E0 E1 E2 E3] は、 [lets H: E0 E1 E2 E3] の後
      [eapply H]、[clear H] と続けることと同じです。

    - [specializes]は、コンテキストの仮定を特定の引数でその場で具体化することの略記法です。
      より詳しくは、[specializes H E0 E1] は [lets H': H E0 E1] の後 
      [clear H]、[rename H' into H] と続けることと同じです。

    [applys]の使用例は以下で出てきます。
    [specializes]と[forwards]の使用例は、
    チュートリアルファイル[UseAuto_J.v]にいくつか含まれています。 *) 


(* ####################################################### *)
(* ** Example of instantiations *)
(** ** 具体化の例 *)

Module ExamplesInstantiations.
  Require Import Subtyping_J.

(* In the following proof, [lets] is used instead of [destruct]
    and [applys] is used instead of [apply] in several places.
    Those places indicated by a comment starting with "old:".
    The exercise consists in also using [lets] where indicated. *)
(** 以下の証明では、いくつかの場所で[lets]が[destruct]の代わりに、
    [applys]が[apply]の代わりに使われます。
    その場所は "old:"で始まるコメントで示されています。
    [lets]を使う練習問題も示されています。*)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S ->
     has_type empty v U ->
     has_type Gamma (subst v x t) S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  (tm_cases (induction t) Case); intros; simpl.
  Case "tm_var".
    rename i into y.

    (* An example where [destruct] is replaced with [lets] *)
    (* old: destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].*)
    (** <<
    (* old: destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].*) 
>> *)
    (* new: *) lets (T&Hctx&Hsub): typing_inversion_var Htypt.
    unfold extend in Hctx.
    remember (beq_id x y) as e. destruct e... (* [cases_if'] could be used here *)
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.

       (* A more involved example where [destruct] is replaced with [lets] *)
       (* old: destruct (free_in_context _ _ S empty Hcontra) as [T' HT']... *)
    (** <<
       (* old: destruct (free_in_context _ _ S empty Hcontra) as [T' HT']... *) 
>> *)
       (* new: *)
        lets [T' HT']: free_in_context S empty Hcontra...
        inversion HT'.
  Case "tm_app".

    (* Exercise: replace the following [destruct] with a [lets] *)
    (** <<
    (* 練習問題: 次の[destruct]を[lets]に換えなさい *)
>> *)
    (* old: destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
            eapply T_App... *)
    (** <<
    (* old: destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
            eapply T_App... *)
>> *)
    (* FILL IN HERE *) admit.

  Case "tm_abs".
    rename i into y. rename t into T1.

    (* Here is another example of using [lets] *)
    (* old: destruct (typing_inversion_abs _ _ _ _ _ Htypt). *)
    (** <<
    (* old: destruct (typing_inversion_abs _ _ _ _ _ Htypt). *)
>> *)
    (* new: *) lets (T2&Hsub&Htypt2): typing_inversion_abs Htypt.

    (* An example of where [apply with] can be replaced with [applys] *)
    (* old: apply T_Sub with (ty_arrow T1 T2)... *)
    (** <<
    (* old: apply T_Sub with (ty_arrow T1 T2)... *)
>> *)
    (* new: *) applys T_Sub (ty_arrow T1 T2)...
     apply T_Abs...
    remember (beq_id x y) as e. destruct e. (* [cases_if'] could be used here *)
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
  Case "tm_true".
    lets: typing_inversion_true Htypt...
  Case "tm_false".
    lets: typing_inversion_false Htypt...
  Case "tm_if".
    lets (Htyp1&Htyp2&Htyp3): typing_inversion_if Htypt...
  Case "tm_unit".
    (* An example where [assert] can be replaced with [lets] *)
    (* old: assert (subtype ty_Unit S) by apply (typing_inversion_unit _ _ Htypt)... *)
    (** <<
    (* old: assert (subtype ty_Unit S) by apply (typing_inversion_unit _ _ Htypt)... *)
>> *)
    (* new: *) lets: typing_inversion_unit Htypt...


Qed.

End ExamplesInstantiations.
