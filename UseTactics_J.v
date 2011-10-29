(** * UseTactics: Coq 用タクティックライブラリ: 入門編 *)
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
(**
   Coq には [reflexivity]、 [intros]、 [inversion] といった組み込みのタクティックがあります。組み込みのタクティックだけを使って証明をすることもできますが、より強力なタクティックを使えば飛躍的に証明の効率を上げることができます。本章では、そのような便利なタクティックを紹介します。これらのタクティックは様々な理由により、素の Coq では使うことができません。これらのタクティックは [LibTactics_J.v] ファイルで定義されています。
   *)

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

(**
   注: 強力なタクティックを提供するパッケージとしては他にも SSReflect があります。 [LibTactics_J] には二点、 SSReflect とは異なるところがあります。
        - SSReflect はもともと数学の定理を証明するために開発されたのに対して、 [LibTactics_J] はプログラミング言語に関する定理を証明するために開発されました。特に、 [LibTactics_J] では SSReflect に対応するもののないような便利なタクティックを多数提供しています。
        - SSReflect がタクティックの表現を根本から考え直したものであるのに対して、 [LibTactics_J] は基本的に Coq の伝統的なタクティックの表現に倣い、タクティックをいくつか追加しただけのものです。このため、 [LibTactics_J] の方が SSReflect よりも取っ付きやすいはずです。
   *)

(* This chapter is a tutorial focusing on the most useful features
    from the "LibTactics" library. It does not aim at presenting all
    the features of "LibTactics". The complete documentation of the
    tactics can be found in the source file [LibTactics.v]. Moreover,
    demos illustrating the working of all the tactics can be found in
    the file [LibTacticsDemos.v]. *)
(**
   本章は [LibTactics_J] ライブラリのうち、最も便利な機能にだけ注目し、 [LibTactics_J] の全機能を紹介することはしていません。 [LibTactics_J] のタクティックの完全な説明は [LibTactics_J.v] のソースファイルを見てください。また、各タクティックの動作の説明については [LibTacticsDemos_J.v] を参照してください。
   *)

(* The tactics are illustrated mostly through examples taken from the
    core chapters of the "Software Foundations" course. To illustrate
    the various ways in which a given tactic can be used, we'll use a
    tactic that duplicates a given goal. More precisely, [dup] produces
    two copies of the current goal, and [dup n] produces [n] copies of it. *)
(**
   タクティックの説明は基本的に Software Foundations 本文から例を取っています。本章では、タクティックの様々な使用法を示すため、現在のゴールを複製するタクティックを使っています。具体的には、 [dup] とすると現在のゴールがふたつに複製され、 [dup n] とすると [n] 個のコピーがゴールになります。
   *)


(* ####################################################### *)
(* * Tactics for introduction and case analysis *)
(** * 導入と場合分けのためのタクティック *)

(* This section presents the following tactics:
    - [introv], for saving time in the naming of hypotheses,
    - [inverts], for improving the [inversion] tactic,
    - [cases], for performing a case analysis without losing information,
    - [cases_if], for automating case analysis on the argument of [if]. *)

(**
   本節では以下のタクティックを説明します。
    - [introv]: 仮定に名前をつける時間を節約する
    - [invert]: [inversion] タクティックの改良版
    - [cases]: 情報を失なわず場合分けをする
    - [cases_if]: [if] の引数の場合分けを自動化する
   *)

(* ####################################################### *)
(* ** The tactic [introv] *)
(** ** [introv] タクティック *)

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

(**
   [introv] タクティックを使うと、定理中の変数を自動的に導入し、関連する仮定に名前をつけることができます。次に示す例では、決定性に言及している部分の変数 [c]、 [st]、 [st1]、 [st2] に自分で名前を付ける必要はありません。これらの変数には補題の中で既に名前が付いているからです。それに対して、ふたつの仮定には [E1]、 [E2] と名前を与えられた方が便利です。
   *)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  introv E1 E2. (* was [intros c st st1 st2 E1 E2] *)
  (* [intros] を使うと [intros c st st1 st2 E1 E2] *)
Admitted.

(* When there is no hypothesis to be named, one can call
    [introv] without any argument. *)
(**
   名前を付けるような仮定がない場合には、引数なしで [introv] を呼ぶことができます。
   *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  introv. (* was [intros c st st'] *)
  (* [intros] を使うと [intros c st st'] *)
Admitted.


(* The tactic [introv] also applies to statements in which
    [forall] and [->] are interleaved. *)
(**
   [introv] は [forall] と [->] が交互に現れるような場合でも使うことができます。
   *)

Theorem ceval_deterministic': forall c st st1,
  (c / st || st1) -> forall st2, (c / st || st2) -> st1 = st2.
Proof.
  introv E1 E2. (* was [intros c st st1 E1 st2 E2] *)
  (* [intros] を使うと [intros c st st1 E1 st2 E2] *)
Admitted.

(* Like the arguments of [intros], the arguments of [introv]
    can be structured patterns. *)
(**
   [intros] と同様、 [introv] の引数にはパターンを指定することができます。
   *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  introv [i E].
  (* was [intros c st st' [i E].], which is itself short
     for [intros c st st' H. destruct H as [i E].] *)
  (* [intros] を使うと [intros c st st' [i E].]。
     これ自体も [intros c st st' H. destruct H as [i E].] の略記。 *)
Admitted.

(* Remark: the tactic [introv] works even when definitions
    need to be unfolded in order to reveal hypotheses. *)
(**
   注: [introv] は仮定が現れるよう定義を展開しなければならない場合にも正しく動作します。
   *)

End IntrovExamples.


(* ####################################################### *)
(* ** The tactic [inverts] *)
(** ** [inverts] タクティック *)

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
(**
   Coq の [inversion] タクティックはそれほど満足のいくものではありません。その理由はみっつあります。ひとつには、 [inversion] を使うと大量の等式が出来ますが、ほとんどは [subst] を使って置き換えてしまいたいようなものばかりだということです。ふたつ目は、仮定に意味のない名前が付くということです。みっつ目は、 [inversion H] しても [H] がコンテキストから取り除かれないことです。ほとんどの場合、 [inversion] したら仮定は必要なくなるのに、です。 [inverts] タクティックはこれらの問題すべてに対応しています。 [inverts] タクティックは [inversion] タクティックの代わりに使うことを意図しています。
   *)

(* The following example illustrates how the tactic [inverts H]
    behaves mostly like [inversion H] except that it performs the
    appropriate substitutions. *)
(**
   以下の例は [inverts H] が [inversion H] とほぼ同じ動作をし、さらに適切な置換を行なっていることを示すものです。
   *)

Theorem skip_left: forall c,
  cequiv (SKIP; c) c.
Proof.
  introv. split; intros H.
  dup. (* duplicate the goal for comparison *)
  (* 比較のためゴールを複製する *)
  (* was: *)
  (* 使用前: *)
  inversion H. subst. inversion H2. subst. assumption.
  (* now: *)
  (* 使用後: *)
  inverts H. inverts H2. assumption.
Admitted.

(* A slightly more interesting example appears next. *)
(** 次はもう少し面白い例です。 *)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1  ->
  c / st || st2 ->
  st1 = st2.
Proof.
  introv E1 E2. generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2.
  admit. admit. (* skip some basic cases *)
  (* 簡単な部分は飛ばす。 *)
  dup. (* duplicate the goal for comparison *)
  (* 比較のためゴールを複製する *)
  (* was: *) (* 使用前: *) inversion E2. subst. admit.
  (* now: *) (* 使用後: *) inverts E2. admit.
Admitted.

(* The tactic [inverts H as.] is like [inverts H] except that the
    variables and hypotheses being produced are placed in the goal
    rather than in the context. This strategy allows naming those
    new variables and hypotheses explicitly, using either [intros]
    or [introv]. *)
(**
   [inverts H as.] は [inverts H] と同じですが、生成された変数と仮定をコンテキストではなくゴールに置きます。こうすることで、 [intros] や [introv] を使って新しい変数や仮定に自分で名前をつけることができます。
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
    (* ここで変数 [n] は自動的に置き換えられない。これは [inversion E2; subst]
       とは異なり、 [invert E2] は実行前から存在した等式は置き換えの対象としないからである。
       *)
    (* new: *) (* 使用後: *) subst n.
    reflexivity.
  Case "E_Seq".
    (* Here, the newly created variables can be introduced
       using intros, so they can be assigned meaningful names,
       for example [st3] instead of [st'0]. *)
    (* ここでは、新たに作られた変数を [intros] を使って導入し、
       [st'0] 等ではなく [st3] という意味のある名前を付けている。
       *)
    (* new: *) (* 使用後: *) intros st3 Red1 Red2.
    assert (st' = st3) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st3.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      (* In an easy case like this one, there is no need to
         provide meaningful names, so we can just use [intros] *)
      (* このような簡単な場合にはわざわざ名前を付ける必要もないので、単に
         [intros] を使う。 *)
      (* new: *) (* 使用後: *) intros.
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      (* new: *) (* 使用後: *) intros.
      rewrite H in H5. inversion H5.
  (* The other cases are similiar *)
  (* 他の場合も同様。 *)
Admitted.

(* In the particular case where a call to [inversion] produces
    a single subgoal, one can use the syntax [inverts H as H1 H2 H3]
    for calling [inverts] and naming the new hypotheses [H1], [H2]
    and [H3]. In other words, the tactic [inverts H as H1 H2 H3] is
    equivalent to [invert H; introv H1 H2 H3]. An example follows. *)
(**
   [inversion] の呼び出し結果がひとつのサブゴールになる場合には特に、 [inverts H as H1 H2 H3] という構文を使うことで、 [inverts] を呼び出して新しい仮定に [H1]、 [H2]、 [H3] という名前を付けることができます。言い換えると、 [inverts H as H1 H2 H3] は [invert H; introv H1 H2 H3] と同等だということです。次に例を示します。
   *)

Theorem skip_left': forall c,
  cequiv (SKIP; c) c.
Proof.
  introv. split; intros H.
  inverts H as U V. (* new hypotheses are named [U] and [V] *)
  (* 新しい仮定の名前を [U]、 [V] とする。 *)
  inverts U. assumption.
Admitted.

(* A more involved example follows. In particular, it shows that
    the name of an inverted hypothesis can be reused. *)
(**
   次はもう少し込み入った例です。 [inverts] した仮定の名前を再利用できることに注目してください。
   *)

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
  (* もとの証明: *)
  intros C. destruct C.
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.

  (* The new proof: *)
  (* 新しい証明: *)
  intros C. destruct C.
  inverts H as H1.
  inverts H1 as H2.
  inverts H2 as H3.
  inverts H3 as H4.
  inverts H4.

  (* The new proof, alternative: *)
  (* もうひとつ、新しい証明: *)
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
(**
   注: 滅多にないことですが、仮定 [H] を [inverts] したときに、その [H] をコンスキストに残したままにしたい場合には、 [inverts keep H] を使うことができます。 [keep] はその仮定をコンテキストに残す（keep）ことを表します。
   *)


(* ####################################################### *)
(* ** The tactics [cases] and [cases_if] *)
(** ** [cases]、 [cases_if] タクティック *)

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
(**
   [cases E] タクティックは [remember E as x; destruct x] の略記法です。相違点は、 [cases] は [remember] の生成する等式と対称なものを生成するということです。例えば、 [cases] は [true = beq_id k1 k2] ではなく、 [beq_id k1 k2 = true] を生成します。前者は読んだ感じがどうにも不格好です。 [cases E as H] とすると生成される等式の名前を指定できます。

   注: [cases] は [case_eq] と非常によく似ています。 [remember] や [case_eq] との互換性のために、 [LibTactics_J] では [cases'] というタクティックを提供しています。 [cases'] は [remember] や [case_eq] とまったく同じ、 [beq_id k1 k2 = true] ではなく [true = beq_id k1 k2] の形式の等式を生成します。以下に [cases' E as H] の動作を示します。
   *)

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.
  dup.

  (* The old proof: *)
  (* もとの証明: *)
  remember (beq_id k1 k2) as b. destruct b.
    apply beq_id_eq in Heqb. subst. reflexivity.
    reflexivity.

  (* The new proof: *)
  (* 新しい証明: *)
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
(**
   [cases_if] タクティックは、ゴールまたはコンテキスト中で [if] の引数として現れる最初の式 [E] に [cases E] を呼び出します。 [cases_if] を使うと既にゴールにある式を copy-past （訳注: copy-paste？）する必要がなくなります。今回もまた互換性の理由で、 [cases_if'] というタクティックが提供されています。 [cases_if' as H] とすると生成された等式の名前を指定することができます。
   *)

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
(** * n 項結合子用のタクティック *)

(* Because Coq encodes conjunctions and disjunctions using binary
    constructors [/\] and [\/], working with a conjunction or a
    disjunction of [N] facts can turn out to be quite cumbursome.
    For this reason, "LibTactics" provides tactics offering direct
    support for n-ary conjunctions and disjunctions. It also provides
    direct support for n-ary existententials. *)
(**
   Coq では連言と選言を二項構成子 [/\] と [\/] で表現しているため、 [n] 個の事実を連言または選言で結合したものを扱おうとするとひどく面倒になることがあります。そのため、 [LibTactics_J] では [n] 項の連言や選言を直接扱えるタクティックを提供しています。それに加えて、 [n] 項の存在量化を扱うタクティックも提供しています。
   *)

(* This section presents the following tactics:
    - [splits] for decomposing n-ary conjunctions,
    - [branch] for decomposing n-ary disjunctions,
    - [exists] for proving n-ary existentials. *)
(**
   本節では以下のタクティックを説明します。
    - [splits]: [n] 項の連言を分解する
    - [branch]: [n] 項の選言を分解する
    - [exists]: [n] 項の存在量化を証明する
   *)

Module NaryExamples.
  Require Import References_J SfLib_J.
  Import STLCRef.


(* ####################################################### *)
(* ** The tactic [splits] *)
(** ** [splits] タクティック *)

(* The tactic [splits] applies to a goal made of a conjunction
    of [n] propositions and it produces [n] subgoals. For example,
    it decomposes the goal [G1 /\ G2 /\ G3] into the three subgoals
    [G1], [G2] and [G3]. *)
(**
   [splits] タクティックを [n] 個の命題の連言から成るゴールに適用すると、 [n] 個のサブゴールが生成されます。例えば、ゴールが [G1 /\ G2 /\ G3] であれば [G1]、 [G2]、 [G3] のみっつのサブゴールに分解されます。
   *)

Lemma demo_splits : forall n m,
  n > 0 /\ n < m /\ m < n+10 /\ m <> 3.
Proof.
  intros. splits.
Admitted.


(* ####################################################### *)
(* ** The tactic [branch] *)
(** ** [branch] タクティック *)

(* The tactic [branch k] can be used to proved a n-ary disjunction.
    For example, if the goal takes the form [G1 \/ G2 \/ G3],
    the tactic [branch 2] leaves only [G2] as subgoal. The following
    example illustrates the behavior of the [branch] tactic. *)
(**
   [branch k] タクティックは [n] 項の選言を証明するのに使うことができます。例えば、ゴールが [G1 \/ G2 \/ G3] の形式のとき、 [branch 2] は [G2] だけをサブゴールとして残します。以下に [branch] タクティックの動作を例示します。
   *)

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
(** ** [exists] タクティック *)

(* The library "LibTactics" introduces a notation for n-ary
    existentials. For example, one can write [exists x y z, H]
    instead of [exists x, exists y, exists z, H]. Similarly,
    the library provides a n-ary tactic [exists a b c], which is a
    shorthand for [exists a; exists b; exists c]. The following
    example illustrates both the notation and the tactic for
    dealing with n-ary existentials. *)
(**
   [LibTactics_J] ライブラリでは [n] 項の存在量化用の記法を導入しています。例えば、 [exists x, exists y, exists z, H] の代わりに [exists x y z, H] と書くことができます。同様に、 [n] 項の [exists a b c] タクテイックも提供しています。こちらは、 [exists a; exists b; exists c] の略です。以下に [n] 項の存在量化を扱う記法とタクティックの両方の使用例を示します。
   *)

Theorem progress : forall ST t T st,
  has_type empty ST t T ->
  store_well_typed ST st ->
  value t \/ exists t' st', t / st ==> t' / st'.
  (* was: [value t \/ exists t', exists st', t / st ==> t' / st'] *)
  (* もとは [value t \/ exists t', exists st', t / st ==> t' / st'] *)
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
        (* もとは [exists (tm_app (tm_abs x T t) t2'). exists st'...] *)
Admitted.

(* Remark: a similar facility for n-ary existentials is provided
    by the module [Coq.Program.Syntax] from the standard library,
    except that this facility only works up to arity 4, whereas
    [LibTactics] supports arities up to 10. *)
(** 注: [n] 項の存在量化を扱う同様の仕組みは標準ライブラリの [Coq.Program.Syntax] モジュールでも提供されています。ただし、標準ライブラリの方が 4 引数までのものにしか対応していないのに対して [LibTactics_J] では 10 引数まで対応しています。
   *)

End NaryExamples.


(* ####################################################### *)
(* * Tactics for working with equality *)
(** * 等価性を扱うタクティック *)

(* One of the major weakness of Coq compared with other interactive
    proof assistants is its relatively poor support for reasoning
    with equalities. The tactics described next aims at simplifying
    pieces of proof scripts manipulating equalities. *)
(**
   Coq を他の定理証明支援器と比べた場合の大きな弱点のひとつは、等価性を使った推論の扱いが弱いことです。次に説明するタクティックは、等価性を扱う証明スクリプトを単純化することを目指したものです。
   *)

(* This section presents the following tactics:
    - [asserts_rewrite] for introducing an equality to rewrite with,
    - [cuts_rewrite], which is similar except subgoals are swapped,
    - [substs] for improving the [subst] tactic,
    - [fequals] for improving the [f_equal] tactic,
    - [applys_eq] for proving [P x y] using an hypothesis [P x z],
      automatically generating the equality [y = z]. *)
(** 本節では以下のタクティックを説明します。
    - [asserts_rewrite]: 書き換えに等価性を導入する
    - [cuts_rewrite]: [asserts_rewrite] と同じだが、サブゴールを取り替える
    - [substs]: [subst] タクティックの改良版
    - [fequals]: [f_equal] タクティックの改良版
    - [applys_eq]: 仮定 [P x z] を使って [P x y] を証明すると、自動的に [y = z] という等価性を生成する
   *)

Module EqualityExamples.


(* ####################################################### *)
(* ** The tactics [asserts_rewrite] and [cuts_rewrite] *)
(** ** [asserts_rewrite]、 [cuts_rewrite] タクティック *)

(* The tactic [asserts_rewrite (E1 = E2)] replaces [E1] with [E2] in
    the goal, and produces the goal [E1 = E2]. *)
(** [asserts_rewrite (E1 = E2)] タクティックは、ゴール中の [E1] を [E2] で置き換え、 [E1 = E2] というゴールを生成します。
   *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.
  (* The old proof: *)
  (* もとの証明: *)
  intros n m.
  assert (H: 0 + n = n). reflexivity. rewrite -> H.
  reflexivity.

  (* The new proof: *)
  (* 新しい証明: *)
  intros n m.
  asserts_rewrite (0 + n = n).
    reflexivity. (* subgoal [0+n = n] *)
    reflexivity. (* subgoal [n*m = m*n] *)
Qed.

(* Remark: the syntax [asserts_rewrite (E1 = E2) in H] allows
     rewriting in the hypothesis [H] rather than in the goal. *)
(** 注: [asserts_rewrite (E1 = E2) in H] とするとゴールではなく仮定 [H] を書き換えることができます。
   *)

(* The tactic [cuts_rewrite (E1 = E2)] is like
    [asserts_rewrite (E1 = E2)], except that the equality [E1 = E2]
    appears as first subgoal. *)
(** [cuts_rewrite (E1 = E2)] は [asserts_rewrite (E1 = E2)] と似ていますが、 [E1 = E2] が最初のサブゴールになります。
   *)

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
(**
   より一般的には、 [asserts_rewrite] と [cuts_rewrite] の引数には補題を引数として与えることができます。例えば、 [asserts_rewrite (forall a b, a * (S b) = a * b + a)] のように書くことができます。この表記法は [a] や [b] が大きな項のときに便利です（[a] や [b] を繰り返さなくて済みます）。
   *)

Theorem mult_0_plus'' : forall u v w x y z: nat,
  (u + v) * (S (w * x + y)) = z.
Proof.
  intros. asserts_rewrite (forall a b, a*(S b) = a*b+a).
    (* first subgoal:  [forall a b, a*(S b) = a*b+a] *)
    (* 第一のサブゴール:  [forall a b, a*(S b) = a*b+a] *)
    (* second subgoal: [(u + v) * (w * x + y) + (u + v) = z] *)
    (* 第二のサブゴール: [(u + v) * (w * x + y) + (u + v) = z] *)
Admitted.


(* ####################################################### *)
(* ** The tactic [substs] *)
(** ** [substs] タクティック *)

(* The tactic [substs] is similar to [subst] except that it
    does not fail when the goal contains "circular equalities",
    such as [x = f x]. *)
(** [substs] は [subst] と似ていますが、ゴールに [x = f x] のような「循環した等式」があると失敗します。
   *)

Lemma demo_substs : forall x y (f:nat->nat),
  x = f x -> y = x -> y = f x.
Proof.
  intros. substs. (* [subst] would fail here *)
  assumption.
Qed.


(* ####################################################### *)
(* ** The tactic [fequals] *)
(** ** [fequals] タクティック *)

(* The tactic [fequals] is similar to [f_equal] except that it
    directly discharges all the trivial subgoals produced. Moreover,
    the tactic [fequals] features an enhanced treatment of equalities
    between tuples. *)
(** [fequals] は [f_equal] と似ていますが、生成されたサブゴールのうち、自明なものは直接片付けてしまいます。さらに、 [fequals] はタプル同士の等価性の扱いが改良されています。
   *)

Lemma demo_fequals : forall (a b c d e : nat) (f : nat->nat->nat->nat->nat),
  a = 1 -> b = e -> e = 2 ->
  f a b c d = f 1 2 c 4.
Proof.
  intros. fequals.
  (* subgoals [a = 1], [b = 2] and [c = c] are proved, [d = 4] remains *)
  (* サブゴールのうち [a = 1]、 [b = 2]、 [c = c] は証明されて、 [d = 4] が残る。 *)
Admitted.


(* ####################################################### *)
(** ** The tactic [applys_eq] *)

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
(**
   [applys_eq] は [eapply] の変種で、単一化できなかった下位項に関する等式を導入します。例えば、ゴールが命題 [P x y] で、前提として [P x z] なる [H] が成り立っているとします。 [y] が [z] に等しいことが証明できるのはわかっています。ですから、 [asserts_rewrite (y = z)] としてゴールを [y = z] に変えることができます。しかし、こうすると [y] や [z] の値をコピペすることになるでしょう。 [applys_eq] タクティックを使い [applys_eq H 1] とすれば、現在のゴールを証明してサブゴールとして [y = z] だけを残すことができます。引数に与えた [1] は [P x y] の引数のうち、右から数えて一番目のものに関する等価性を導入することを表しています。下のみっつの例では、 [applys_eq H 1]、 [applys_eq H 2]、 [applys_eq H 1 2] を呼び出した場合の動作を説明します。
   *)

Axiom big_expression_using : nat->nat. (* Used in the example *)

Lemma demo_applys_eq_1 : forall (P:nat->nat->Prop) x y z,
  P x (big_expression_using z) ->
  P x (big_expression_using y).
Proof.
  introv H. dup.

  (* The old proof: *)
  (* もとの証明: *)
  assert (Eq: big_expression_using y = big_expression_using z).
    admit. (* Assume we can prove this equality somehow. *)
    (* どうにかしてこの等式を証明できたとする *)
  rewrite Eq. apply H.

  (* The new proof: *)
  (* 新しい証明: *)
  applys_eq H 1.
    admit. (* Assume we can prove this equality somehow. *)
    (* どうにかしてこの等式を証明できたとする *)
Qed.

(* If the mismatch was on the first argument of [P] instead of
    the second, we would have written [applys_eq H 2]. Recall
    that the occurences are counted from the right. *)
(** [P] の第二引数ではなく第一引数が異なっている場合には [applys_eq H 2] とします。位置は右から数えることに注意してください。
   *)

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
(**
   引数両方が異なっている場合には、等式をふたつ生成したいところです。この場合は [applys_eq H 1 2] と書きます。より一般的には [applys_eq] は引数としてひとつの補題と複数の自然数を受け付けます。
   *)

Lemma demo_applys_eq_3 : forall (P:nat->nat->Prop) x1 x2 y1 y2,
  P (big_expression_using x2) (big_expression_using y2) ->
  P (big_expression_using x1) (big_expression_using y1).
Proof.
  introv H. applys_eq H 1 2.
  (* produces two subgoals:
     [big_expression_using x1 = big_expression_using x2]
     [big_expression_using y1 = big_expression_using y2] *)
  (* 以下のふたつのサブゴールが生成される。
     [big_expression_using x1 = big_expression_using x2]
     [big_expression_using y1 = big_expression_using y2] *)
Admitted.

End EqualityExamples.


(* ####################################################### *)
(* * Some convenient shorthands *)
(** * 便利な省略タクティック *)

(* This section of the tutorial introduces a few tactics
    that help make proof scripts shorter and more readable:
    - [unfolds] (without argument) for unfolding the head definition,
    - [false] for replacing the goal with [False],
    - [gen] as a shorthand for [dependent generalize],
    - [skip] for skipping a subgoal (works with existential variables),
    - [sort] for moving propositions at the bottom of the proof context. *)
(**
   本節では証明スクリプトを短かく読みやすくするためのタクティックを紹介します。
   - [unfolds]: （引数なし）先頭の定義を展開する
   - [false]: ゴールを [False] と置き換える
   - [gen]: [dependent generalize] の略
   - [skip]: サブゴールをスキップする（存在量化された変数があっても可）
   - [sort]: コンテキストの下の方にある命題を移動させる
   *)


(* ####################################################### *)
(* ** The tactic [unfolds] *)
(** ** [unfolds] タクティック *)

Module UnfoldsExample.
  Require Import Hoare_J.

(* The tactic [unfolds] (without any argument) unfolds the
    head constant of the goal. This tactic saves the need to
    name the constant explicitly. *)
(** [unfold] タクティック（引数は取りません）はゴールの先頭にある定数を展開します。このタクティックを使うと定数に名前を与える必要がなくなります。
   *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe. dup.

  (* The old proof: *)
  (* もとの証明: *)
  unfold bassn. assumption.

  (* The new proof: *)
  (* 新しい証明: *)
  unfolds. assumption.
Qed.

(* Remark: contrary to the tactic [hnf], which unfolds all the
    head constants, [unfolds] performs only a single unfolding. *)
(**
   注: 先頭の定数をすべて展開する [hnf] タクティックとは違い、 [unfolds] は最初のものだけを展開します。
   *)

(* Remark: the tactic [unfolds in H] can be used to unfold the
    head definition of the hypothesis [H]. *)
(**
   注: [unfolds in H] とすると仮定 [H] 中の先頭の定義を展開することができます。
   *)

End UnfoldsExample.


(* ####################################################### *)
(* ** The tactics [false] and [tryfalse] *)
(** ** [false]、 [tryfalse] タクティック *)

(* The tactic [false] can be used to replace any goal with [False].
    In short, it is a shorthand for [apply ex_falso_quodlibet].
    Moreover, [false] proves the goal if it contains an absurd
    assumption, such as [False] or [0 = S n], or if it contains
    contradictory assumptions, such as [x = true] and [x = false]. *)
(**
   [false] タクティックを使うと任意のゴールを [False] に置き換えることができます。つまり、このタクティックは [apply ex_falso_quodlibet] の略なのです。さらに、 [false] を使うと、 [False] や [0 = S n] のような不合理な前提や、 [x = true] かつ [x = false] のような矛盾した仮定がある場合にゴールを証明することができます。
   *)

Lemma demo_false :
  forall n, S n = 1 -> n = 0.
Proof.
  intros. destruct n. reflexivity. false.
Qed.

(* The tactic [tryfalse] is a shorthand for [try solve [false]]:
    it tries to find a contradiction in the goal. The tactic
    [tryfalse] is generally called after a case analysis. *)
(**
   [tryfalse] タクティックは [try solve [false]] の略で、ゴールに矛盾がないか探します。一般に [tryfalse] は場合分けの後に使います。
   *)

Lemma demo_tryfalse :
  forall n, S n = 1 -> n = 0.
Proof.
  intros. destruct n; tryfalse. reflexivity.
Qed.


(* ####################################################### *)
(* ** The tactic [gen] *)
(** ** [gen] タクティック *)

(* The tactic [gen] is a shortand for [generalize dependent]
    that accepts several arguments at once. An invokation of
    this tactic takes the form [gen x y z]. *)
(**
   [gen] タクティックは [generalize dependent] の略で、一度に複数の引数を取ることができます。呼び出しは [gen x y z] のような形になります。
   *)

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
  (* もとの証明: *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.

  (* The new proof: *)
  (* 新しい証明: *)
  introv Htypt Htypv. gen S Gamma.
  induction t; intros; simpl.
  admit. admit. admit. admit. admit. admit.
Qed.

End GenExample.


(* ####################################################### *)
(* ** The tactics [skip], [skip_rewrite] and [skip_goal] *)
(** ** [skip]、 [skip_rewrite]、 [skip_goal] タクティック *)

(* The ability to admit a given subgoal is very useful when
    constructing proofs. It gives the ability to focus first
    on the most interesting cases of a proof. The tactic [skip]
    is like [admit] except that it also works when the proof
    includes existential variables. Recall that existential
    variables are those whose name starts with a question mark,
    e.g. [?24], and which are typically introduced by [eapply]. *)
(**
   証明を組み立てているときには、与えられたサブゴールを [admit] できると非常に便利です。こうすることで、最初に証明のもっとも面白い部分に集中することができます。 [skip] タクティックは [admit] とほぼ同じですが、証明に存在量化された変数が入っている場合でも使うことができます。存在量化された変数というのは、 [?24] のような、名前が疑問符から始まるような変数で、一般には [eapply] 等で導入されます。
   *)

Module SkipExample.
  Require Import Stlc_J.
  Import STLC.

Example astep_example1 :
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state ==>a* (ANum 15).
Proof.
  eapply rsc_step. skip. (* [admit] would not work here *)
  (* これは [admit] できない *)
  eapply rsc_step. skip. skip.
  (* Note that because some unification variables have
     not been instantiated, we still need to write
     [Admitted] instead of [Qed] at the end of the proof. *)
  (* 単一化変数に具体化されていないものがあるので、証明の最後は [Qed] ではなく [Admitted] にする必要がある。
     *)
Admitted.

(* The tactic [skip H: P] adds the hypothesis [H: P] to the context,
    without checking whether the proposition [P] is true.
    It is useful for exploiting a fact and postponing its proof.
    Note: [skip H: P] is simply a shorthand for [assert (H:P). skip.] *)
(**
   [skip H: P] タクティックは、命題 [P] が真であるか確認することなしにコンテキストに [H: P] を追加します。これは、とりあえず事実を使っておき、その証明は後回しにするときに便利です。 注: [skip H: P] は単純に [assert (H:P). skip.] の略です。
   *)

Theorem demo_skipH : True.
Proof.
  skip H: (forall n m : nat, (0 + n) * m = n * m).
Admitted.

(* The tactic [skip_rewrite (E1 = E2)] replaces [E1] with [E2] in
    the goal, without checking that [E1] is actually equal to [E2]. *)
(**
   [skip_rewrite (E1 = E2)] タクティックはゴール中の [E1] を [E2] で置き換えます。このとき、 [E1] が実際に [E2] と等しいかは確認しません。
   *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  dup.

  (* The old proof: *)
  (* もとの証明: *)
  intros n m.
  assert (H: 0 + n = n). skip. rewrite -> H.
  reflexivity.

  (* The new proof: *)
  (* 新しい証明: *)
  intros n m.
  skip_rewrite (0 + n = n).
  reflexivity.
Qed.

(* Remark: the tactic [skip_rewrite] can in fact be given a lemma
    statement as argument, in the same way as [asserts_rewrite]. *)
(**
   注: [skip_rewrite] タクティックには [asserts_rewrite] と同じ形式で、引数に補題を渡すことができます。
   *)

(* The tactic [skip_goal] adds the current goal as hypothesis.
    This cheat is useful to set up the structure of a proof by
    induction without having to worry about the induction hypothesis
    being applied only to smaller arguments. Using [skip_goal], one
    can construct a proof in two steps: first, check that the main
    arguments go through without waisting time on fixing the details
    of the induction hypotheses, and then focus on fixing the
    invokations of the induction hypothesis. *)
(* @TYPO: invokations -> invocations *)
(**
   [skip_goal] タクティックは現在のゴールを仮定に追加します。こういったずるをしておくと、帰納的証明を構成するときに、帰納法の仮定がより小さい引数にしか適用できないことに悩まされなくて済みます。 [skip_goal] タクティックを使うと、証明を二段階で構成することができます。まず最初に帰納法の仮定の細部にかかずらうことなく本題が証明できるか確認し、それから帰納法の仮定をどこで使うかに集中します。
   *)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  (* [skip_goal] creates an hypothesis called [IH] asserting
     that the statment of [ceval_deterministic] is true. *)
  (* [skip_goal] すると [ceval_deterministic] が真であるという主張を仮定 [IH] として作成する。
     *)
  skip_goal.
  (* Of course, if we call [assumption] here, then the goal is solved
     right away, but the point is to do the proof and use [IH]
     only at the places where we need an induction hypothesis. *)
  (* もちろん、ここで [assumption] を呼べば証明は直ちに終了するが、
     ここでのポイントは帰納法の仮定の必要なところでだけ [IH] を使い証明をすることである。
     *)
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
        (* もとは [apply IHE1_1; assumption.] *)
        (* new: *) eapply IH. eapply E1_1. eapply Red1.
    subst st3.
    (* was: apply IHE1_2. assumption.] *)
    (* もとは apply IHE1_2. assumption.] *)
    (* new: *) eapply IH. eapply E1_2. eapply Red2.
  (* The other cases are similiar. *)
  (* 他の場合も同様。 *)
Admitted.

End SkipExample.


(* ####################################################### *)
(* ** The tactic [sort] *)
(** ** [sort] タクティック *)

Module SortExamples.
  Require Import Imp_J.

(* The tactic [sort] reorganizes the proof context by placing
    all the variables at the top and all the hypotheses at the
    bottom, thereby making the proof context more readable. *)
(**
   [sort] タクティックは、コンテキストを再構成し、変数が上に、仮定が下に来るようにます。これによりコンテキストが読みやすくなります。
   *)

Theorem ceval_deterministic: forall c st st1 st2,
  c / st || st1 ->
  c / st || st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  (ceval_cases (induction E1) Case); intros st2 E2; inverts E2.
  admit. admit. (* Skipping some trivial cases *)
  (* 自明な場合を飛ばす *)
  sort. (* Observe how the context is reorganized *)
  (* コンテキストがどのように再構成されるか確認 *)
Admitted.

End SortExamples.


(* ####################################################### *)
(* * Tactics for advanced lemma instantiation *)
(** * 高度な補題具体化タクティック*)

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
(**
   本節で紹介するのは、補題を具体化する際、引数のうちいくつかを手で与え、残りを暗黙に与えるようにする仕組みです。具体化されなかった変数は存在量化された変数になり、具体化されなかった事実はサブゴールになります。

   注: この仕組みは「暗黙の引数」よりもさらに強力なものです。本節で説明する具体化機能を使えば、補題を具体化するときにアンダースコアをいくつ書けばいいのかもう悩まなくて済みます。
   *)

(* In this section, we'll use a useful feature of Coq for decomposing
    conjunctions and existentials. In short, a tactic like [intros] or
    [destruct] can be provided with a pattern [(H1 & H2 & H3 & H4 & H5)],
    which is a shorthand for [[H1 [H2 [H3 [H4 H5]]]]]]. For example,
    [destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].]
    can be rewritten in the form
    [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).] *)
(**
   本節では、連言や存在量化を分解するための Coq の機能を使っています。この機能を使うと、 [intros] や [destruct] に与える [[H1 [H2 [H3 [H4 H5]]]]]] のようなパターンは [(H1 & H2 & H3 & H4 & H5)] と書くことができます。例えば、
    [destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].]
    を
    [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).]
    と書けます。
   *)


(* ####################################################### *)
(* ** Working of [lets] *)
(** ** [lets] の動作 *)

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
(**
   証明中で利用したい補題（や前提）があるとき、
   [destruct (typing_inversion_var _ _ _ Htypt) as (T & Hctx & Hsub).]
   のようにして、引数を陽に与えてやらないとならないことがしばしばあります。このとき、何度も何度もアンダースコアを書かなくてはならないのは冗長です。アンダースコアを何回書かなければならないか調べなければなりませんし、証明スクリプトもひどく不格好になります。 [lets] タクティックを使えば、簡単に
   [lets (T & Hctx & Hsub): typing_inversion_var Htypt.]
   と書けます。

   [lets] タクティックを使うと、一連の変数や仮定に対して補題を特殊化することができます。 [E0] という事実に [E1] から [EN] の引数を与えて [I] という仮定を構成するには [lets I: E0 E1 .. EN] と書きます。引数をすべて与える必要はありませんが、与える引数の順番は正しくなければなりません。このタクティックは、型にもとづく first match アルゴリズムで、与えられた引数で補題をどのように具体化するか決定します。
   *)
(* TODO: 訳語 first match *)

Module ExamplesLets.
  Require Import Subtyping_J.

(* To illustrate the working of [lets], assume that we want to
   exploit the following lemma. *)
(** [lets] の動作を説明するため、ここでは以下の補題を使うことにします。
   *)

Axiom typing_inversion_var : forall (G:context) (x:id) (T:ty),
  has_type G (tm_var x) T ->
  exists S, G x = Some S /\ subtype S T.

(* First, assume we have an assumption [H] with the type of the form
    [has_type G (tm_var x) T]. We can obtain the conclusion of the
    lemma [typing_inversion_var] by invoking the tactics
    [lets K: typing_inversion_var H], as shown next. *)
(** まず、 [has_type G (tm_var x) T] 型の補題 [H] があるとします。次に示す通り、 [typing_inversion_var] 補題の結果は [lets K: typing_inversion_var H] で得ることができます。
   *)

Lemma demo_lets_1 : forall (G:context) (x:id) (T:ty),
  has_type G (tm_var x) T -> True.
Proof.
  intros G x T H. dup.

  (* step-by-step: *)
  (* 段階を踏んで: *)
  lets K: typing_inversion_var H.
  destruct K as (S & Eq & Sub).
  admit.

  (* all-at-once: *)
  (* 一気に: *)
  lets (S & Eq & Sub): typing_inversion_var H.
  admit.

Qed.

(* Assume now that we know the values of [G], [x] and [T] and we
    want to obtain [S], and have [has_type G (tm_var x) T] be produced
    as a subgoal. To indicate that we want all the remaining arguments
    of [typing_inversion_var] to be produced as subgoals, we use a
    triple-underscore symbol [___]. (We'll later introduce a shorthand
    tactic called [forwards] to avoid writing triple underscores.) *)
(**
   [G]、 [x]、 [T] の値はわかっていて、 [S] を得て [has_type G (tm_var x) T] をサブゴールに加えたいとします。 [typing_inversion_var] の残りの引数をサブゴールにすることを示すために、三重のアンダースコア [___] を使います。（後で [___] を書かなくて済む [forwards]  タクティックを紹介します。）
   *)

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
(**
   普通は、 [has_type G (tm_var x) T] を証明するのに使う [G] や [T] はコンテキストにはひとつしかありませんから、実際には [G] や [T] を与えてやる必要はないはずです。その場合には [lets (S & Eq & Sub): typing_inversion_var x] とすれば十分です。そうすると [G] や [T] は存在量化された変数として具体化されます。
   *)

Lemma demo_lets_3 : forall (x:id), True.
Proof.
  intros x.
  lets (S & Eq & Sub): typing_inversion_var x ___.
Admitted.

(* We could be even more extreme and not give any argument to
    instantiate [typing_inversion_var]. In this case, three unification
    variables are introduced. *)
(**
   より進めて、 [typing_inversion_var] を具体化するのにまったく引数を与えないこともできます。この場合、単一化変数がみっつ導入されます。
   *)

Lemma demo_lets_4 : True.
Proof.
  lets (S & Eq & Sub): typing_inversion_var ___.
Admitted.

(* Note: if we provide [lets] with only the name of the lemma as
    argument, it simply adds this lemma in the proof context, without
    trying to instantiate any of its arguments. *)
(**
   注: [lets] の引数に補題の名前だけ与えた場合には、引数を具体化せずに、単にその補題をコンテキストに追加します。
   *)

Lemma demo_lets_5 : True.
Proof.
  lets H: typing_inversion_var.
Admitted.

(* A last useful feature of [lets] is the double-underscore symbol,
    which allows skipping an argument when several arguments have
    the same type. In the following example, we want [m] to be
    instantiated as the value [3], but we want [n] to be instantiated
    using an existential variable. *)
(**
   最後に説明する [lets] の機能は二重アンダースコアです。これを使うと、複数の引数の型が同じときに、引数を飛ばすことができます。下の例では、 [m] を [3] に具体化し、 [n] は存在量化された変数を使って具体化します。
   *)

Lemma demo_lets_underscore :
  (forall n m, n <= m -> n < m+1) -> True.
Proof.
  intros H.

  (* If we do not use a double underscore, the first argument,
     which is [n], gets instantiated as 3. *)
  (* 二重アンダースコアを使わないと、最初の引数の [n] が [3] に具体化される。
     *)
  lets K: H 3. (* gives [K] of type [forall m, 3 <= m -> 3 < m+1] *)
  (* [K] は [forall m, 3 <= m -> 3 < m + 1] 型になる  *)
    clear K.

  (* The double underscore preceeding [3] indicates that we want
     to skip a value that has the type [nat] (because [3] has
     the type [nat]). So, the variable [m] gets instiated as [3]. *)
  (* [3] の前の二重アンダースコアは [nat] 型の引数をひとつ飛ばすことを意味する（[3] が [nat] 型なので）。そのため、 [m] が [3] に具体化される。
     *)
  lets K: H __ 3. (* gives [K] of type [?X <= 3 -> ?X < 3+1] *)
  (* [K] は [?X <= 3 -> ?X < 3 + 1] 型になる *)
    clear K.
Admitted.


(* Note: one can write [lets: E0 E1 E2] in place of [lets H: E0 E1 E2]
    when the name [H] needs not be mentioned in the proof script.

    Note: the tactics [lets] accepts up to five arguments. Another
    syntax if available for providing more than five arguments.
    It consists in using a list introduced with the keyword [>>],
    for example [lets H: (>> E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 10)]. *)
(* ???: Another syntax *is* か *)
(**
   証明スクリプト内で [H] という名前を参照する必要がないのであれば [lets H: E0 E1 E1] の代わりに [lets: E0 E1 E1] と書くこともできます。

   注: [lets] には引数をいつつまでしか与えることができません。引数をむっつ以上与えるには、 [>>] で引数リストを書く別の構文を使い、例えば、
   [lets H: (>> E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 10)]
   のように書きます。
   *)

End ExamplesLets.


(* ####################################################### *)
(* ** Working of [applys], [forwards] and [specializes] *)
(** ** [applys]、 [forwards]、 [specializes] の動作 *)

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
(* ???: 以下原文は -- で各タクティックの説明を始めるが、箇条書きのつもりか。私意により改める。 *)
(**
   [applys]、 [forwards]、 [specializes] は特定の操作をするときに [lets] の代わりに使える略記法です。

   - [forwards] は補題の引数をすべて具体化するための略記法です。 [forwards H: E0 E1 E2 E3] は [lets H: E0 E1 E2 E3 ___] と同じです。この三重アンダースコアの意味は先ほど説明した通りです。

   - [applys] を使うと [lets] を使って補題を構成し、その補題を即座に適用することができます。 [applys E0 E1 E2 E3] は [lets H: E0 E1 E2 E3] して [eapply H] し、それから [clear H] するのと同じです。

   - [specializes] はコンテキスト中の前提をその場で指定の引数で具体化するための略記法です。 [specializes H E0 E1] は [lets H': H E0 E1] して [clear H] して [rename H' into H] するのと同じです。

   以下に [applys] の使用例を示します。 [specializes]、 [forwards] の使用例は [UseAuto_J.v] にいくつかあります。
   *)


(* ####################################################### *)
(* ** Example of instantiations *)
(** ** 具体化の例 *)

Module ExamplesInstantiations.
  Require Import Subtyping_J.

(* In the following proof, [lets] is used instead of [destruct]
    and [applys] is used instead of [apply] in several places.
    Those places indicated by a comment starting with "old:".
    The exercise consists in also using [lets] where indicated. *)
(**
   以下の証明では数カ所で [destruct] の代わりに [lets] を使い、 [apply] の代わりに [applys] を使っています。そのような部分は「旧: 」で始まるコメントで示してあります。他にも [lets] を使える場所を、練習問題としてコメントで示してあります。
   *)

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
    (* [destruct] を [lets] で置き換えられる例 *)
    (* old: destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].*)
    (* 旧: destruct (typing_inversion_var _ _ _ Htypt) as [T [Hctx Hsub]].*)
    (* 新: *)
    (* new: *) lets (T&Hctx&Hsub): typing_inversion_var Htypt.
    unfold extend in Hctx.
    remember (beq_id x y) as e. destruct e... (* [cases_if'] could be used here *)
    (* ここでは [cases_if'] を使うこともできる *)
    SCase "x=y".
      apply beq_id_eq in Heqe. subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      intros x Hcontra.

       (* A more involved example where [destruct] is replaced with [lets] *)
       (* [destruct] を [lets] で置き換える、もう少し込み入った例 *)
       (* old: destruct (free_in_context _ _ S empty Hcontra) as [T' HT']... *)
       (* 旧: destruct (free_in_context _ _ S empty Hcontra) as [T' HT']... *)
       (* 新: *)
       (* new: *)
        lets [T' HT']: free_in_context S empty Hcontra...
        inversion HT'.
  Case "tm_app".

    (* Exercise: replace the following [destruct] with a [lets] *)
    (* 練習問題: 下の [destruct] を [lets] で置き換えなさい *)
    (* old: destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
            eapply T_App... *)
    (* 旧: destruct (typing_inversion_app _ _ _ _ Htypt) as [T1 [Htypt1 Htypt2]].
            eapply T_App... *)
    (* FILL IN HERE *) admit.

  Case "tm_abs".
    rename i into y. rename t into T1.

    (* Here is another example of using [lets] *)
    (* 別の [lets] の使用例 *)
    (* old: destruct (typing_inversion_abs _ _ _ _ _ Htypt). *)
    (* 旧: destruct (typing_inversion_abs _ _ _ _ _ Htypt). *)
    (* 新: *)
    (* new: *) lets (T2&Hsub&Htypt2): typing_inversion_abs Htypt.

    (* An example of where [apply with] can be replaced with [applys] *)
    (* [apply with] を [applys] で置き換えられる例 *)
    (* old: apply T_Sub with (ty_arrow T1 T2)... *)
    (* 旧: apply T_Sub with (ty_arrow T1 T2)... *)
    (* 新: *)
    (* new: *) applys T_Sub (ty_arrow T1 T2)...
     apply T_Abs...
    remember (beq_id x y) as e. destruct e. (* [cases_if'] could be used here *)
    (* ここでは [cases_if'] を使うこともできる *)
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
    (* [assert] を [lets] で置き換えられる例 *)
    (* old: assert (subtype ty_Unit S) by apply (typing_inversion_unit _ _ Htypt)... *)
    (* 旧: assert (subtype ty_Unit S) by apply (typing_inversion_unit _ _ Htypt)... *)
    (* 新: *)
    (* new: *) lets: typing_inversion_unit Htypt...


Qed.

End ExamplesInstantiations.


