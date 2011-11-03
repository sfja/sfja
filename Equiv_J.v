(** * Equiv_J: プログラムの同値性 *)
(* * Equiv: Program Equivalence *)

(* $Date: 2011-04-05 21:37:47 -0400 (Tue, 05 Apr 2011) $ *)


Require Export Imp_J.

(* *** Some general advice for homework assignments

    - We've tried to make sure that most of the Coq proofs we ask you
      to do are similar to proofs that we've provided.  Before
      starting to work on the homework problems, take the time to work
      through our proofs (both informally, on paper, and in Coq) and
      make sure you understand them in detail.  This will save you a
      lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them simply by
      "following your nose" or random hacking.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.

    - Use automation to save work!  Some of the proofs in this
      chapter's exercises are pretty long if you try to write out all
      the cases explicitly. *)
(** *** 宿題割当てについての一般的アドバイス

    - Coqによる証明問題は、そこまでに文中で行ってきた証明となるべく同じようにできるようにしています。
      宿題に取り組む前に、そこまでの証明を自分でも(紙上とCoqの両方で)やってみなさい。
      そして、細部まで理解していることを確認しなさい。
      そうすることは、多くの時間を節約することになるでしょう。

    - 問題にする Coq の証明はそれなりに複雑なため、
      単に怪しそうなところをランダムに探ってみるような方法で解くことはまず無理です。
      なぜその性質が真で、どう進めば証明になるかを最初に考える必要があります。
      そのための一番良い方法は、形式的な証明を始める前に、
      紙の上に非形式的な証明をスケッチでも良いので書いてみることです。
      そうすることで、定理が成立することを直観的に確信できます。

    - 仕事を減らすために自動化を使いなさい。この章の練習問題の証明のいくつかは、
      もしすべての場合を明示的に書き出すとすると、とても長くなります。*)

(* ####################################################### *)
(* * Behavioral Equivalence *)
(** * 振る舞い同値性 *)

(* In the last chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    it was very easy to define what it _means_ for a program
    transformation to be correct: it should always yield a program
    that evaluates to the same number as the original.

    To talk about the correctness of program transformations in the
    full Imp language, we need to think about the role of variables
    and the state. *)
(** 前の章で、簡単なプログラム変換の正しさを調べました。
    [optimize_0plus]関数です。
    対象としたプログラミング言語は、算術式の言語の最初のバージョンでした。
    それには変数もなく、そのためプログラム変換が正しいとはどういうことを意味する(_means_)
    かを定義することはとても簡単でした。
    つまり、変換の結果得られるプログラムが常に、
    それを評価すると元のプログラムと同じ数値になるということでした。

    Imp言語全体についてプログラム変換の正しさを語るためには、
    変数の役割、および状態について考えなければなりません。*)

(* ####################################################### *)
(* ** Definitions *)
(** ** 定義 *)

(* For [aexp]s and [bexp]s, the definition we want is clear.  We say
    that two [aexp]s or [bexp]s are _behaviorally equivalent_ if they
    evaluate to the same result _in every state_. *)
(** [aexp]と[bexp]については、どう定義すれば良いかは明らかです。
    2つの[aexp]または[bexp]が振る舞い同値である(_behaviorally equivalent_)とは、
    「すべての状態で」2つの評価結果が同じになることです。*)    

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

(* For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are run in the
    same initial state," because some commands (in some starting
    states) don't terminate in any final state at all!  What we need
    instead is this: two commands are behaviorally equivalent if, for
    any given starting state, they either both diverge or both
    terminate in the same final state.  A compact way to express this
    is "if the first one terminates in a particular state then so does
    the second, and vice versa." *)
(** コマンドについては、状況はもうちょっと微妙です。
    簡単に「2つのコマンドが振る舞い同値であるとは、
    両者を同じ状態から開始すれば同じ状態で終わることである」と言うわけには行きません。
    コマンドによっては(特定の状態から開始したときには)
    停止しないためどのような状態にもならないことがあるからです!
    すると次のように言う必要があります。
    2つのコマンドが振る舞い同値であるとは、任意の与えられた状態から両者をスタートすると、
    両者ともに発散するか、両者ともに停止して同じ状態になることです。
    これを簡潔に表現すると、「1つ目が停止して特定の状態になるならば2つ目も同じになり、
    逆もまた成り立つ」となります。*)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st':state),
    (c1 / st || st') <-> (c2 / st || st').

(* **** Exercise: 2 stars, optional (pairs_equiv) *)
(** **** 練習問題: ★★, optional (pairs_equiv) *)
(* Which of the following pairs of programs are equivalent? Write
    "yes" or "no" for each one.

(a)
[[
    WHILE (BLe (ANum 1) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END
]]
    and
[[
    WHILE (BLe (ANum 2) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END
]]
(* FILL IN HERE *)

(b)
[[
    WHILE BTrue DO
      WHILE BFalse DO X ::= APlus (AId X) (ANum 1) END
    END
]]
and
[[
    WHILE BFalse DO
      WHILE BTrue DO X ::= APlus (AId X) (ANum 1) END
    END
]]

(* FILL IN HERE *)

[] *)
(** 以下のプログラムの対の中で、同値なのはどれでしょうか？
    それぞれについて、"yes" か "no" を書きなさい。

(a)
[[
    WHILE (BLe (ANum 1) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END
]]
    と
[[
    WHILE (BLe (ANum 2) (AId X)) DO
      X ::= APlus (AId X) (ANum 1)
    END
]]
(* FILL IN HERE *)

(b)
[[
    WHILE BTrue DO
      WHILE BFalse DO X ::= APlus (AId X) (ANum 1) END
    END
]]
    と
[[
    WHILE BFalse DO
      WHILE BTrue DO X ::= APlus (AId X) (ANum 1) END
    END
]]

(* FILL IN HERE *)

[] *)

(* ####################################################### *)
(* ** Examples *)
(** ** 例 *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. apply minus_diag.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(* For examples of command equivalence, let's start by looking at
    trivial transformations involving [SKIP]: *)
(** コマンドの同値性の例として、
    [SKIP]にからんだ自明な変換から見てみましょう: *)

Theorem skip_left: forall c,
  cequiv
     (SKIP; c)
     c.
Proof.
  intros c st st'.
  split; intros H.
  Case "->".
    inversion H. subst.
    inversion H2. subst.
    assumption.
  Case "<-".
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(* **** Exercise: 2 stars (skip_right) *)
(** **** 練習問題: ★★ (skip_right) *)
Theorem skip_right: forall c,
  cequiv
    (c; SKIP)
    c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* We can also explore transformations that simplify [IFB]
    commands: *)
(** [IFB]コマンドを簡単化する変換を探索することもできます: *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  Case "->".
    inversion H; subst. assumption. inversion H5.
  Case "<-".
    apply E_IfTrue. reflexivity. assumption.  Qed.

(* Of course, few programmers would be tempted to write a conditional
    whose guard is literally [BTrue].  A more interesting case is when
    the guard is _equivalent_ to true...

   _Theorem_: If [b] is equivalent to [BTrue], then [IFB b THEN c1
   ELSE c2 FI] is equivalent to [c1].

   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [IFB b
       THEN c1 ELSE c2 FI / st || st'] then [c1 / st || st'].

       Proceed by cases on the rules that could possibly have been
       used to show [IFB b THEN c1 ELSE c2 FI / st || st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule rule in the derivation of [IFB b THEN
         c1 ELSE c2 FI / st || st'] was [E_IfTrue].  We then have, by
         the premises of [E_IfTrue], that [c1 / st || st'].  This is
         exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [IFB b THEN c1 ELSE c2 FI / st || st'] was [E_IfFalse].
         We then know that [beval st b = false] and [c2 / st || st'].

         Recall that [b] is equivalent to [BTrue], i.e. forall [st],
         [beval st b = beval st BTrue].  In particular, this means
         that [beval st b = true], since [beval st BTrue = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if [c1 / st
       || st'] then [IFB b THEN c1 ELSE c2 FI / st || st'].

       Since [b] is equivalent to [BTrue], we know that [beval st b] =
       [beval st BTrue] = [true].  Together with the assumption that
       [c1 / st || st'], we can apply [E_IfTrue] to derive [IFB b THEN
       c1 ELSE c2 FI / st || st'].  []

   Here is the formal version of this proof: *)
(** もちろん、ガードが[BTrue]そのままである条件文を書こうとするプログラマはほとんどいないでしょう。
    より興味深いのは、ガードが真と「同値である」場合です...

   「定理」:もし[b]が[BTrue]と同値ならば、[IFB b THEN c1 ELSE c2 FI]は[c1]と同値である。

   「証明」:

     - ([->]) すべての[st]と[st']に対して、もし[IFB b THEN c1 ELSE c2 FI / st || st']
       ならば[c1 / st || st']となることを示す。

       [IFB b THEN c1 ELSE c2 FI / st || st']を示すのに使うことができた可能性のある規則、
       つまり[E_IfTrue]と[E_IfFalse]とで、場合分けをする。

       - [IFB b THEN c1 ELSE c2 FI / st || st']
         の導出の最後の規則が[E_IfTrue]であると仮定する。
         このとき、[E_IfTrue]の仮定より[c1 / st || st']となる。
         これはまさに証明したいことである。

       - 一方、[IFB b THEN c1 ELSE c2 FI / st || st']
         の導出の最後の規則が[E_IfFalse]と仮定する。
         すると、[beval st b = false]かつ[c2 / st || st']となる。

         [b]が[BTrue]と同値であったことから、
         すべての[st]について、[beval st b = beval st BTrue]が成立する。
         これは特に[beval st b = true]を意味する。
         なぜなら[beval st BTrue = true]だからである。
         しかしこれは矛盾である。なぜなら、
         [E_IfFalse]から[beval st b = false]でなければならないからである。
         従って、最後の規則は[E_IfFalse]ではあり得ない。

     - ([<-]) すべての[st]と[st']について、もし[c1 / st|| st']ならば
       [IFB b THEN c1 ELSE c2 FI / st || st']となることを示す。

       [b]が[BTrue]と同値であることから、
       [beval st b] = [beval st BTrue] = [true]となる。
       仮定[c1 / st || st']より[E_IfTrue]が適用でき、
       [IFB b THEN c1 ELSE c2 FI / st || st']となる。  []
       

   以下がこの証明の形式化版です: *)

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  Case "->".
    inversion H; subst.
    SCase "b evaluates to true".
      assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite Hb in H5.
      inversion H5.
  Case "<-".
    apply E_IfTrue; try assumption.
    rewrite Hb. reflexivity.  Qed.

(* **** Exercise: 2 stars, recommended (IFB_false) *)
(** **** 練習問題: ★★, recommended (IFB_false) *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (swap_if_branches) *)
(** **** 練習問題: ★★★ (swap_if_branches) *)
Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* For while loops, there is a similar pair of theorems: a loop whose
    guard is equivalent to [BFalse] is equivalent to [SKIP], while a
    loop whose guard is equivalent to [BTrue] is equivalent to [WHILE
    BTrue DO SKIP END] (or any other non-terminating program).  The
    first of these facts is easy. *)
(** whileループについては、同様の2つ定理があります:
    ガードが[BFalse]と同値であるループは[SKIP]と同値である、というものと、
    ガードが[BTrue]と同値であるループは[WHILE BTrue DO SKIP END]
    (あるいは他の任意の停止しないプログラム)と同値である、というものです。
    1つ目のものは簡単です。*)

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  Case "->".
    inversion H; subst.
    SCase "E_WhileEnd".
      apply E_Skip.
    SCase "E_WhileLoop".
      rewrite Hb in H2. inversion H2.
  Case "<-".
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(* **** Exercise: 2 stars (WHILE_false_informal) *)
(** **** 練習問題: ★★ (WHILE_false_informal) *)
(* Write an informal proof of WHILE_false.

(* FILL IN HERE *)
[]
*)
(** WHILE_falseの非形式的証明を記述しなさい。

(* FILL IN HERE *)
[]
*)

(* To prove the second fact, we need an auxiliary lemma stating that
    while loops whose guards are equivalent to [BTrue] never
    terminate:

    _Lemma_: If [b] is equivalent to [BTrue], then it cannot be the
    case that [(WHILE b DO c END) / st || st'].

    _Proof_: Suppose that [(WHILE b DO c END) / st || st'].  We show,
    by induction on a derivation of [(WHILE b DO c END) / st || st'],
    that this assumption leads to a contradiction.

      - Suppose [(WHILE b DO c END) / st || st'] is proved using rule
        [E_WhileEnd].  Then by assumption [beval st b = false].  But
        this contradicts the assumption that [b] is equivalent to
        [BTrue].

      - Suppose [(WHILE b DO c END) / st || st'] is proved using rule
        [E_WhileLoop].  Then we are given the induction hypothesis
        that [(WHILE b DO c END) / st || st'] is contradictory, which
        is exactly what we are trying to prove!

      - Since these are the only rules that could have been used to
        prove [(WHILE b DO c END) / st || st'], the other cases of
        the induction are immediately contradictory. [] *)
(** 2つ目の事実を証明するためには、
    ガードが[BTrue]と同値であるwhileループが停止しないことを言う補題が1つ必要です:

    「補題」:[b]が[BTrue]と同値のとき、
    [(WHILE b DO c END) / st || st']となることはない。

    「証明」:[(WHILE b DO c END) / st || st']と仮定する。
    [(WHILE b DO c END) / st || st']の導出についての帰納法によって、
    この仮定から矛盾が導かれることを示す。

      - [(WHILE b DO c END) / st || st']が規則[E_WhileEnd]
        から証明されると仮定する。すると仮定から[beval st b = false]となる。
        しかしこれは、[b]が[BTrue]と同値という仮定と矛盾する。

      - [(WHILE b DO c END) / st || st']が規則[E_WhileLoop]
        を使って証明されると仮定する。
        すると帰納法の仮定として
        [(WHILE b DO c END) / st || st']が矛盾するということが得られる。
        これはまさに証明しようとしていることである。

      - 上記が[(WHILE b DO c END) / st || st']
        の証明に使うことができる可能性がある規則のすべてであり、
        帰納法の他の場合は、すぐに矛盾になる。[] *)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  Case "E_WhileEnd". (* contradictory -- b is always true! *)
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop". (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(* **** Exercise: 2 stars, optional (WHILE_true_nonterm_informal) *)
(** **** 練習問題: ★★, optional (WHILE_true_nonterm_informal) *)
(* Explain what the lemma [WHILE_true_nonterm] means in English.

(* FILL IN HERE *)
*)
(** 補題[WHILE_true_nonterm]が意味するものを日本語で書きなさい。

(* FILL IN HERE *)
*)
(** [] *)

(* **** Exercise: 2 stars, recommended (WHILE_true) *)
(** **** 練習問題: ★★, recommended (WHILE_true) *)
(* You'll want to use [WHILE_true_nonterm] here. *)
(** ここで[WHILE_true_nonterm]を使いなさい。*)

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  Case "->".
    inversion Hce; subst.
    SCase "loop doesn't run".
      apply E_IfFalse. assumption. apply E_Skip.
    SCase "loop runs".
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  Case "<-".
    inversion Hce; subst.
    SCase "loop runs".
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    SCase "loop doesn't run".
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.

(* **** Exercise: 2 stars, optional (seq_assoc) *)
(** **** 練習問題: ★★, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Finally, let's look at simple equivalences involving assignments.
    This turns out to be a little tricky.
    To start with, we might expect to be able to show that certain
    kinds of "useless" assignments can be removed. Most trivially: *)
(** 最後に、代入に関する簡単な同値を見てみましょう。
    これは、ちょっとトリッキーです。
    まず最初に、ある種の「意味のない」代入が除去できることを示せないか、やってみましょう。
    一番自明なのは: *)

Theorem identity_assignment_first_try : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     Case "->".
       inversion H; subst.  simpl.
       replace (update st X (st X)) with st.
       constructor.
       (* But here we're stuck. The goal looks reasonable, but in fact
          it is not provable!  If we look back at the set of lemmas we
          proved about [update] in the last chapter, we can see that
          lemma [update_same] almost does the job, but not quite: it
          says that the original and updated states agree at all
          values, but this is not the same thing as saying that they
          are [eq] in Coq's sense! *)
       (* しかしここで行き詰まります。ゴールは合理的に見えますが、しかし実は証明できません!
          前の章で[update]に関して証明した補題のセットをふりかえってみましょう。
          補題[update_same]がほとんどのことをやっていますが、全部ではありません。
          [update_same]
          は元の状態と更新された状態がすべての値について一致することを言っていますが、
          それは、Coqの意味で[eq]だと言っているわけではありません! *)
Admitted.

(* What is going on here?  Recall that our states are just functions
    from identifiers to values.  For Coq, functions are only equal
    when their definitions are syntactically the same, modulo
    simplification.  (This is the only way we can legally apply the
    [eq] constructor!) In practice, for functions built up by repeated
    uses of the [update] operation, this means that two functions can
    be proven equal only if they were constructed using the _same_
    [update] operations, applied in the same order.  In the theorem
    above, the sequence of updates on the first parameter [cequiv] is
    one longer than for the second parameter, so it is no wonder that
    the equality doesn't hold.

    But the problem is quite general. If we try to prove other
    "trivial" facts, such as
[[
    cequiv (X ::= APlus (AId X ANum 1) ;
            X ::= APlus (AId X ANum 1))
           (X ::= APlus (AId X ANum 2))
]]
    or
[[
    cequiv (X ::= ANum 1; Y ::= ANum 2)
           (y ::= ANum 2; X ::= ANum 1)

]]
    we'll get stuck in the same way: we'll have two functions that
    behave the same way on all inputs, but cannot be proven to be [eq]
    to each other.

    The reasoning principle we would like to use in these situations
    is called _functional extensionality_:
[[[
                        forall x, f x = g x
                        -------------------
                               f = g
]]]
    Although this principle is not derivable in Coq's built-in logic,
    it is safe to add it as an additional _axiom_.  *)
(** 何がどうなっているのでしょう？
    我々の状態は単に識別子から値への関数であることを思い出してください。
    Coqでは、関数同士が等しいとは、その定義が簡単化(simplification)
    の範囲での変形を除いて構文的に同じということです。
    (簡単化だけが Coq で[eq]コンストラクタに適用することが許されたものなのです!)
    実際には、[update]操作の繰り返しで構築された関数については、
    2つの関数が等しいと証明できるのは「同じ」[update]操作を同じ順番で適用した場合だけです。
    上述の定理では、第一パラメータ[cequiv]のupdateの列は第二パラメータのものより1つ長いので、
    等しさが成立しないのも当然です。

    しかし、この問題はかなり一般的なものです。
    何か別の「自明な」事実、例えば
[[
    cequiv (X ::= APlus (AId X ANum 1) ;
            X ::= APlus (AId X ANum 1))
           (X ::= APlus (AId X ANum 2))
]]
    あるいは
[[
    cequiv (X ::= ANum 1; Y ::= ANum 2)
           (y ::= ANum 2; X ::= ANum 1)

]]
    を証明しようとするとき、同じように行き詰まることになります。
    つまり、すべての入力に対して同一の振る舞いをする2つの関数が出てくるのですが、
    その2つが[eq]であることが証明できないのです。

    こういった状況でこれから使おうとしている推論原理は、
    関数外延性(_functional extensionality_)と呼ばれます:
[[
                        forall x, f x = g x
                        -------------------
                               f = g
]]
    この原理は Coq のビルトインの論理からは導出できませんが、
    追加公理(_axiom_)として導入することは安全です。*)    

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* It can be shown that adding this axiom doesn't introduce any
    inconsistencies into Coq.  (In this way, it is similar to adding
    one of the classical logic axioms, such as [excluded_middle].)

    With the benefit of this axiom we can prove our theorem: *)
(** Coq にこの公理を導入することが矛盾を生むものではないことを示すことができます。
    (このように、この公理の導入は、
     [excluded_middle]のような古典論理の公理を追加するのと同様なのです。)

    この公理のおかげで、先の定理を証明することができます: *)

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     Case "->".
       inversion H; subst. simpl.
       replace (update st X (st X)) with st.
       constructor.
       apply functional_extensionality. intro.
       rewrite update_same; reflexivity.
     Case "<-".
       inversion H; subst.
       assert (st' = (update st' X (st' X))).
          apply functional_extensionality. intro.
          rewrite update_same; reflexivity.
       rewrite H0 at 2.
       constructor. reflexivity.
Qed.

(* **** Exercise: 2 stars, recommended (assign_aequiv) *)
(** **** 練習問題: ★★, recommended (assign_aequiv) *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(* * Properties of Behavioral Equivalence *)
(** * 振る舞い同値の性質 *)

(* We now turn to developing some of the properties of the program
    equivalences we have defined. *)
(** ここからは、定義したプログラムの同値概念の性質を調べていきましょう。*)

(* ####################################################### *)
(* ** Behavioral Equivalence is an Equivalence *)
(** ** 振る舞い同値は同値関係である *)

(* First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive: *)
(** 最初に、[aexps]、[bexps]、[com]の同値が、本当に「同値関係」であること、つまり、
    反射性、対称性、推移性を持つことを検証します: *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st || st' <-> c2 / st || st') as H'.
    SCase "Proof of assertion". apply H.
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st || st'). apply H12. apply H23.  Qed.

(* ########################################################*)
(* ** Behavioral Equivalence is a Congruence *)
(** ** 振る舞い同値は合同関係である *)

(* Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the whole programs in which they are embedded:
[[[
              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;c2) (c1';c2')
]]]
    ...and so on.  (Note that we are using the inference rule notation
    here not as part of a definition, but simply to write down some
    valid implications in a readable format. We prove these
    implications below.)

    We will see a concrete example of why these congruence properties
    are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)
(** よりわかりにくいですが、振る舞い同値は、合同関係(_congruence_)でもあります。
    つまり、2つのサブプログラムが同値ならば、それを含むプログラム全体も同値です:
[[
              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')

              cequiv c1 c1'
              cequiv c2 c2'
         ------------------------
         cequiv (c1;c2) (c1';c2')
]]
    ...などです。
    (注意して欲しいのですが、ここで推論規則の記法を使っていますが、これは定義の一部ではありません。
    単に正しい含意を読みやすい形で書き出しただけです。
    この含意は以下で証明します。)

    合同性がなぜ重要なのか、
    次の節で具体的な例([fold_constants_com_sound]の証明)によって見ます。
    ただ、メインのアイデアは、大きなプログラムの小さな部分を同値の小さな部分で置き換えると、
    大きなプログラム全体が元のものと同値になることを、
    変化していない部分についての明示的な証明「なしに」わかるということです。
    つまり、大きなプログラムの小さな変更についての証明の負担が、
    プログラムではなく変更に比例するということです。*)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  Case "->".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  Case "<-".
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(* The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [WHILE] -- that is, if
    [b1] is equivalent to [b1'] and [c1] is equivalent to [c1'], then
    [WHILE b1 DO c1 END] is equivalent to [WHILE b1' DO c1' END].

    _Proof_: Suppose [b1] is equivalent to [b1'] and [c1] is
    equivalent to [c1'].  We must show, for every [st] and [st'], that
    [WHILE b1 DO c1 END / st || st'] iff [WHILE b1' DO c1' END / st
    || st'].  We consider the two directions separately.

      - ([->]) We show that [WHILE b1 DO c1 END / st || st'] implies
        [WHILE b1' DO c1' END / st || st'], by induction on a
        derivation of [WHILE b1 DO c1 END / st || st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileEnd] or [E_WhileLoop].

          - [E_WhileEnd]: In this case, the form of the rule gives us
            [beval st b1 = false] and [st = st'].  But then, since
            [b1] and [b1'] are equivalent, we have [beval st b1' =
            false], and [E-WhileEnd] applies, giving us [WHILE b1' DO
            c1' END / st || st'], as required.

          - [E_WhileLoop]: The form of the rule now gives us [beval st
            b1 = true], with [c1 / st || st'0] and [WHILE b1 DO c1
            END / st'0 || st'] for some state [st'0], with the
            induction hypothesis [WHILE b1' DO c1' END / st'0 ||
            st'].

            Since [c1] and [c1'] are equivalent, we know that [c1' /
            st || st'0].  And since [b1] and [b1'] are equivalent, we
            have [beval st b1' = true].  Now [E-WhileLoop] applies,
            giving us [WHILE b1' DO c1' END / st || st'], as
            required.

      - ([<-]) Similar. [] *)
(** ループの合同性は帰納法が必要になるので、さらに少しおもしろいものになります。

    「定理」:[WHILE]についての同値は合同関係である。
    すなわち、もし[b1]が[b1']と同値であり、[c1]が[c1']と同値ならば、
    [WHILE b1 DO c1 END]は[WHILE b1' DO c1' END]と同値である。

    「証明」:[b1]が[b1']と同値、[c1]が[c1']と同値であるとする。
    すべての[st]と[st']について、証明すべきことは、
    [WHILE b1 DO c1 END / st || st']の必要十分条件は
    [WHILE b1' DO c1' END / st || st']であることである。
    必要条件と十分条件の両方向を別々に証明する。

      - ([->]) [WHILE b1 DO c1 END / st || st']ならば
        [WHILE b1' DO c1' END / st || st']であることを、
        [WHILE b1 DO c1 END / st || st']の導出についての帰納法で示す。
        自明でないのは、導出の最後の規則が[E_WhileEnd]または[E_WhileLoop]のときだけである。

          - [E_WhileEnd]: この場合、
            規則の形から[beval st b1 = false]かつ[st = st']となる。
            しかし[b1]と[b1']が同値であることから
            [beval st b1' = c1' END / st || st']になる。
            さらに[E-WhileEnd]を適用すると
            証明すべき[WHILE b1' DO c1' END / st || st']が得られる。

          - [E_WhileLoop]: 規則の形から
            [beval st b1 = true]および、ある状態[st'0]について
            帰納法の仮定[WHILE b1' DO c1' END / st'0 || st']のもとで、
            [c1 / st || st'0]かつ[WHILE b1 DO c1 END / st'0 || st']となる。

            [c1]と[c1']が同値であることから、[c1' / st || st'0]となる。
            さらに[b1]と[b1']が同値であることから、[beval st b1' = true]となる。
            [E-WhileLoop]を適用すると、
            証明すべき[WHILE b1' DO c1' END / st || st']が得られる。

      - ([<-]) 同様である。[] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  Case "->".
    remember (WHILE b1 DO c1 END) as cwhile.
    induction Hce; inversion Heqcwhile; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite <- Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st').  apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.
  Case "<-".
    remember (WHILE b1' DO c1' END) as c'while.
    induction Hce; inversion Heqc'while; subst.
    SCase "E_WhileEnd".
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    SCase "E_WhileLoop".
      apply E_WhileLoop with (st' := st').
      SSCase "show loop runs". rewrite -> Hb1e. apply H.
      SSCase "body execution".
        apply (Hc1e st st').  apply Hce1.
      SSCase "subsequent loop execution".
        apply IHHce2. reflexivity.  Qed.

(* **** Exercise: 3 stars, optional (CSeq_congruence) *)
(** **** 練習問題: ★★★, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;c2) (c1';c2').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (CIf_congruence) *)
(** **** 練習問題: ★★★ (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* For example, here are two equivalent programs and a proof of their
    equivalence... *)
(** 同値である2つのプログラムとその同値の証明の例です... *)

Example congruence_example:
  cequiv
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= ANum 0;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- changed here *)
     ELSE
       Y ::= ANum 42
     FI).
Proof.
  apply CSeq_congruence.
    apply refl_cequiv.
    apply CIf_congruence.
      apply refl_bequiv.
      apply CAss_congruence. unfold aequiv. simpl.
        symmetry. apply minus_diag.
      apply refl_cequiv.
Qed.

(* ####################################################### *)
(* * Case Study: Constant Folding *)
(** * ケーススタディ: 定数畳み込み *)

(* A _program transformation_ is a function that takes a program
    as input and produces some variant of the program as its
    output.  Compiler optimizations such as constant folding are
    a canonical example, but there are many others. *)
(** プログラム変換(_program transformation_)とは、
    プログラムを入力とし、出力としてそのプログラムの何らかの変形を生成する関数です。
    定数畳み込みのようなコンパイラの最適化は標準的な例ですが、それ以外のものもたくさんあります。*)

(* ####################################################### *)
(* ** Soundness of Program Transformations *)
(** ** プログラム変換の健全性 *)

(* A program transformation is _sound_ if it preserves the
    behavior of the original program.

    We can define a notion of soundness for translations of
    [aexp]s, [bexp]s, and [com]s. *)
(** プログラム変換が健全(_sound_)とは、その変換が元のプログラムの振る舞いを保存することです。
    
    [aexp]、[bexp]、[com]の変換の健全性の概念を定義することができます。*)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ######################################################## *)
(* ** The Constant-Folding Transformation *)
(** ** 定数畳み込み変換 *)

(* An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)
(** 式が定数(_constant_)であるとは、その式が変数参照を含まないことです。

    定数畳み込みは、定数式をその値に置換する最適化です。*)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(* Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)
(** 定数畳み込みのこのバージョンは簡単な足し算等を消去していないことに注意します。
    複雑になるのを避けるため、1つの最適化に焦点を絞っています。
    式の単純化の他の方法を組込むことはそれほど難しいことではありません。
    定義と証明が長くなるだけです。*)

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

(* Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases), we can also find constant _boolean_
    expressions and reduce them in-place. *)
(** ([BEq]と[BLe]の場合に)[fold_constants_aexp]を[bexp]
    に持ち上げることができるだけでなく、定数「ブール」式をみつけてその場で置換することもできます。*)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

(* To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)
(** コマンド内の定数を畳み込みするために、含まれるすべての式に対応する畳み込み関数を適用します。*)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ; c2  =>
      (fold_constants_com c1) ; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (X ::= APlus (ANum 4) (ANum 5);
     Y ::= AMinus (AId X) (ANum 3);
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END) =
  (X ::= ANum 9;
   Y ::= AMinus (AId X) (ANum 3);
   IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
     SKIP
   ELSE
     (Y ::= ANum 0)
   FI;
   Y ::= ANum 0;
   WHILE BEq (AId Y) (ANum 0) DO
     X ::= APlus (AId X) (ANum 1)
   END).
Proof. reflexivity. Qed.

(* ################################################### *)
(* ** Soundness of Constant Folding *)
(** ** 定数畳み込みの健全性 *)

(* Now we need to show that what we've done is correct.  Here's
    the proof for arithmetic expressions: *)
(** 上でやったことが正しいことを示さなければなりません。以下が算術式に対する証明です: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  aexp_cases (induction a) Case; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (APlus a1 a2)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(* **** Exercise: 3 stars, optional (fold_bexp_BEq_informal) *)
(** **** 練習問題: ★★★, optional (fold_bexp_BEq_informal) *)
(* Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [BEq a1 a2].

   In this case, we must show
[[
       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).
]]
   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have
[[
           fold_constants_bexp (BEq a1 a2)
         = if beq_nat n1 n2 then BTrue else BFalse
]]
       and
[[
           beval st (BEq a1 a2)
         = beq_nat (aeval st a1) (aeval st a2).
]]
       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know
[[
           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1
]]
       and
[[
           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,
]]
       so
[[
           beval st (BEq a1 a2)
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.
]]
       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that
[[
           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.
]]
       So
[[
           beval st (BEq a1 a2)
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
]]
       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show
[[
           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),
]]
       which, by the definition of [beval], is the same as showing
[[
           beq_nat (aeval st a1) (aeval st a2)
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).
]]
       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us
[[
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
]]
       completing the case.  []
*)
(** ここに、ブール式の定数畳み込みに関する健全性の議論の[BEq]の場合の非形式的証明を示します。
    これを丁寧に読みその後の形式的証明と比較しなさい。
    次に、形式的証明の[BLe]部分を(もし可能ならば[BEq]の場合を見ないで)記述しなさい。

   「定理」:ブール式に対する定数畳み込み関数[fold_constants_bexp]は健全である。

   「証明」:すべてのブール式[b]について[b]が[fold_constants_bexp]
   と同値であることを示す。
   [b]についての帰納法を行う。
   [b]が[BEq a1 a2]という形の場合を示す。

   この場合、
[[
       beval st (BEq a1 a2)
     = beval st (fold_constants_bexp (BEq a1 a2)).
]]
   を示せば良い。これには2種類の場合がある:

     - 最初に、ある[n1]と[n2]について、[fold_constants_aexp a1 = ANum n1]かつ
       [fold_constants_aexp a2 = ANum n2]と仮定する。

       この場合、
[[
           fold_constants_bexp (BEq a1 a2)
         = if beq_nat n1 n2 then BTrue else BFalse
]]
       かつ
[[
           beval st (BEq a1 a2)
         = beq_nat (aeval st a1) (aeval st a2).
]]
       となる。
       算術式についての定数畳み込みの健全性(補題[fold_constants_aexp_sound])より、
[[
           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1
]]
       かつ
[[
           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,
]]
       である。
       従って、
[[
           beval st (BEq a1 a2)
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.
]]
       となる。また、([n1 = n2]と[n1 <> n2]の場合をそれぞれ考えると)
[[
           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.
]]
       となることは明らかである。
       ゆえに
[[
           beval st (BEq a1 a2)
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
]]
       となる。これは求められる性質である。

     - それ以外の場合、[fold_constants_aexp a1]と[fold_constants_aexp a2]
       のどちらかは定数ではない。この場合、
[[
           beval st (BEq a1 a2)
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),
]]
       を示せば良い。
       [beval]の定義から、これは     
[[
           beq_nat (aeval st a1) (aeval st a2)
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).
]]
       を示すことと同じである。
       算術式についての定数畳み込みの健全性([fold_constants_aexp_sound])より、
[[
         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),
]]
       となり、この場合も成立する。[]
*)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  bexp_cases (induction b) Case;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  Case "BEq".
    (* Doing induction when there are a lot of constructors makes
       specifying variable names a chore, but Coq doesn't always
       choose nice variable names.  We can rename entries in the
       context with the [rename] tactic: [rename a into a1] will
       change [a] to [a1] in the current goal and context. *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1'.
    remember (fold_constants_aexp a2) as a2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      (* The only interesting case is when both a1 and a2
         become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  Case "BLe".
    (* FILL IN HERE *) admit.
  Case "BNot".
    simpl. remember (fold_constants_bexp b) as b'.
    rewrite IHb.
    destruct b'; reflexivity.
  Case "BAnd".
    simpl.
    remember (fold_constants_bexp b1) as b1'.
    remember (fold_constants_bexp b2) as b2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.  Qed.
(** [] *)

(* **** Exercise: 3 stars (fold_constants_com_sound) *)
(** **** 練習問題: ★★★ (fold_constants_com_sound) *)
(* Complete the [WHILE] case of the following proof. *)
(** 次の証明の[WHILE]の場合を完成させなさい。*)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";". apply CSeq_congruence; assumption.
  Case "IFB".
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    remember (fold_constants_bexp b) as b'.
    destruct b';
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ########################################################## *)
(* *** Soundness of (0 + n) Elimination, Redux *)
(** *** (0 + n)の消去の健全性、再び *)

(* **** Exercise: 4 stars, optional (optimize_0plus) *)
(** **** 練習問題: ★★★★, optional (optimize_0plus) *)
(* Recall the definition [optimize_0plus] from Imp.v:
[[
    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.
]]
   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   and analogous ones for [bexp]s and commands:
[[
     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
]]
   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] (otherwise it will be _long_!).

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)
(** Imp_J.vの[optimize_0plus]の定義をふり返ります。
[[
    Fixpoint optimize_0plus (e:aexp) : aexp :=
      match e with
      | ANum n =>
          ANum n
      | APlus (ANum 0) e2 =>
          optimize_0plus e2
      | APlus e1 e2 =>
          APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
          AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
          AMult (optimize_0plus e1) (optimize_0plus e2)
      end.
]]
   この関数は、[aexp]の上で定義されていて、状態を扱わないことに注意します。

   変数を扱えるようにした、この関数の新しいバージョンを記述しなさい。
   また、[bexp]およびコマンドに対しても、同様のものを記述しなさい:
[[
     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
]]
   これらの関数の健全性を、[fold_constants_*]について行ったのと同様に証明しなさい。
   [optimize_0plus_com]の証明においては、合同性補題を確実に使いなさい
   (そうしなければ証明はとても長くなるでしょう!)。

   次に、コマンドに対して次の処理を行う最適化関数を定義しなさい。行うべき処理は、
   まず定数畳み込みを([fold_constants_com]を使って)行い、
   次に[0 + n]項を([optimize_0plus_com]を使って)消去することです。

   - この最適化関数の出力の意味のある例を示しなさい。

   - この最適化関数が健全であることを示しなさい。(この部分は「とても」簡単なはずです。) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(* * Proving That Programs Are _Not_ Equivalent *)
(** * プログラムが同値でないことを証明する *)

(* Suppose that [c1] is a command of the form [X ::= a1; Y ::= a2]
    and [c2] is the command [X ::= a1; Y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:
[[
       c1  =  (X ::= 42 + 53;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;
               Y ::= Y + (42 + 53))
]]
    Clearly, this particular [c1] and [c2] are equivalent.  But is
    this true in general? *)
(** [c1]が[X ::= a1; Y ::= a2]という形のコマンドで、
    [c2]がコマンド[X ::= a1; Y ::= a2']であると仮定します。ただし[a2']は、
    [a2]の中のすべてのXを[a1]で置換したものとします。
    例えば、[c1]と[c2]は次のようなものです。
[[
       c1  =  (X ::= 42 + 53;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;
               Y ::= Y + (42 + 53))
]]
    明らかに、この例の場合は[c1]と[c2]は同値です。
    しかし、一般にそうだと言えるでしょうか？ *)

(* We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own (or remember the one from the discussion in class). *)
(** この後すぐ、そうではないことを示します。
    しかし、ここでちょっと立ち止まって、
    自分の力で反例を見つけることができるか試してみるのは意味があることです。
    (あるいは、クラスでの議論を思い出してください。) *)

(* Here, formally, is the function that substitutes an arithmetic
    expression for each occurrence of a given variable in another
    expression: *)
(** 次が、式の中の指定された変数を別の算術式で置換する関数の形式的定義です。*)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i'       => if beq_id i i' then u else AId i'
  | APlus a1 a2  => APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  => AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(* And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)
(** そして次が、興味対象の性質です。
    上記コマンド[c1]と[c2]が常に同値であることを主張するものです。*)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1; i2 ::= a2)
         (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

(* Sadly, the property does _not_ always hold.

    _Theorem_: It is not the case that, for all [i1], [i2], [a1],
    and [a2],
[[
         cequiv (i1 ::= a1; i2 ::= a2)
                (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).
]]
    _Proof_: Suppose, for a contradiction, that for all [i1], [i2],
    [a1], and [a2], we have
[[
      cequiv (i1 ::= a1; i2 ::= a2)
             (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).
]]
    Consider the following program:
[[
         X ::= APlus (AId X) (ANum 1); Y ::= AId X
]]
    Note that
[[
         (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
         / empty_state || st1,
]]
    where [st1 = { X |-> 1, Y |-> 1 }].

    By our assumption, we know that
[[
        cequiv (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
]]
    so, by the definition of [cequiv], we have
[[
        (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
        / empty_state || st1.
]]
    But we can also derive
[[
        (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
        / empty_state || st2,
]]
    where [st2 = { X |-> 1, Y |-> 2 }].  Note that [st1 <> st2]; this
    is a contradiction, since [ceval] is deterministic!  [] *)
(** 残念ながら、この性質は、常には成立「しません」。

    「定理」:すべての[i1], [i2], [a1], [a2]について、次が成立するわけではない:
[[
         cequiv (i1 ::= a1; i2 ::= a2)
                (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).
]]
    「証明」:仮にすべての[i1], [i2], [a1], [a2]について
[[
      cequiv (i1 ::= a1; i2 ::= a2)
             (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2)
]]
    が成立するとする。
    次のプログラムを考える:
[[
         X ::= APlus (AId X) (ANum 1); Y ::= AId X
]]
    次のことに注意する:
[[
         (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
         / empty_state || st1,
]]
    ここで [st1 = { X |-> 1, Y |-> 1 }]である。

    仮定より、次が言える:
[[
        cequiv (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
]]
    すると、[cequiv]の定義より、次が言える:
[[
        (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
        / empty_state || st1.
]]
    しかし次のことも言える:
[[
        (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
        / empty_state || st2,
]]
    ただし[st2 = { X |-> 1, Y |-> 2 }]である。
    [st1 <> st2]に注意すると、これは[ceval]が決定性を持つことに矛盾する!
      [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = {X |-> 1, Y |-> 1}
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (update (update empty_state X 1) Y 1) as st1.
  remember (update (update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state || st1);
  assert (H2: c2 / empty_state || st2);
  try (subst;
       apply E_Seq with (st' := (update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(* **** Exercise: 4 stars (better_subst_equiv) *)
(** **** 練習問題: ★★★★ (better_subst_equiv) *)
(* The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)
(** 上で成立すると考えていた同値は、完全に意味がないものではありません。
    それは実際、ほとんど正しいのです。それを直すためには、
    最初の代入の右辺に変数[X]が現れる場合を排除すれば良いのです。*)

Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
  | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
  | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult: forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (update st i ni) a = aeval st a.
Proof.
  (* FILL IN HERE *) Admitted.

(* Using [var_not_used_in_aexp], formalize and prove a correct verson
    of [subst_equiv_property]. *)
(** [var_not_used_in_aexp]を使って、[subst_equiv_property]の正しいバージョンを形式化し、
    証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 3 stars, recommended (inequiv_exercise) *)
(** **** 練習問題: ★★★, recommended (inequiv_exercise) *)
Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(* * Doing Without Extensionality (Optional) *)
(** * 外延性を使わずに行う (Optional) *)

(* Purists might object to using the [functional_extensionality]
    axiom.  In general, it can be quite dangerous to add axioms,
    particularly several at once (as they may be mutually
    inconsistent). In fact, [functional_extensionality] and
    [excluded_middle] can both be assumed without any problems, but
    some Coq users prefer to avoid such "heavyweight" general
    techniques, and instead craft solutions for specific problems that
    stay within Coq's standard logic.

    For our particular problem here, rather than extending the
    definition of equality to do what we want on functions
    representing states, we could instead give an explicit notion of
    _equivalence_ on states.  For example: *)
(** 純粋主義者は、[functional_extensionality]を使うことに不服かもしれません。
    一般に、公理を追加することは非常に危険です。
    特に、一度にいくつも追加するときは(追加するものが相互に矛盾することもあるため)
    そうです。
    実際は、[functional_extensionality]と[excluded_middle]
    は両者とも何の問題もなく導入できます。
    しかし、Coqユーザの中には、このような「ヘビーウェイト」の一般テクニックを避け、
    Coqの標準論理の中で特定の問題のために技巧的解法を使うことを選びたい人もいるでしょう。

    ここで扱っている問題に特定するなら、
    状態を表現している関数についてやりたいことをやるために等しさの定義を拡張するより、
    状態の同値(_equivalence_)の概念を明示的に与えることもできたかもしれません。
    例えば: *)

Definition stequiv (st1 st2 : state) : Prop :=
  forall (X:id), st1 X = st2 X.

Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

(* It is easy to prove that [stequiv] is an _equivalence_ (i.e., it
   is reflexive, symmetric, and transitive), so it partitions the set
   of all states into equivalence classes. *)
(** [stequiv]が同値関係(_equivalence_、 つまり、反射的、対称的、推移的関係)
    であることを証明することは容易です。この同値関係により、
    すべての状態の集合は同値類に分割されます。*)

(* **** Exercise: 1 star, optional (stequiv_refl) *)
(** **** 練習問題: ★, optional (stequiv_refl) *)
Lemma stequiv_refl : forall (st : state),
  st ~ st.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (stequiv_sym) *)
(** **** 練習問題: ★, optional (stequiv_sym) *)
Lemma stequiv_sym : forall (st1 st2 : state),
  st1 ~ st2 ->
  st2 ~ st1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (stequiv_trans) *)
(** **** 練習問題: ★, optional (stequiv_trans) *)
Lemma stequiv_trans : forall (st1 st2 st3 : state),
  st1 ~ st2 ->
  st2 ~ st3 ->
  st1 ~ st3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Another useful fact... *)
(** 別の有用な事実です... *)
(* **** Exercise: 1 star, optional (stequiv_update) *)
(** **** 練習問題: ★, optional (stequiv_update) *)
Lemma stequiv_update : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (X:id) (n:nat),
  update st1 X n ~ update st2 X n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* It is then straightforward to show that [aeval] and [beval] behave
    uniformly on all members of an equivalence class: *)
(** [aeval]と[beval]が同値類のすべての要素に対して同じように振る舞うことは、
    ここからストレートに証明できます: *)

(* **** Exercise: 2 stars, optional (stequiv_aeval) *)
(** **** 練習問題: ★★, optional (stequiv_aeval) *)
Lemma stequiv_aeval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (a:aexp), aeval st1 a = aeval st2 a.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (stequiv_beval) *)
(** **** 練習問題: ★★, optional (stequiv_beval) *)
Lemma stequiv_beval : forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (b:bexp), beval st1 b = beval st2 b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* We can also characterize the behavior of [ceval] on equivalent
    states (this result is a bit more complicated to write down
    because [ceval] is a relation). *)
(** 同値である状態の面から[ceval]の振る舞いを特徴づけることもできます
    ([ceval]は関係なので、この結果を書き下すのはもうちょっと複雑です)。 *)

Lemma stequiv_ceval: forall (st1 st2 : state),
  st1 ~ st2 ->
  forall (c: com) (st1': state),
    (c / st1 || st1') ->
    exists st2' : state,
    ((c / st2 || st2') /\  st1' ~ st2').
Proof.
  intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
  induction CEV1; intros st2 STEQV.
  Case "SKIP".
    exists st2. split.
      constructor.
      assumption.
  Case ":=".
    exists (update st2 l n). split.
       constructor.  rewrite <- H. symmetry.  apply stequiv_aeval.
       assumption. apply stequiv_update.  assumption.
  Case ";".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''.  split.
      apply E_Seq with st2';  assumption.
      assumption.
  Case "IfTrue".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'.  split.
      apply E_IfTrue.  rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption. assumption.
  Case "IfFalse".
    destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
    exists st2'. split.
     apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
     assumption.  assumption. assumption.
  Case "WhileEnd".
    exists st2. split.
      apply E_WhileEnd. rewrite <- H. symmetry. apply stequiv_beval.
      assumption. assumption.
  Case "WhileLoop".
    destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
    destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
    exists st2''. split.
      apply E_WhileLoop with st2'.  rewrite <- H. symmetry.
      apply stequiv_beval. assumption. assumption. assumption.
      assumption.
Qed.

(* Now we need to redefine [cequiv] to use [~] instead of [=].  It is
    not completely trivial to do this in a way that keeps the
    definition simple and symmetric, but here is one approach (thanks
    to Andrew McCreight). We first define a looser variant of [||]
    that "folds in" the notion of equivalence. *)
(** ここで[cequiv]を[=]の代わりに[~]を使って再定義する必要があります。
    定義の簡潔さと対称性を保ったまま再定義するのは、それほど自明なことではありません。
    しかしその方法はあります(Andrew McCreightに感謝します)。
    最初に[||]のより緩いバージョンを定義します。
    これは同値概念の中に「畳み込まれ」ます。*)

Reserved Notation "c1 '/' st '||'' st'" (at level 40, st at level 39).

Inductive ceval' : com -> state -> state -> Prop :=
  | E_equiv : forall c st st' st'',
    c / st || st' ->
    st' ~ st'' ->
    c / st ||' st''
  where   "c1 '/' st '||'' st'" := (ceval' c1 st st').

(* Now the revised definition of [cequiv'] looks familiar: *)
(** すると[cequiv']の新しい定義は馴染みのあるものになります: *)

Definition cequiv' (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st ||' st') <-> (c2 / st ||' st').

(* A sanity check shows that the original notion of command
   equivalence is at least as strong as this new one.  (The converse
   is not true, naturally.) *)
(** もとのコマンド同値の概念が、新しいものより弱くはないことをサニティチェックします。
    (その逆は当然成立しません。) *)

Lemma cequiv__cequiv' : forall (c1 c2: com),
  cequiv c1 c2 -> cequiv' c1 c2.
Proof.
  unfold cequiv, cequiv'; split; intros.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0); assumption. assumption.
    inversion H0 ; subst.  apply E_equiv with st'0.
    apply (H st st'0). assumption. assumption.
Qed.

(* **** Exercise: 2 stars, optional (identity_assignment') *)
(** **** 練習問題: ★★, optional (identity_assignment') *)
(* Finally, here is our example once more... (You can complete the
    proof.) *)
(** 最後にもとの例を再度扱います... (証明を完成しなさい。) *)

Example identity_assignment' :
  cequiv' SKIP (X ::= AId X).
Proof.
    unfold cequiv'.  intros.  split; intros.
    Case "->".
      inversion H; subst; clear H. inversion H0; subst.
      apply E_equiv with (update st'0 X (st'0 X)).
      constructor. reflexivity.  apply stequiv_trans with st'0.
      unfold stequiv. intros. apply update_same.
      reflexivity. assumption.
    Case "<-".
      (* FILL IN HERE *) Admitted.
(** [] *)

(* On the whole, this explicit equivalence approach is considerably
    harder to work with than relying on functional
    extensionality. (Coq does have an advanced mechanism called
    "setoids" that makes working with equivalences somewhat easier, by
    allowing them to be registered with the system so that standard
    rewriting tactics work for them almost as well as for equalities.)
    But it is worth knowing about, because it applies even in
    situations where the equivalence in question is _not_ over
    functions.  For example, if we chose to represent state mappings
    as binary search trees, we would need to use an explicit
    equivalence of this kind. *)
(** 概して、この明示的な同値のアプローチは、関数外延性を使うものよりかなり難しくなります。
    (Coqは"setoids"という先進的な仕組みを持っています。
    setoid は同値関係の扱いをいくらか容易にします。
    その方法は、同値関係をシステムに登録すると、
    それを使った書き換えタクティックが、もとの等しさ(equality)
    に対してとほとんど同じようにはたらくようになるというものです。)
    しかしこの、状態の同値を明示的に記述する方法は知っておく価値があります。
    なぜなら、この方法は、問題となる同値が関数についてのもの「ではない」状況でも使えるからです。
    例えば、状態の写像を二分探索木を使って行ったとすると、
    このような明示的な同値を使う必要があるでしょう。*)

(* ####################################################### *)
(* * Additional Exercises *)
(** * さらなる練習問題 *)

(* **** Exercise: 4 stars, optional (for_while_equiv) *)
(** **** 練習問題: ★★★★, optional (for_while_equiv) *)
(* This exercise extends the optional add_for_loop exercise from
    Imp.v, where you were asked to extend the language of commands
    with C-style [for] loops.  Prove that the command:
[[
      for (c1 ; b ; c2) {
          c3
      }
]]
    is equivalent to:
[[
       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
]]
*)
(** この練習問題は、Imp_J.vのoptionalの練習問題 add_for_loop を拡張したものです。
    もとの add_for_loop は、コマンド言語に C-言語のスタイルの [for]ループを
    拡張しなさい、というものでした。
    ここでは次のことを証明しなさい:    
[[
      for (c1 ; b ; c2) {
          c3
      }
]]
    は
[[
       c1 ;
       WHILE b DO
         c3 ;
         c2
       END
]]
    と同値である。
*)
(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 3 stars, optional (swap_noninterfering_assignments) *)
(** **** 練習問題: ★★★, optional (swap_noninterfering_assignments) *)
Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1; l2 ::= a2)
    (l2 ::= a2; l1 ::= a1).
Proof.
(* Hint: You'll need [functional_extensionality] *)
(* ヒント: [functional_extensionality]を必要とするでしょう。 *)
(* FILL IN HERE *) Admitted.
(** [] *)

