(** * Imp_J: 単純な命令型プログラム *)

(* $Date: 2011-06-22 14:56:13 -0400 (Wed, 22 Jun 2011) $ *)

(* In this chapter, we begin a new direction that we'll
    continue for the rest of the course: up to now we've been mostly
    studying Coq itself, but from now on we'll mostly be using Coq to
    formalize other things.
    
    ...
    This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, the best known logic for
    reasoning about imperative programs. *)
(** この章では、コースの残りに続く新しい方向へ進み始めます。
    ここまではもっぱらCoq自身について学習してきましたが、ここからは、
    主として別のものを形式化するためにCoqを使います。
    
    はじめの例は、Imp と呼ばれる単純な命令型プログラミング言語です。
    下の例は、おなじみの数学的関数を Imp で書いたものです。
[[
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
]]
    この章ではImpの構文(_syntax_)と意味(_semantics_)をどのように定義するかを見ます。
    続く章では、プログラムの同値性(_program equivalence_)の理論を展開し、
    命令型プログラムについての推論のための論理として一番知られているホーア論理
    (_Hoare Logic_)を紹介します。 *)

(* ####################################################### *)
(* *** Sflib *)
(** *** Sflib *)

(* A minor technical point: Instead of asking Coq to import our
    earlier definitions from [Logic.v], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  You won't notice much difference, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing this is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)
(** マイナーな技術的ポイント: ここまでの定義を[Logic_J.v]からインポートする代わりに、
    [Sflib_J.v]という小さなライブラリをインポートします。
    このライブラリは、前の章の定義や定理のうち、残りの章で実際に使うものだけを集めたものです。
    読者はそれほど違うものとは感じないでしょう。というのは、
    Sflib で抜けているもののほとんどは、Coqの標準ライブラリの定義と同じものだからです。
    こうする主な理由は、Coqのグローバルな環境を整理して、例えば、
    関係する定理を探すのを容易にするためです。 *)

Require Export SfLib_J.

(* ####################################################### *)
(* * Arithmetic and Boolean Expressions *)
(** * 算術式とブール式 *)

(* We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)
(** Impを三つの部分に分けて示します: 最初に算術式(_arithmetic expressions_)
    とブール式(_boolean expressions_)、次にこれらの式に変数(_variables_)を加えたもの、
    そして最後に代入(assignment)、条件分岐(conditions)、コマンド合成(sequencing)、
    ループ(loops)を持つコマンド(_commands_)の言語です。*)

Module AExp.

(* ####################################################### *)
(* ** Syntax *)
(** ** 構文 *)

(* These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)
(** 次の2つの定義は、算術式とブール式の抽象構文(_abstract syntax_)を定めます。*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The file [ImpParser.v] develops a
    simple implementation of a lexical analyzer and parser that can
    perform this translation.  You do _not_ need to understand that
    file to understand this one, but if you haven't taken a course
    where these techniques are covered (e.g., a compilers course) you
    may want to skim it. *)
(** この章では、プログラマが実際に書く具象構文から抽象構文木への変換は省略します。
    例えば、文字列["1+2*3"]をAST(Abstract Syntax Tree, 抽象構文木) 
    [APlus (ANum 1) (AMult (ANum 2) (ANum 3))] にする変換のことです。
    この変換ができる字句解析器と構文解析器をファイル[ImpParser_J.v]で簡単に実装します。
    このファイル([Imp_J.v])を理解するには[ImpParser_J.v]の理解は必要ではありませんが、
    もしそれらの技術についてのコース(例えばコンパイラコース)を受講していないならば、
    ざっと見てみるのも良いでしょう。 *)

(* For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:
[[
    aexp ::= nat
           | aexp '+' aexp
           | aexp '-' aexp
           | aexp '*' aexp

    bexp ::= true
           | false
           | aexp '=' aexp
           | aexp '<=' aexp
           | bexp 'and' bexp
           | 'not' bexp
]]
*)
(** 比較のため、同じ抽象構文を定義する慣習的なBNF(Backus-Naur Form)
    文法を以下に示します:
[[
    aexp ::= nat
           | aexp '+' aexp
           | aexp '-' aexp
           | aexp '*' aexp

    bexp ::= true
           | false
           | aexp '=' aexp
           | aexp '<=' aexp
           | bexp 'and' bexp
           | 'not' bexp
]]
*)

(* Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and arguably
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to which
         form of BNF they're using because there is no need to: a
         rough-and-ready informal understanding is all that's
         needed. *)
(** 上述のCoq版と比較して...

       - BNFはより非形式的です。例えば、
         BNFは式の表面的な構文についていくらかの情報を与えています
         (可算は[+]と記述され、それは中置記号であるという事実などです)が、
         字句解析と構文解析の他の面は定めないままになっています([+]、[-]、[*]
         の相対的優先順位などです)。
         (例えばコンパイラを実装するときに)この記述を形式的定義にするためには、
         追加の情報、および人間の知性が必要でしょう。

         Coq版はこれらの情報を整合的に省略し、抽象構文だけに集中します。

       - 一方、BNF版はより軽くて、おそらく読むのがより簡単です。
         非形式的であることで柔軟性を持っているので、
         黒板を使って議論する場面などでは特段に有効です。
         そういう場面では、細部をいちいち正確に確定させていくことより、
         全体的アイデアを伝えることが重要だからです。

         実際、BNFのような記法は山ほどあり、人は皆、それらの間を自由に行き来しますし、
         通常はそれらのうちのどのBNFを使っているかを気にしません。
         その必要がないからです。おおざっぱな非形式的な理解だけが必要なのです。 *)

(* It's good to be comfortable with both sorts of notations: informal
    ones for communicating between humans and formal ones for carrying
    out implementations and proofs. *)
(** 両方の記法に通じているのは良いことです。
    非形式的なものは人間とのコミュニケーションのために、
    形式的なものは実装と証明のためにです。 *)


(* ####################################################### *)
(* ** Evaluation *)
(** ** 評価 *)

(* _Evaluating_ an arithmetic expression reduces it to a single number. *)
(** 算術式を評価する(_evaluating_)とその式を1つの数に簡約します。 *)

Fixpoint aeval (e : aexp) : nat :=
  match e with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(* Similarly, evaluating a boolean expression yields a boolean. *)
(** 同様に、ブール式を評価するとブール値になります。*)

Fixpoint beval (e : bexp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* ####################################################### *)
(* ** Optimization *)
(** ** 最適化(Optimization) *)

(* We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)
(** ここまで定義したものはわずかですが、その定義から既にいくらかのものを得ることができます。
    算術式をとって、それを少し簡単化する関数を定義するとします。
    すべての [0+e] (つまり [(APlus (ANum 0) e)])を単に[e]にするものです。 *)

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

(* To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)
(** この最適化が正しいことをすることを確認するために、
    いくつかの例についてテストして出力がよさそうかを見てみることができます。 *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(* But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)
(** しかし、もし最適化が正しいことを確認したいならば、
    -- つまり、最適化した式がオリジナルの式と同じ評価結果を返すことを確認したいならば、
    証明すべきです。 *)

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHe2.
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2".
      simpl. simpl in IHe1. rewrite IHe1.
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.

(* ####################################################### *)
(* * Coq Automation *)
(** * Coq の自動化 *)

(* The repetition in this last proof is starting to be a little
    annoying.  It's still just about bearable, but if either the
    language of arithmetic expressions or the optimization being
    proved sound were significantly more complex, it would begin to be
    a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its very powerful
    facilities for constructing proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us to
    scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, or low-level details. *)
(** 前の証明の最後の繰り返しはちょっと面倒です。今のところまだ耐えられますが、
    証明対象の言語や算術式や最適化が今に比べて著しく複雑だったら、現実的に問題になるでしょう。

    ここまで、Coq のタクティックのほんのひとつかみだけですべての証明をしてきていて、
    証明を自動的に構成する非常に強力な機構を完全に無視してきました。
    このセクションではこれらの機構のいくつかを紹介します。
    それ以上のものを、以降のいくつかの章で次第に見ることになるでしょう。
    それらに慣れるには多少エネルギーが必要でしょう。
    -- Coq の自動化は電動工具です。--
    しかし自動化機構を使うことで、より複雑な定義や、より興味深い性質について、
    退屈で繰り返しの多いローレベルな詳細に飲み込まれることなく、
    作業をスケールアップできます。 *)

(* ####################################################### *)
(* ** Tacticals *)
(** ** タクティカル(Tacticals) *)

(* _Tactical_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)
(** タクティカル(_tactical_)は Coq の用語で、
    他のタクティックを引数に取るタクティックのことです。
    「高階タクティック」("higher-order tactics")と言っても良いでしょう。 *)

(* ####################################################### *)
(* *** The [try] Tactical *)
(** *** [try]タクティカル *)

(* One very simple tactical is [try]: If [T] is a tactic, then [try
    T] is a tactic that is just like [T] except that, if [T] fails,
    [try T] does nothing at all (instead of failing). *)
(** 非常にシンプルなタクティカルの1つが[try]です。[T]がタクティックのとき、
    タクティック [try T] は[T]と同様ですが、[T]が失敗するとき
    [try T] は(失敗せずに)何もしない点が違います。 *)

(* ####################################################### *)
(* *** The [;] Tactical *)
(** *** [;]タクティカル *)

(* Another very basic tactical is written [;].  If [T], [T1], ...,
    [Tn] are tactics, then
[[
      T; [T1 | T2 | ... | Tn]
]]
   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   In the special case where all of the [Ti]'s are the same tactic
   [T'], we can just write [T;T'] instead of:
[[
      T; [T' | T' | ... | T']
]]
   That is, if [T] and [T'] are tactics, then [T;T'] is a tactic that
   first performs [T] and then performs [T'] on _each subgoal_
   generated by [T].  This is the form of [;] that is used most often
   in practice. *)
(** 別の非常に基本的なタクティカルは[;]と書かれます。
    [T], [T1], ..., [Tn] がタクティックのとき、
[[
      T; [T1 | T2 | ... | Tn]
]]
   はタクティックで、最初に[T]を行ない、
   [T]によって生成された最初のサブゴールに[T1]を行ない、
   二番目のサブゴールに[T2]を行ない、... という処理をします。

   すべての[Ti]が同じタクティック[T']であるという特別な場合、
[[
      T; [T' | T' | ... | T']
]]
   と書く代わりに [T;T'] と書くだけで済ますことができます。
   つまり、[T]と[T']がタクティックのとき、
   [T;T'] はタクティックで、最初に[T]を行ない、
   [T]が生成したそれぞれのサブゴールに[T']を行ないます。
   これが[;]の実際に一番よく使われる形です。*)

(* For example, consider the following trivial lemma: *)
(** 例えば、次の簡単な補題を考えます: *)

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
    (* ... which are discharged similarly *)
Qed.

(* We can simplify the proof above using the [;] tactical. *)
(** 上の証明を[;]タクティカルを使って簡単化できます。 *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  (* Apply [destruct] to the current goal *)
  destruct n;
  (* then apply [simpl] to each resulting subgoal *)
  simpl;
  (* then apply [reflexivity] to each resulting subgoal *)
  reflexivity.
Qed.

(* Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)
(** [try]と[;]の両方を使うと、
    ちょっと前に悩まされた証明の繰り返しを取り除くことができます。 *)

Theorem optimize_0plus_sound': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
  Case "ANum". reflexivity.
  Case "APlus".
    destruct e1;
      (* Most cases follow directly by the IH *)
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    (* The interesting case, on which the above fails, is
       when [e1 = ANum n]. In this case, we have to destruct [n]
       (to see whether the optimization applies) and rewrite
       with the induction hypothesis. *)
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity.   Qed.

(* In practice, Coq experts often use [try] with a tactic like
    [induction] to take care of many similar "straightforward" cases
    all at once.  Naturally, this practice has an analog in informal
    proofs. *)
(** 実際的にはCoqの専門家は、[try]を[induction]のようなタクティックと一緒に使うことで、
    多くの似たような「簡単な」場合を一度に処理します。
    これは自然に非形式的な証明に対応します。*)
(* Here is an informal proof of this theorem that
    matches the structure of the formal one:

    _Theorem_: For all arithmetic expressions [e],
[[
       aeval (optimize_0plus e) = aeval e.
]]
    _Proof_: By induction on [e].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      - Suppose [e = ANum n] for some [n].  We must show
[[
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
]]
        This is immediate from the definition of [optimize_0plus].

      - Suppose [e = APlus e1 e2] for some [e1] and [e2].  We
        must show
[[
          aeval (optimize_0plus (APlus e1 e2))
        = aeval (APlus e1 e2).
]]
        Consider the possible forms of [e1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [e1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [e1 = ANum n] for some [n].
        If [n = ANum 0], then
[[
          optimize_0plus (APlus e1 e2) = optimize_0plus e2
]]
        and the IH for [e2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)
(** この定理の形式的な証明の構造にマッチする非形式的な証明は次の通りです:

    「定理」: すべての算術式[e]について
[[
       aeval (optimize_0plus e) = aeval e.
]]
    「証明」: [e]についての帰納法を使う。
    [AMinus]と[AMult]の場合は帰納仮定から直接得られる。
    残るのは以下の場合である:

      - ある[n]について [e = ANum n] とする。示すべきことは次の通りである:
[[
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
]]
        これは[optimize_0plus]の定義からすぐに得られる。

      - ある[e1]と[e2]について [e = APlus e1 e2] とする。
        示すべきことは次の通りである:
[[
          aeval (optimize_0plus (APlus e1 e2))
        = aeval (APlus e1 e2).
]]
        [e1]のとり得る形を考える。そのほとんどの場合、
        [optimize_0plus]は部分式について単に自分自身を再帰的に呼び出し、
        [e1]と同じ形の新しい式を再構成する。
        これらの場合、結果は帰納仮定からすぐに得られる。

        興味深い場合は、ある[n]について [e1 = ANum n] であるときである。
        このとき [n = ANum 0] ならば次が成立する:
[[
          optimize_0plus (APlus e1 e2) = optimize_0plus e2
]]
        そして[e2]についての帰納仮定がまさに求めるものである。
        一方、ある[n']について [n = S n'] ならば、
        [optimize_0plus]はやはり自分自身を再帰的に呼び出し、
        結果は帰納仮定から得られる。 [] *)

(* This proof can still be improved: the first case (for [e = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)
(** この証明はさらに改良できます。最初の場合([e = ANum n] のとき)はかなり自明です。
    帰納仮定からすぐに得られると言ったものより自明でしょう。
    それなのに完全に記述しています。
    これを消して、単に最初に「ほとんどの場合、すぐに、あるいは帰納仮定から直接得られる。
    興味深いのは[APlus]の場合だけである...」
    と言った方がより良く、より明快でしょう。
    同じ改良を形式的な証明にも行うことができます。以下のようになります: *)

Theorem optimize_0plus_sound'': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when e = APlus e1 e2. *)
  Case "APlus".
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1;
                      rewrite IHe2; reflexivity).
    SCase "e1 = ANum n". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.

(* ####################################################### *)
(* ** Defining New Tactic Notations *)
(** ** 新しいタクティック記法を定義する *)

(* Coq also provides several ways of "programming" tactic scripts.

      - The [Tactic Notation] command gives a handy way to define
        "shorthand tactics" that, when invoked, apply several tactics
        at the same time.

      - For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - There is also an OCaml API that can be used to build new
        tactics that access Coq's internal structures at a lower
        level, but this is seldom worth the trouble for ordinary Coq
        users.

The [Tactic Notation] mechanism is the easiest to come to grips with,
and it offers plenty of power for many purposes.  Here's an example.
*)
(** Coqはまた、タクティックスクリプトを「プログラミングする」いろいろな方法も提供します。

      - [Tactic Notation] コマンドは、「略記法タクティック」("shorthand tactics")
        を定義する簡単な方法を提供します。
       「略記法タクティック」は、呼ばれると、いろいろなタクティックを一度に適用します。

      - より洗練されたプログラミングのために、
        Coqは[Ltac]と呼ばれる小さなビルトインのプログラミング言語と、
        証明の状態を調べたり変更したりするための[Ltac]のプリミティブを提供します。
        その詳細はここで説明するにはちょっと複雑過ぎます
        (しかも、[Ltac]がCoqの設計の一番美しくない部分だというのは共通見解です!)。
        しかし、詳細はリファレンスマニュアルにありますし、
        Coqの標準ライブラリには、読者が参考にできる[Ltac]の定義のたくさんの例があります。

      - Coqの内部構造のより深いレベルにアクセスする新しいタクティックを作ることができる
        OCaml API も存在します。しかしこれは、普通のCoqユーザにとっては、
        苦労が報われることはほとんどありません。

[Tactic Notation] 機構は取り組むのに一番簡単で、多くの目的に十分なパワーを発揮します。
例を挙げます。
*)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(* This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)
(** これは1つのタクティック[c]を引数としてとる[simpl_and_try]
    という新しいタクティカルを定義しています。
    そして、タクティック [simpl; try c] と同値なものとして定義されます。
    例えば、証明内で"[simpl_and_try reflexivity.]"と書くことは
    "[simpl; try reflexivity.]"と書くことと同じでしょう。 *)

(* The next subsection gives a more sophisticated use of this
    feature... *)
(** 次のサブセクションでは、この機構のより洗練された使い方を見ます... *)

(* ####################################################### *)
(* *** Bulletproofing Case Analyses *)
(** *** 場合分けを万全にする *)

(* Being able to deal with most of the cases of an [induction] or
    [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice little
    trick that smoothly achieves this. *)
(** [induction]や[destruct]で、ほとんどの場合を一度に扱えるのはとても便利ですが、
    またちょっと混乱もします。よく起こる問題は、
    このスタイルで記述された証明をメンテナンスすることが難しいということです。
    例えば、後で、[aexp]の定義を拡張して、
    やはり特別な引数をとるコンストラクタを追加したとします。
    このとき上述の証明は成立しなくなっているでしょう。
    なぜなら、
    Coqは[APlus]についてのサブゴールの前にこのコンストラクタに対応するサブゴールを生成し、
    その結果、[APlus]の場合に取りかかる時には、
    Coqは実際にはまったく別のコンストラクタを待っていることになるからです。
    ここで欲しいのは、「この場所で[AFoo]の場合を期待していましたが、
    証明スクリプトは[APlus]について話しています。」という賢いエラーメッセージです。
    以下は、これを難なく可能にするちょっとしたトリックです。 *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(* ([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)
(** ([Case_aux]は[Case]、[SCase]、[SSCase]等の共通機能を実装します。
    例えば、[Case "foo"]は [Case_aux Case "foo"] と定義されます。) *)

(* For example, if [e] is a variable of type [aexp], then doing
[[
      aexp_cases (induction e) Case
]]
    will perform an induction on [e] (the same as if we had just typed
    [induction e]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    optimize_0plus_sound, using [aexp_cases]: *)
(** 例えば、[e]が型[aexp]の変数のとき、
[[
      aexp_cases (induction e) Case
]]
    と書くと[e]についての帰納法を実行し(単に [induction e] と書いたのと同じです)、
    そして、「その上に」、[induction]によって生成されたそれぞれのサブゴールに[Case]
    タグを付加します。このタグは、そのサブゴールがどのコンストラクタから来たかのラベルです。
    例えば、[aexp_cases]を使った、[optimize_0plus_sound]のさらに別証です: *)

Theorem optimize_0plus_sound''': forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  aexp_cases (induction e) Case;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.

  (* At this point, there is already an ["APlus"] case name in the
     context.  The [Case "APlus"] here in the proof text has the
     effect of a sanity check: if the "Case" string in the context is
     anything _other_ than ["APlus"] (for example, because we added a
     clause to the definition of [aexp] and forgot to change the
     proof) we'll get a helpful error at this point telling us that
     this is now the wrong case. *)
  Case "APlus".
    aexp_cases (destruct e1) SCase;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHe2; reflexivity.  Qed.

(* **** Exercise: 3 stars (optimize_0plus_b) *)
(** **** 練習問題: ★★★ (optimize_0plus_b) *)
(* Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)
(** [optimize_0plus]の変換が[aexp]の値を変えないことから、
    [bexp]の値を変えずに、[bexp]に現れる[aexp]をすべて変換するために
    [optimize_0plus]が適用できるべきでしょう。
    [bexp]についてこの変換をする関数を記述しなさい。そして、
    それが健全であることを証明しなさい。
    ここまで見てきたタクティカルを使って証明を可能な限りエレガントにしなさい。*)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 4 stars, optional (optimizer) *)
(** **** 練習問題: ★★★★, optional (optimizer) *)
(* _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

(* FILL IN HERE *)
*)
(** 設計練習: 定義した[optimize_0plus]関数で実装された最適化は、
    算術式やブール式に対して考えられるいろいろな最適化の単なる1つに過ぎません。
    より洗練された最適化関数を記述し、その正しさを証明しなさい。

(* FILL IN HERE *)
*)
(** [] *)

(* ####################################################### *)
(* ** The [omega] Tactic *)
(** ** [omega]タクティック *)

(* The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)
(** [omega]タクティックは「プレスバーガー算術」
    (_Presburger arithmetic_、「プレスブルガー算術」とも)
    と呼ばれる一階述語論理のサブセットの決定手続き(decision procedure)を実装します。
    William Pugh が1992年に発明したOmegaアルゴリズムに基いています。

    ゴールが以下の要素から構成された全称限量された論理式とします。以下の要素とは:

      - 数値定数、加算([+]と[S])、減算([-]と[pred])、
        定数の積算(これがプレスバーガー算術である条件です)、

      - 等式([=]と[<>])および不等式([<=])、

      - 論理演算子[/\], [\/], [~], [->]

    です。このとき、[omega]を呼ぶと、ゴールを解くか、
    そのゴールが偽であると告げるか、いずれかになります。 *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(* Andrew Appel calls this the "Santa Claus tactic." *)
(** Andrew Appel は[omega]を「サンタクロース・タクティック」と呼んでいます。 *)

(* ####################################################### *)
(* ** A Few More Handy Tactics *)
(** ** 便利なタクティックをさらにいくつか *)

(* Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is equivalent to [False].  If one is found, solve
       the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see many examples of these in the proofs below. *)
(** 最後に、役に立ちそうないろいろなタクティックをいくつか紹介します。

     - [clear H]: 仮定[H]をコンテキストから消去します。

     - [subst x]: コンテキストから仮定 [x = e] または [e = x] を発見し、
       [x]をコンテキストおよび現在のゴールのすべての場所で[e]に置き換え、
       この仮定を消去します。

     - [subst]: [x = e] および [e = x] の形のすべての仮定を置換します。

     - [rename... into...]: 証明コンテキストの仮定の名前を変更します。
       例えば、コンテキストが[x]という名前の変数を含んでいるとき、
       [rename x into y] は、すべての[x]の出現を[y]に変えます。

     - [assumption]: ゴールにちょうどマッチする仮定[H]をコンテキストから探そうとします。
       発見されたときは [apply H] と同様に振る舞います。

     - [contradiction]: [False]と同値の仮定[H]をコンテキストから探そうとします。
       発見されたときはゴールを解きます。

     - [constructor]: 現在のゴールを解くのに使えるコンストラクタ[c]を
       (現在の環境の[Inductive]による定義から)探そうとします。
       発見されたときは [apply c] と同様に振る舞います。

    以降の証明でこれらのたくさんの例を見るでしょう。 *)

(* ####################################################### *)
(* * Evaluation as a Relation *)
(** * 関係としての評価 *)

(* We have presented [aeval] and [beval] as functions defined by
    [Fixpoints]. An alternative way to think about evaluation is as a
    _relation_ between expressions and their values.

    This leads naturally to Coq [Inductive] definitions like the
    following one for arithmetic expressions... *)
(** [aeval]と[beval]を[Fixpoints]によって定義された関数として示しました。
    評価について考える別の方法は、それを式と値との間の関係(_relation_)と見ることです。

    この考えに立つと、
    算術式についてCoqの[Inductive]による以下の定義が自然に出てきます... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(* As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    || n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ascii
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double
    vertical bar as the closest approximation in ascii .v files.)  *)
(** 関係についてよく行うように、[aevalR]の中置記法を定義するのが便利です。
    算術式[e]が値[n]に評価されることを [e || n] と書きます。
    (この記法は煩わしいascii記号の限界の1つです。評価関係の標準記法は二重の下向き矢印です。
    HTML版ではそのようにタイプセットしますが、ascii の
    .v ファイルでは可能な近似として縦棒二本を使います。) *)

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

(* In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)
(** 実際は、Coqでは[aevalR]自身の定義中でこの記法を使うことができます。
    これにより、[e || n] の形の主張を含む証明で、[aevalR e n] 
    という形の定義に戻らなければならない状況にならずに済みます。

    このためには、最初に記法を「予約」し、
    それから定義と、記法が何を意味するかの宣言とを一緒に行います。*)

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

(* It is straightforward to prove that the relational and functional
    definitions of evaluation agree on all possible arithmetic
    expressions... *)
(** 評価の、関係による定義と関数による定義が、
    すべての算術式について一致することを証明するのは簡単です... *)

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

(* A shorter proof making more aggressive use of tacticals: *)
(** タクティカルをより積極的に使ったより短い証明です: *)

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* **** Exercise: 2 stars, optional (bevalR) *)
(** **** 練習問題: ★★, optional (bevalR) *)
(* Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)
(** 関係[bevalR]を[aevalR]と同じスタイルで記述し、
    それが[beval]と同値であることを証明しなさい。 *)

(*
Inductive bevalR:
(* FILL IN HERE *)
(** [] *)
*)

(* For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations; in particular,
    we can more readily do induction over them.  On the other hand, in
    some sense function definitions carry more information, because
    functions are necessarily deterministic and defined on all
    arguments; for a relation we have to show these properties
    explicitly if we need them.

    However, there are circumstances where relational definitions of
    evaluation are greatly preferable to functional ones, as we'll see
    shortly. *)
(** 算術式とブール式の評価の定義について、関数を使うか関係を使うかはほとんど趣味の問題です。
    一般に、Coqは関係を扱う方がいくらかサポートが厚いです。
    特に帰納法についてはそうです。一方、
    ある意味で関数による定義の方がより多くの情報を持っています。
    なぜなら、関数は決定的でなければならず、
    またすべての引数について定義されていなければなりません。
    関数については、必要ならばこれらの性質を明示的に示さなければなりません。

    しかしながら、評価の定義として、
    関係による定義が関数による定義よりはるかに望ましい状況があります。
    以下で簡単に見ます。 *)

(* ####################################################### *)
(* ** Inference Rule Notation *)
(** ** 推論規則記法 *)

(* In informal discussions, it is convenient write the rules for
    [aevalR] and similar relations in a more readable "graphical" form
    called _inference rules_, where the premises above the line allow
    you to derive the conclusion below the line.  For example, the
    constructor [E_APlus]...
[[
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
]]
    ...would be written like this as an inference rule:
[[[
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
]]]
    Formally, there is nothing very deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line and the line itself as [->].
    All the variables mentioned in the rule ([e1], [n1], etc.) are
    implicitly bound by universal quantifiers at the beginning.  The
    whole collection of rules is understood as being wrapped in an
    [Inductive] declaration (this is either left completely implicit
    or else indicated informally by saying something like "Let
    [aevalR] be the smallest relation closed under the following
    rules...").

    For example, [||] is the smallest relation closed under these
    rules:
[[[
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
]]]
*)
(** 非形式的な議論には、[aevalR]や似たような関係についての規則を、
    推論規則(_inference rules_)と呼ばれる、
    より読みやすいグラフィカルな形で書くのが便利です。
    推論規則は、横線の上の前提から、横線の下の結論を導出できることを述べます。
    例えば、コンストラクタ[E_APlus]...
[[
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
]]
    ...は推論規則として次のように書けるでしょう:
[[
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
]]
    形式的には、推論規則について何も深いものはありません。単なる含意です。
    右に書かれた規則名はコンストラクタで、
    横線より上の前提の間の各改行と横線自体は[->]と読むことができます。
    規則で言及されるすべての変数([e1]、[n1]等)
    は暗黙のうちに冒頭で全称限量子に束縛されています。
    規則の集合全体は[Inductive]宣言で囲われていると理解されます
    (これは完全に暗黙のまま置かれるか、非形式的に
    「[aevalR]は以下の規則について閉じた最小の関係とします...」
    などと述べられるかします)。

    例えば、[||]は以下の規則について閉じた最小の関係です:
[[
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
]]
*)

End AExp.

(* ####################################################### *)
(* * Expressions With Variables *)
(** * 変数を持つ式 *)

(* Now let's turn our attention back to defining Imp.  The next thing
    we need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)
(** さて、Impの定義に戻りましょう。次にしなければならないことは、
    算術式とブール式に変数を拡張することです。
    話を単純にするため、すべての変数はグローバルで、数値だけを持つとしましょう。 *)

(* ##################################################### *)
(* ** Identifiers *)
(** ** 識別子 *)

(* To begin, we'll need to formalize _identifiers_, such as program
    variables.  We could use strings for this, or (in a real compiler)
    some kind of fancier structures like pointers into a symbol table.
    But for simplicity let's just use natural numbers as identifiers.

    (We hide this section in a module because these definitions are
    actually in [SfLib.v], but we want to repeat them here so that we
    can explain them.) *)
(** 始めに、プログラム変数などの識別子(_identifiers_)を形式化しなければなりません。
    このために文字列を使うこともできるでしょうし、(実際のコンパイラでは)
    シンボルテーブルへのポインタのようなある種の特別な構造を使うこともできるでしょう。
    しかし、簡単にするため、識別子に単に自然数を使います。

    (このセクションをモジュールに隠します。それは、これらの定義が実際には[SfLib_J.v]
    にあるからです。しかし説明のためにここで繰り返します。) *)

Module Id.

(* We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers. *)
(** 新しいデータタイプ[Id]を定義して、識別子と数値を混乱しないようにします。 *)

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

(* Now, having "wrapped" numbers as identifiers in this way, it
    is convenient to recapitulate a few properties of numbers as
    analogous properties of identifiers, so that we can work with
    identifiers in definitions and proofs abstractly, without
    unwrapping them to expose the underlying numbers.  Since all we
    need to know about identifiers is whether they are the same or
    different, just a few basic facts are all we need. *)
(** さて、この方法で「覆った」数値を識別子としたので、
    数値のいくつかの性質を、対応する識別子の性質として繰り返しておくのが便利です。
    そうすると、定義や証明の中の識別子を、
    覆いを開いて中の数値を晒すことなく抽象的に扱うことができます。
    識別子について知らなければならないことは、識別子同士が同じか違うかだけなので、
    本当に2、3のことだけが必要です。 *)

Theorem beq_id_refl : forall X,
  true = beq_id X X.
Proof.
  intros. destruct X.
  apply beq_nat_refl.  Qed.

(* **** Exercise: 1 star, optional (beq_id_eq) *)
(** **** 練習問題: ★, optional (beq_id_eq) *)
(* For this and the following exercises, do not use induction, but
    rather apply similar results already proved for natural numbers.
    Some of the tactics mentioned above may prove useful. *)
(** この問題とそれに続く練習問題では、帰納法を使わずに、
    既に証明した自然数の同様の結果を適用しなさい。
    上述したいくつかのタクティックが使えるかもしれません。 *)

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (beq_id_false_not_eq) *)
(** **** 練習問題: ★, optional (beq_id_false_not_eq) *)
Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (not_eq_beq_id_false) *)
(** **** 練習問題: ★, optional (not_eq_beq_id_false) *)
Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star, optional (beq_id_sym) *)
(** **** 練習問題: ★, optional (beq_id_sym) *)
Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Id.

(* ####################################################### *)
(* ** States *)
(** ** 状態 *)

(* A _state_ represents the current values of all the variables at
    some point in the execution of a program. *)
(** 状態(_state_)はプログラムの実行のある時点のすべての変数の現在値を表します。 *)
(* For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going tomention a finite number of them. *)
(** 簡単にするため(部分関数を扱うのを避けるため)、
    どのようなプログラムも有限個の変数しか使わないにもかかわらず、
    状態はすべての変数について値を定義しているものとします。 *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

(* We'll need a few simple properties of [update]. *)
(** [update]についての単純な性質が必要です。 *)

(* **** Exercise: 2 stars, optional (update_eq) *)
(** **** 練習問題: ★★, optional (update_eq) *)
Theorem update_eq : forall n X st,
  (update st X n) X = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (update_neq) *)
(** **** 練習問題: ★★, optional (update_neq) *)
Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (update_example) *)
(** **** 練習問題: ★★, optional (update_example) *)
(* Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)
(** タクティックを使って遊び始める前に、
    定理が言っていることを正確に理解していることを確認しなさい! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars (update_shadow) *)
(** **** 練習問題: ★★ (update_shadow) *)
Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (update_same) *)
(** **** 練習問題: ★★, optional (update_same) *)
Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (update_permute) *)
(** **** 練習問題: ★★, optional (update_permute) *)
Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(* ** Syntax  *)
(** ** 構文  *)

(* We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)
(** 前に定義した算術式に、単にもう1つコンストラクタを追加することで変数を追加できます: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(* Shorthands for variables: *)
(** 変数の略記法: *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(* (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in this part of
    the course, this overloading should not cause confusion.) *)
(** (プログラム変数のこの慣習([X], [Y], [Z])は、
    型に大文字の記号を使うという以前の使用法と衝突します。
    コースのこの部分では多相性を多用はしないので、このことが混乱を招くことはないはずです。) *)

(* The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)
(** [bexp]の定義は前と同じです(ただし新しい[aexp]を使います): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(* ** Evaluation  *)
(** ** 評価  *)

(* The arith and boolean evaluators are extended to handle
    variables in the obvious way: *)
(** 算術とブールの評価器は、自明な方法で変数を扱うように拡張されます: *)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X                                        (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* ####################################################### *)
(* * Commands *)
(** * コマンド *)

(*  Now we are ready define the syntax and behavior of Imp
    _commands_ (or _statements_). *)
(** さて、Imp コマンド (または主張) の構文と挙動を定義する準備が出来ました *)

(* ################################################### *)
(*  ** Syntax *)
(** ** 構文 *)

(*  Informally, commands are described by the following BNF
    grammar:
[[
     com ::= 'SKIP'
           | X '::=' aexp
           | com ';' com
           | 'WHILE' bexp 'DO' com 'END'
           | 'IFB' bexp 'THEN' com 'ELSE' com 'FI'
]]
    For example, here's the factorial function in Imp.
[[
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
]]
   When this command terminates, the variable [Y] will contain the
   factorial of the variable [X].
*)
(** 非形式的には、コマンドは以下の BNF で表現されます。
    構文:
[[
     com ::= 'SKIP'
           | X '::=' aexp
           | com ';' com
           | 'WHILE' bexp 'DO' com 'END'
           | 'IFB' bexp 'THEN' com 'ELSE' com 'FI'
]]
    例えば、Imp における階乗関数は以下のようになります。
[[
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
]]
   このコマンドが終わったとき、変数 [Y] は変数 [X] の階乗の値を持つでしょう。
*)

(*  Here is the formal definition of the syntax of commands: *)
(** 以下に、コマンドの構文の形式的な定義を示します。 *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

(*  As usual, we can use a few [Notation] declarations to make things
    more readable.  However, we need to be a bit careful to avoid
    conflicts with Coq's built-in notations, so we'll keep this
    light -- in particular, we won't introduce any notations for
    [aexps] and [bexps] to avoid confusion with the numerical and
    boolean operators we've already defined.  (We use the keyword
    [IFB] for conditionals instead of the usual [IF] for similar
    reasons.) *)
(** いつものとおり、より読みやすいよう、いくつかの [Notation] 宣言が使えます。
    しかし、Coq の組み込みの表記と衝突しないよう、少し気をつける必要があります 
    (手軽さを維持しつつ！)。
    特に、[aexp] と [bexp] については、
    すでに定義した数値演算子やブール演算子との混同を避けるために、
    新しい表記は導入しません。
    (同様の理由により、条件文に対しては通常使われる [IF] の代わりに 
    [IFB] というキーワードを使います。) *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

(*  For example, here is the factorial function again, written as a
    formal definition to Coq: *)
(** 例えば先の階乗関数を Coq での形式的な定義として記述し直すと、
    以下のようになります。*)

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* ####################################################### *)
(*  ** Examples *)
(** ** 例 *)

(*  Here are some more examples... *)
(** 以下に、さらなる例を挙げます。 *)

(*  Assignment: *)
(** 割り当て: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

(*  Loops: *)
(** ループ: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

(*  An infinite loop: *)
(** 無限ループ: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(*  Factorial again (broken up into smaller pieces this time, for
    convenience when we come back to proving things about it
    later).  *)
(** 階乗関数再び (あとで戻って証明するとき便利なように、
    細かい部品に分割してあります)。 *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(* ################################################################ *)
(*  * Evaluation *)
(** * 評価 *)

(* Next we need to define what it means to evaluate an Imp command.
    [WHILE] loops actually make this a bit tricky... *)
(** 次に、Imp のコマンドの実行が何を意味するかを定義する必要があります。
    [WHILE] ループは、これを少々扱いにくいものにしています ... *)

(* #################################### *)
(*  ** Evaluation Function *)
(** ** 評価関数 *)

(*  Here's a first try at an evaluation function for commands,
    omitting [WHILE]. *)
(** 以下は [WHILE] 以外のコマンドの評価関数を得ようとした、最初の試みです。 *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | l ::= a1 =>
        update st l (aeval st a1)
    | c1 ; c2 =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | WHILE b1 DO c1 END =>
        st  (* bogus *)
  end.

(*  Second try, using an extra numeric argument as a "step index" to
    ensure that evaluation always terminates. *)
(** 次の試みでは、評価が常に停止することを保証するため、
    数の引数を追加して「ステップ指数」として用いています。*)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_state
  | S i' =>
    match c with
      | SKIP =>
          st
      | l ::= a1 =>
          update st l (aeval st a1)
      | c1 ; c2 =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(*  _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below. *)
(** 注: ここでの指数 [i] は「評価のステップ数」を数えるものだろうか？
    という点が気になります。しかしよく見ると、そうではないと分かります。
    例えば、直列実行に対する規則では、2 つの再帰呼び出しに同じ [i] が渡されています。
    [i] がどのように扱われているのかを正確に理解することは、
    以下で演習問題として与えられている [ceval__ceval_step] の証明で重要となるでしょう。 *)

(*  Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)
(** 3 つ目の試みでは、単なる [state] の代わりに [option state] を返すようにしています。
    こうすると、通常終了と異常終了を区別出来ます。*)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(*  We can improve the readability of this definition by introducing a
    bit of auxiliary notation to hide the "plumbing" involved in
    repeatedly matching against optional states. *)
(** オプション状態に対する場合分けに繰り返し含まれている「配管」を隠すための、
    補助的なちょっとした記法を導入すると、この定義の読みやすさは改善出来ます。*)

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

(*
Eval compute in
  (test_ceval empty_state
      (X ::= ANum 2;
       IFB BLe (AId X) (ANum 1)
         THEN Y ::= ANum 3
         ELSE Z ::= ANum 4
       FI)).
====>
   Some (2, 0, 4)
*)

(* **** Exercise: 2 stars, recommended (pup_to_n) *)
(** **** 練習問題: ★★, recommended (pup_to_n) *)
(*  Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)
(** [1] から [X] までの整数を変数 [Y] に足す (つまり [1 + 2 + ... + X]) 
    Imp プログラムを書きなさい。下に示したテストを満たすことを確認しなさい。 *)

Definition pup_to_n : com :=
  (* FILL IN HERE *) admit.

(*
Example pup_to_n_1 :
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
*)
(** [] *)

(*  **** Exercise: 2 stars, optional (peven) *)
(** **** 練習問題: ★★, optional (peven) *)
(*  Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)
(** [X] が偶数だったら [Z] に [0] を、そうでなければ [Z] に [1] をセットする 
    [While] プログラムを書きなさい。テストには [ceval_test] を使いなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* #################################### *)
(*  ** Evaluation as a Relation *)
(** ** 関係としての評価 *)

(*  Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] and [bevalR] above.

    This is an important change.  Besides freeing us from the
    silliness of passing around step indices all over the place, it
    gives us a lot more flexibility in the definition.  For example,
    if we added concurrency features to the language, we'd want the
    definition of evaluation to be non-deterministic -- i.e., not only
    would it not be total, it would not even be a partial function! *)
(** ここに改善策があります: [ceval] を関数ではなく関係 (_relation_) として定義しましょう。
    つまり、上の [aevalR] と [bevalR] と同様に [Type] ではなく [Prop] で定義しましょう。

    これは重要な変更です。
    ステップ指数をすべての場所で引き回す馬鹿馬鹿しさから解放してくれるのに加え、
    定義での柔軟性を与えてくれます。
    例えば、もし言語に並行性の要素を導入したら、評価の定義を非決定的に書きたくなるでしょう。
    つまり、その関数は全関数でないだけでなく、部分関数ですらないかも知れません！*)

(*  We'll use the notation [c / st || st'] for our [ceval] relation,
    that is [c / st || st'] means that executing program [c] in a
    starting state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']".
[[[
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   l := a1 / st || (update st l n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b1 DO c1 END / st || st

                          beval st b1 = true
                           c1 / st || st'
                  WHILE b1 DO c1 END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b1 DO c1 END / st || st''
]]]
*)
(** [ceavl] 関係に対する表記として [c / st || st'] を使います。
    正確に言うと、[c / st || st'] と書いたらプログラム [c] を初期状態 [st] で評価すると、
    その結果は最終状態 [st'] になる、ということを意味します。
    これは「[c] は状態 [st] を [st'] に持っていく」とも言えます。
[[
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   l := a1 / st || (update st l n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b1 DO c1 END / st || st

                          beval st b1 = true
                           c1 / st || st'
                  WHILE b1 DO c1 END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b1 DO c1 END / st || st''
]]
*)


(*  Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)
(** 以下に形式的な定義を挙げます。
    (上の推論規則とどのように対応するか、確認しておきましょう。) *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(*  The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)
(** 評価を関数ではなく関係として定義することのコストは、
    あるプログラムを実行した結果がとある状態になる、
    というのを Coq の計算機構にやってもらうだけではなく、
    その「証明」を構築する必要がある、ということです。*)

Example ceval_example1:
    (X ::= ANum 2;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(*  **** Exercise: 2 stars (ceval_example2) *)
(** **** 練習問題: ★★ (ceval_example2) *)
Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################ *)
(*  ** Equivalence of Relational and Step-Indexed Evaluation *)
(** ** 関係による評価とステップ指数を利用した評価の等価性 *)

(* As with arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation actually boil down
    to the same thing.  This section shows that this is the case.
    Make sure you understand the statements of the theorems and can
    follow the structure of the proofs. *)
(** 算術式とブール式で行ったように、2 つの評価の定義が本当に、
    結局のところ同じものになるのかを確認したくなるでしょう。
    この章では、それを確認します。定理の主張を理解して、
    証明の構造を追えることを確認しておいて下さい。*)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase;
           simpl in H; inversion H; subst; clear H.
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";".
        remember (ceval_step st c1 i') as r1. destruct r1.
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB".
        remember (beval st b) as r. destruct r.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". remember (beval st b) as r. destruct r.
        SSCase "r = true".
          remember (ceval_step st c i') as r1. destruct r1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1.
          apply E_WhileEnd.
          rewrite Heqr. subst. reflexivity.  Qed.

(*  **** Exercise: 4 stars (ceval_step__ceval_inf) *)
(** **** 練習問題: ★★★★ (ceval_step__ceval_inf) *)
(* Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof.

(* FILL IN HERE *)
[]
*)
(** いつものテンプレートにのっとって、
    [ceval_step__ceval] の形式的でない証明を書きましょう。
    (帰納的に定義された値の場合分けに対するテンプレートは、
    帰納法の仮定がないこと以外は帰納法と同じ見た目になるはずです。) 
    単に形式的な証明のステップを書き写すだけでなく、
    人間の読者に主要な考えが伝わるようにしなさい。

(* FILL IN HERE *)
[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";".
      simpl in Hceval. simpl.
      remember (ceval_step st c1 i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      remember (beval st b) as bval.
      destruct bval; apply (IHi1' i2') in Hceval; assumption.

    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      remember (ceval_step st c i1') as st1'o.
      destruct st1'o.
      SSCase "st1'o = Some".
        symmetry in Heqst1'o.
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval.  Qed.

(*  **** Exercise: 3 stars, recommended (ceval__ceval_step) *)
(** **** 練習問題: ★★★, recommended (ceval__ceval_step) *)
(*  Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)
(** 以下の証明を完成させなさい。何度か [ceval_step_more] が必要となり、
    さらに [<=] と [plus] に関するいくつかの基本的な事実が必要となるでしょう。*)

Theorem ceval__ceval_step: forall c st st',
      c / st || st' ->
      exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(*  ** Determinacy of Evaluation *)
(** ** 実行の決定性 *)

(*  Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on Fixpoint
    definitions) that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    actually a partial function?  That is, is it possible that,
    beginning from the same state [st], we could evaluate some command
    [c] in different ways to reach two different output states [st']
    and [st'']?

    In fact, this cannot happen: the evaluation relation [ceval] is a
    partial function.  Here's the proof: *)
(** 評価の定義を計算的なものから関係的なものに変更するのは、
    評価は全関数であるべきという (Fixpoint の定義における 
    Coq の制限によって課せられる) 不自然な要求から逃れさせてくれる良い変更です。
    しかしこれは、2 つ目の評価の定義は本当に部分関数なのか？という疑問ももたらします。
    つまり、同じ状態 [st] から始めて、あるコマンド [c] を違った方法で評価し、
    2 つの異なる出力状態 [st'] と [st''] に至るのは可能か？ということです。

   実際には、こうなることはありません。評価関係 [ceval] は部分関数です。
   以下に証明を挙げます: *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(*  Here's a slicker proof, using the fact that the relational and
    step-indexed definition of evaluation are the same. *)
(** 以下に、より巧みな証明を示します。
    これは関係による定義と指数を利用した定義の評価が同じである事実を利用しています。*)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1].
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity.
  omega. omega.  Qed.

(* ####################################################### *)
(*  * Reasoning About Programs *)
(** * プログラムの検証 *)

(*  We'll get much deeper into systematic techniques for reasoning
    about programs in Imp in the following chapters, but we can do
    quite a bit just working with the bare definitions.  This section
    explores some examples. *)
(** ここから Imp におけるプログラムの検証に対する系統だったテクニックに深く関わっていきます。
    しかし、その多くはむき出しの (もとの) 定義を扱うだけで出来ます。
    この章では、いくつかの例を探します。*)

(*  ** Basic Examples *)
(** ** 基本的な例 *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverting Heval essentially forces Coq to expand one
     step of the ceval computation - in this case revealing
     that st' must be st extended with the new value of X,
     since plus2 is an assignment *)
  inversion Heval. subst.
  apply update_eq.  Qed.

(*  **** Exercise: 3 stars, recommended (XtimesYinZ_spec) *)
(** **** 練習問題: ★★★, recommended (XtimesYinZ_spec) *)
(*  State and prove a specification of the XtimesYinZ Imp program. *)
(** XtimesYinZ の Imp プログラムの仕様を書いて証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 3 stars, recommended (loop_never_stops) *)
(** **** 練習問題: ★★★, recommended (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  (* Proceed by induction on the assumed derivation showing that
     loopdef terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(*  **** Exercise: 2 stars, optional (no_whilesR) *)
(** **** 練習問題: ★★, optional (no_whilesR) *)
(*  The [no_whiles] property yields [true] on just those programs that
    have no while loops.  Using [Inductive], write a property
    [no_whilesR] such that [no_whilesR c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)
(** 性質 [no_whiles] はプログラムが while ループを含まない場合 [true] を返します。
    Inductive を使って [c] が while ループのないプログラムのとき証明可能な性質 [no_whilesR] を書きなさい。
    さらに、それが [no_whiles] と等価であることを示しなさい。*)

Inductive no_whilesR: com -> Prop :=
 (* FILL IN HERE *)
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 4 stars, optional (no_whiles_terminating) *)
(** **** 練習問題: ★★★★, optional (no_whiles_terminating) *)
(*  Imp programs that don't involve while loops always terminate.
    State and prove a theorem that says this. *)
(** while ループを含まない Imp プログラムは必ず停止します。
    これを定理として記述し、証明しなさい。*)
(*  (Use either [no_whiles] or [no_whilesR], as you prefer.) *)
(** ([no_whiles] と [no_whilesR] のどちらでも好きなほうを使いなさい。) *)

(* FILL IN HERE *)
(** [] *)

(*  ** Proving a Program Correct (Optional) *)
(** ** プログラム正当性 (Optional) *)

(*  Recall the factorial program: *)
(** 階乗のプログラムを思い出しましょう: *)

Print fact_body. Print fact_loop. Print fact_com.

(*  Here is an alternative "mathematical" definition of the factorial
    function: *)
(** 階乗関数の別の「数学的な」定義を以下に示します: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(*  We would like to show that they agree -- if we start [fact_com] in
    a state where variable [X] contains some number [x], then it will
    terminate in a state where variable [Y] contains the factorial of
    [x].

    To show this, we rely on the critical idea of a _loop
    invariant_. *)
(** 変数 [X] がある数 [x] を持つ状態で [fact_com] を実行すると、
    変数 [Y] が [x] の階乗の値を持つ状態で停止する、ということを示したくなります。
    
    これを示すため、ループ不変式 (_loop invariant_) という重要な概念を使います。 *)

Definition fact_invariant (x:nat) (st:state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Theorem fact_body_preserves_invariant: forall st st' x,
     fact_invariant x st ->
     st Z <> 0 ->
     fact_body / st || st' ->
     fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as [| z'].
    apply ex_falso_quodlibet. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.  Qed.

Theorem fact_loop_preserves_invariant : forall st st' x,
     fact_invariant x st ->
     fact_loop / st || st' ->
     fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
              inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    (* trivial when the loop doesn't run... *)
    assumption.
  Case "E_WhileLoop".
    (* if the loop does run, we know that fact_body preserves
       fact_invariant -- we just need to assemble the pieces *)
    apply IHHce2.
      apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
      reflexivity.  Qed.

Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st || st' ->
     beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case;
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.  Qed.

(*  Patching it all together... *)
(** これらをすべてつなぎ合わせましょう... *)

Theorem fact_com_correct : forall st st' x,
     st X = x ->
     fact_com / st || st' ->
     st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. omega.
  (* ...so when the loop is done running, the invariant
     is maintained *)
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  (* Finally, if the loop terminated, then Z is 0; so Y must be
     factorial of X *)
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. omega.
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.

(*  One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the topic of the next chapter ([Hoare.v])! *)
(** この、状態をつっついて定義を展開するような全体のやり方を、何かより強力な補題や、
    より一貫性のある推論原理で改善できないのかと思う人もいるかもしれません。
    実は、それがまさに次の章([Hoare_J.v])の主題です! *)


(* **** Exercise: 4 stars, optional (subtract_slowly_spec) *)
(** **** 練習問題: ★★★★, optional (subtract_slowly_spec) *)
(** 上の [fact_com] の仕様、および以下の不変式をガイドとして、
    subtract_slowly の仕様を証明しなさい。 *)

Definition ss_invariant (x:nat) (z:nat) (st:state) :=
  minus (st Z) (st X) = minus z x.

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(*  * Additional Exercises *)
(** * 追加の練習問題 *)

(*  **** Exercise: 4 stars, optional (add_for_loop) *)
(** **** 練習問題: ★★★★, optional (add_for_loop) *)
(*  Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)
(** C 風の [for] ループをコマンドの言語に追加し、[ceval] の定義を
   [for] ループの意味も与えるよう更新して、
   このファイルにあるすべての証明が Coq に通るよう、
   必要なところへ [for] ループに対する場合分けを追加しなさい。

    [for] ループは (a) 初めに実行される主張、
    (b) 各繰り返しで実行される、ループを続けてよいか決定するテスト、
    (c) 各ループの繰り返しの最後に実行される主張、および
    (d) ループの本体を構成する主張によってパラメタ化されていなければなりません。
    ([for] ループに対する具体的な表記の構成を気にする必要はありませんが、
    やりたければ自由にやって構いません。) *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 3 stars, optional (short_circuit) *)
(** **** 練習問題: ★★★, optional (short_circuit) *)
(*  Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)
(** 多くのモダンなプログラミング言語はブール演算子 [and] に対し、
    「省略した」実行を使っています。
    [BAnd b1 b2] を実行するには、まず [b1] を評価します。
    それが [false] に評価されるならば、[b2] の評価はせず、
    すぐに [BAnd] 式全体の結果を [false] に評価します。
    そうでなければ、[BAnd] 式の結果を決定するため、[b2] が評価されます。

    このように [BAnd] を省略して評価する、別のバージョンの [beval] を書き、
    それが [beavl] と等価であることを証明しなさい。 *)

(* FILL IN HERE *)

(* **** Exercise: 4 stars, recommended (stack_compiler) *)
(** **** 練習問題: ★★★★, recommended (stack_compiler) *)
(*  HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions, and to prove its
  correctness.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad X]: Load the identifier [X] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply.
*)
(** HP の電卓、Forth や Postscript などのプログラミング言語、
   および Java Virtual Machine などの抽象機械はすべて、スタックを使って算術式を評価します。
   例えば、
<<
   (2*3)+(3*(4-2))
>>
   という式は
<<
   2 3 * 3 4 2 - * +
>>
   と入力され、以下のように実行されるでしょう:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  この練習問題のタスクは、[eaxp] をスタック機械の命令列に変換する小さなコンパイラを書き、その正当性を証明することです。

  スタック言語の命令セットは、以下の命令から構成されます:
     - [SPush n]: 数 [n] をスタックにプッシュする。
     - [SLoad X]: ストアから識別子 [X] に対応する値を読み込み、スタックにプッシュする。
     - [SPlus]:   スタックの先頭の 2 つの数をポップし、それらを足して、
                  結果をスタックにプッシュする。
     - [SMinus]:  上と同様。ただし引く。
     - [SMult]:   上と同様。ただし掛ける。
*)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(*  Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense it is
    immaterial, since our compiler will never emit such a malformed
    program. However, when you do the correctness proof you may find
    some choices makes the proof easier than others. *)
(** スタック言語のプログラムを評価するための関数を書きなさい。
    入力として、状態、数のリストとして表現されたスタック
    (スタックの先頭要素はリストの先頭)、
    および命令のリストとして表現されたプログラムを受け取り、
    受け取ったプログラムの実行した後のスタックを返します。
    下にある例で、その関数のテストをしなさい。

    上の仕様では、スタックが 2 つ未満の要素しか含まずに [SPlus] や [SMinus]、
    [SMult] 命令に至った場合を明示していないままなことに注意しましょう。
    我々のコンパイラはそのような奇形のプログラムは生成しないので、
    これは重要でないという意味です。
    しかし正当性の証明をするときは、いくつかの選択のほうが証明をより簡単にすることに気づくかもしれません。*)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
(* FILL IN HERE *) admit.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute (update empty_state X 3) [3,4]
       [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
(* FILL IN HERE *) Admitted.

(*  Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)
(** 次に、[aexp] をスタック機械のプログラムにコンパイルする関数を書きなさい。
    このプログラムを実行する影響は、もとの式の値をスタックに積むことと同じでなければなりません。*)

Fixpoint s_compile (e : aexp) : list sinstr :=
(* FILL IN HERE *) admit.

(*
Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X, SPush 2, SLoad Y, SMult, SMinus].
Proof. reflexivity. Qed.
*)

(*  Finally, prove the following theorem, stating that the [compile]
    function behaves correctly.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis. *)
(** 最後に、[compile] 関数が正しく振る舞うことを述べている以下の定理を証明しなさい。
    まずは使える帰納法の仮定を得るため、より一般的な補題を述べる必要があるでしょう。*)

(* FILL IN HERE *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

