(** * Hoare_J: ホーア論理 *)
(* * Hoare: Hoare Logic *)

(* $Date: 2011-06-22 14:56:13 -0400 (Wed, 22 Jun 2011) $ *)

(* Alexandre Pilkiewicz suggests the following alternate type for the
   decorated WHILE construct:
     | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
   This leads to a simpler rule in the VC generator, which is much
   easier to explain:
     | DCWhile b P' c  => ((fun st => post c st /\ bassn b st) ~~> P')
                         /\ (P ~~> post c)  (* post c is the loop invariant *)
                         /\ verification_conditions P' c
   His full development (based on an old version of our formalized
   decorated programs, unfortunately), can be found in the file
   /underconstruction/PilkiewiczFormalizedDecorated.v *)
(* Alexandre Pilkiewicz が WHILE 構文を修飾するための型について、以下の別案を
   提案してくれた:
     | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
   これによって VC生成器の規則がよりシンプルなものになり、説明がはるかに簡単になる:
     | DCWhile b P' c  => ((fun st => post c st /\ bassn b st) ~~> P')
                         /\ (P ~~> post c)  (* post c is the loop invariant *)
                         /\ verification_conditions P' c
   彼の完全版(残念ながら、我々の修飾付きプログラムの古いバージョンをベースにしている)は
   以下のファイルにある。
   /underconstruction/PilkiewiczFormalizedDecorated.v *)
   
Require Export ImpList_J.

(* We've begun applying the mathematical tools developed in the
    first part of the course to studying the theory of a small
    programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than properties of particular programs in the language.
      These included:

        - determinacy of evaluation

        - equivalence of some different ways of writing down the
          definition

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the optional chapter
          [Equiv.v]).

      If we stopped here, we would still have something useful: a set
      of tools for defining and discussing programming languages and
      language features that are mathematically precise, flexible, and
      easy to work with, applied to a set of key properties.

      All of these properties are things that language designers,
      compiler writers, and users might care about knowing.  Indeed,
      many of them are so fundamental to our understanding of the
      programming languages we deal with that we might not consciously
      recognize them as "theorems."  But properties that seem
      intuitively obvious can sometimes be quite subtle -- or, in some
      cases, actually even wrong!

      We'll return to this theme later in the course when we discuss
      _types_ and _type soundness_.

    - We saw a couple of examples of _program verification_ -- using
      the precise definition of Imp to prove formally that certain
      particular programs (e.g., factorial and slow subtraction)
      satisfied particular specifications of their behavior. *)
(** コースの最初のパートで用意した数学的道具立てを、
    小さなプログラミング言語 Imp の理論の学習に適用し始めています。

    - Imp の抽象構文木(_abstract syntax trees_)の型を定義しました。
      また、操作的意味論(_operational semantics_)を与える
      評価関係(_evaluation relation_)(状態間の部分関数)も定義しました。
      
      定義した言語は小さいですが、C, C++, Java などの本格的な言語の主要な
      機能を持っています。その中には変更可能な状態や、いくつかのよく知られた制御構造も
      含まれます。

    - いくつものメタ理論的性質(_metatheoretic properties_)を証明しました。
      "メタ"というのは、言語で書かれた特定のプログラムの性質ではなく言語自体の性質という意味です。
      証明したものには、以下のものが含まれます:

        - 評価の決定性

        - 異なった書き方をした定義の同値性

        - プログラムのあるクラスの、停止性の保証

        - プログラムの動作の同値性([Equiv_J.v]のオプションの章において)

      もしここで止めたとしても、有用なものを持っていることになります。
      それは、プログラミング言語と言語の特性を定義し議論する、数学的に正確で、
      柔軟で、使いやすい、主要な性質に適合した道具立てです。

      これらの性質は、言語を設計する人、コンパイラを書く人、そしてユーザも知っておく
      べきものです。実際、その多くは我々が扱うプログラミング言語を理解する上で本当に
      基本的なことですので、"定理"と意識することはなかったかもしれません。
      しかし、直観的に明らかだと思っている性質はしばしばとても曖昧で、時には間違っている
      こともあります!

      この問題については、後に型(_types_)とその健全性(_type soundness_)を
      議論する際に再度出てきます。

    - プログラムの検証(_program verification_)の例を2つ行いました。
      Imp を厳密に定義し、ある特定のプログラム(つまり階乗計算と遅い引き算)が
      その動作についての特定の仕様を満たすことを形式的に証明するものでした。*)

(* In this chapter, we'll take this last idea further.  We'll
    develop a reasoning system called _Floyd-Hoare Logic_ -- commonly,
    if somewhat unfairly, shortened to just _Hoare Logic_ -- in which
    each of the syntactic constructs of Imp is equipped with a single,
    generic "proof rule" that can be used to reason about programs
    involving this construct.

    Hoare Logic originates in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a huge variety of tools that are now being
    used to specify and verify real software systems. *)
(** この章では、この最後の考え方をさらに進めます。
    一般にフロイド-ホーア論理(_Floyd-Hoare Logic_)、あるいは、やや不公平に
    省略してホーア論理(_Hoare Logic_)と呼ばれている推論システムを作ります。
    この推論システムの中では、Imp の各構文要素に対して1つの一般的な"証明規則"
    (proof rule)が与えられ、これによってその構文要素を含むプログラムについての
    推論ができるようになっています。

    ホーア論理の起源は1960年代です。そして今現在まで継続的にさかんに研究がされています。
    実際のソフトウェアシステムの仕様を定め検証するために使われている非常に多くのツールの、
    核となっています。*)


(* ####################################################### *)
(* * Hoare Logic *)
(** * ホーア 論理 *)

(* Hoare Logic offers two important things: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that these specifications are met --
    where by "compositional" we mean that the structure of proofs
    directly mirrors the structure of the programs that they are
    about. *)
(** ホーア論理は2つの重要なことがらを提供します。プログラムの仕様(_specification_)を
    自然に記述する方法と、その仕様が適合していることを証明する合成的証明法(_compositional
    proof technique_)です。ここでの"合成的"(compositional)という意味は、
    証明の構造が証明対象となるプログラムの構造を直接的に反映しているということです。*)

(* ####################################################### *)
(* ** Assertions *)
(** ** 表明 *)

(* If we're going to talk about specifications of programs, the first
    thing we'll want is a way of making _assertions_ about properties
    that hold at particular points in time -- i.e., properties that
    may or may not be true of a given state of the memory. *)
(** プログラムの仕様について話そうとするとき、最初に欲しくなるのは、ある特定の時点で成立している
    性質 -- つまり、与えられたメモリ状態で真になり得るか、なり得ないかの性質 -- についての
    表明(_assertions_)を作る方法です。*)

Definition Assertion := state -> Prop.

(* **** Exercise: 1 star (assertions) *)
(** **** 練習問題: ★ (assertions) *)
(* Paraphrase the following assertions in English.
[[
      fun st =>  asnat (st X) = 3
      fun st =>  asnat (st X) = x
      fun st =>  asnat (st X) <= asnat (st Y)
      fun st =>  asnat (st X) = 3 \/ asnat (st X) <= asnat (st Y)
      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x
                 /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
      fun st =>  True
      fun st =>  False
]]
[] *)
(** 以下の表明を日本語に直しなさい。
[[
      fun st =>  asnat (st X) = 3
      fun st =>  asnat (st X) = x
      fun st =>  asnat (st X) <= asnat (st Y)
      fun st =>  asnat (st X) = 3 \/ asnat (st X) <= asnat (st Y)
      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                 /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x)
      fun st =>  True
      fun st =>  False
]]
[] *)

(* This way of writing assertions is formally correct -- it
    precisely captures what we mean, and it is exactly what we will
    use in Coq proofs -- but it is a bit heavy to look at, for several
    reasons.  First, every single assertion that we ever write is
    going to begin with [fun st => ]; (2) this state [st] is the only
    one that we ever use to look up variables (we never need to talk
    about two different states at the same time); and (3) all the
    variable lookups in assertions are cluttered with [asnat] or
    [aslist] coercions.  When we are writing down assertions
    informally, we can make some simplifications: drop the initial
    [fun st =>], write just [X] instead of [st X], and elide [asnat]
    and [aslist]. *)
(** この方法で表明を書くことは、形式的に正しいのです。-- この方法は意図することを
    正確に捕えています。そしてこれがまさに Coq の証明で使う方法なのです。しかしこれは
    いくつかの理由から、若干ヘビーに見えます。最初に、すべての個々の表明は、[fun st=> ]
    から始まっています。(2)状態[st]は変数を参照するために使うただ1つのものです(2つの
    別々の状態を同時に考える必要はありません)。(3)表明で参照するすべての変数は
    [asnat]または[aslist]の強制型変換により取り散らかっています。
    (訳注：「最初に」「(2)」「(3)」は変な並びだが、原文がそうなっている
    ("First,","(2)","(3)")ためそう訳した。) 表明をインフォーマルに書くときには、
    いくらか簡単にします。最初の[fun st =>]は書かず、[st X]のかわりに単に[X]と書きます。
    また[asnat]と[aslist]は略します。*)
(* Informally, instead of writing
[[
      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x
                 /\ ~ ((S (asnat (st Z))) * (S (asnat (st Z))) <= x)
]]
    we'll write just
[[
         Z * Z <= x
      /\ ~((S Z) * (S Z) <= x).
]]
*)
(** インフォーマルには、次のように書くかわりに
[[
      fun st =>  (asnat (st Z)) * (asnat (st Z)) <= x 
                 /\ ~ ((S (asnat (st Z))) * (S (asnat (st Z))) <= x)
]]
    次のように書きます。
[[
         Z * Z <= x 
      /\ ~((S Z) * (S Z) <= x).
]]
*)

(* ####################################################### *)
(* ** Hoare Triples *)
(** ** ホーアの三つ組 *)

(* Next, we need a way of specifying -- making claims about -- the
    behavior of commands. *)
(** 次に、コマンドのふるまいの仕様を定める -- つまりコマンドのふるまい
    についての表明を作る -- 方法が必要です。*)

(* Since we've defined assertions as a way of making claims about the
    properties of states, and since the behavior of a command is to
    transform one state to another, a claim about a command takes the
    following form:

      - "If [c] is started in a state satisfying assertion [P], and if
        [c] eventually terminates, then the final state is guaranteed
        to satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c]; [Q] is the _postcondition_ of
    [c]. *)
(** 表明を、状態の性質について表明するものとして定義してきたことから、
    また、コマンドのふるまいは、状態を別の状態に変換するものであることから、
    コマンドについての表明は次の形をとります:

      - "もし [c] が表明 [P] を満たす状態から開始され、また、[c]が
        いつかは停止するならば、最終状態では、表明[Q]が成立することを保証する。"

    この表明は ホーアの三つ組(_Hoare Triple_)と呼ばれます。性質[P]は[c]の
    事前条件(_precondition_)と呼ばれます。[Q]は[c]の事後条件(_postcondition_)と
    呼ばれます。*)

(* (Traditionally, Hoare triples are written [{P} c {Q}], but single
    braces are already used for other things in Coq.)  *)
(** (伝統的に、ホーアの三つ組は [{P} c {Q}]と書かれます。しかし Coq では一重の中カッコは
    別の意味で既に使われています。) *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

(* Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
[[
       {{P}}  c  {{Q}}.
]]
*)
(** ホーアの三つ組を今後多用するので、簡潔な記法を用意すると便利です:
[[
       {{P}}  c  {{Q}}.
]]
*)

Notation "{{ P }}  c" :=          (hoare_triple P c (fun st => True)) (at level 90)
                                  : hoare_spec_scope.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level)
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

(* (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.  The first notation -- with missing postcondition -- will
    not actually be used here; it's just a placeholder for a notation
    that we'll want to define later, when we discuss decorated
    programs.) *)
(** この[hoare_spec_scope]アノテーションは、Coqにこの記法はグローバルではなく、
    特定のコンテキストで使うものであることを伝えるものです。[Open Scope]は
    このファイルがそのコンテキストであることを Coq に伝えます。最初の記法、
    -- 事前条件を持たないもの -- はここで実際に使うことはありません。
    これは単に後に定義する記法のための場所を用意したものです。後に修飾付きプログラムについて
    議論する際に使います。*)

(* **** Exercise: 1 star (triples) *)
(** **** 練習問題: ★ (triples) *)
(* Paraphrase the following Hoare triples in English.
[[
      {{True}} c {{X = 5}}

      {{X = x}} c {{X = x + 5)}}

      {{X <= Y}} c {{Y <= X}}

      {{True}} c {{False}}

      {{X = x}}
      c
      {{Y = real_fact x}}.

      {{True}}
      c
      {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}
]]
 *)
(** 以下の ホーア の三つ組を日本語に直しなさい。
[[
      {{True}} c {{X = 5}}

      {{X = x}} c {{X = x + 5)}}

      {{X <= Y}} c {{Y <= X}}

      {{True}} c {{False}}

      {{X = x}}
      c
      {{Y = real_fact x}}.

      {{True}}
      c
      {{(Z * Z) <= x /\ ~ (((S Z) * (S Z)) <= x)}}
]]
 *)
(** [] *)

(* **** Exercise: 1 star (valid_triples) *)
(** **** 練習問題: ★ (valid_triples) *)
(* Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?
[[
      {{True}} X ::= 5 {{X = 5}}

      {{X = 2}} X ::= X + 1 {{X = 3}}

      {{True}} X ::= 5; Y ::= 0 {{X = 5}}

      {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

      {{True}} SKIP {{False}}

      {{False}} SKIP {{True}}

      {{True}} WHILE True DO SKIP END {{False}}

      {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

      {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}
]]
*)
(** 以下の ホーアの三つ組のうち、正しい(_valid_)ものを選択しなさい。
    -- 正しいとは、[P],[c],[Q]の関係が真であるということです。
[[
      {{True}} X ::= 5 {{X = 5}}

      {{X = 2}} X ::= X + 1 {{X = 3}}

      {{True}} X ::= 5; Y ::= 0 {{X = 5}}

      {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}

      {{True}} SKIP {{False}}

      {{False}} SKIP {{True}}

      {{True}} WHILE True DO SKIP END {{False}}

      {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}

      {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}
]]
*)
(* (Note that we're using informal mathematical notations for
   expressions inside of commands, for readability.  We'll continue
   doing so throughout the chapter.) *)
(** (読みやすくするため、コマンド内の式について、非形式的な数学記法を
      使います。この章の最後までその方針をとります。) *)
(** [] *)

(* To get us warmed up, here are two simple facts about Hoare
    triples. *)
(** ウォーミングアップとして、ホーアの三つ組についての2つの事実をみてみ
    ます。*)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

(* ####################################################### *)
(* ** Weakest Preconditions *)
(** ** 最弱事前条件 *)

(* Some Hoare triples are more interesting than others.  For example,
[[
      {{ False }}  X ::= Y + 1  {{ X <= 5 }}
]]
    is _not_ very interesting: it is perfectly valid, but it tells us
    nothing useful.  Since the precondition isn't satisfied by any
    state, it doesn't describe any situations where we can use the
    command [X ::= Y + 1] to achieve the postcondition [X <= 5].

    By contrast,
[[
      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}
]]
    is useful: it tells us that, if we can somehow create a situation
    in which we know that [Y <= 4 /\ Z = 0], then running this command
    will produce a state satisfying the postcondition.  However, this
    triple is still not as useful as it could be, because the [Z = 0]
    clause in the precondition actually has nothing to do with the
    postcondition [X <= 5].  The _most_ useful triple (with the same
    command and postcondition) is this one:
[[
      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}
]]
    In other words, [Y <= 4] is the _weakest_ valid precondition of
    the command [X ::= Y + 1] for the postcondition [X <= 5]. *)
(** いくつかの ホーアの三つ組は、他のものより興味深いものです。例えば:
[[
      {{ False }}  X ::= Y + 1  {{ X <= 5 }}
]]
    はあまり興味深いものではありません。これは完全に正しいものです。しかし、
    何も有用なことを伝えてくれません。事前条件がどのような状態でも満たされないことから、
    コマンド [X ::= Y + 1] によって事後条件 [X <= 5] に至るどのような
    状況も記述していません。
 
    一方、
[[
      {{ Y <= 4 /\ Z = 0 }}  X ::= Y + 1 {{ X <= 5 }}
]]
    は有用です。これは、何らかの方法で[Y <= 4 /\ Z = 0]であるという状況を作りあげた後、
    このコマンドを実行すると事後条件を満たす状態になる、ということを伝えています。
    しかしながら、この三つ組はもう少し改良できます。なぜなら、事前条件の[Z = 0]という節は
    実際には事後条件[X <= 5]に何の影響も与えないからです。
    (このコマンドと事後条件のもとで)最も有効な三つ組は次のものです:
[[
      {{ Y <= 4 }}  X ::= Y + 1  {{ X <= 5 }}
]]
    言いかえると、[Y <= 4] は事後条件[X <= 5]に対してコマンド[X ::= Y + 1]の
    最弱の(_weakest_)正しい事前条件です。*)
(* In general, we say that "[P] is the weakest precondition of
    [c] for [Q]" if

    - [{{P}} c {{Q}}], and

    - whenever [P'] is an assertion such that [{{P'}} c {{Q}}], we
      have [P' st] implies [P st] for all states [st].  *)
(** 一般に、次の条件が成立するとき"[P]は[Q]に対する[c]の最弱事前条件である"と言います:
   
    - [{{P}} c {{Q}}], かつ

    - [P'] が [{{P'}} c {{Q}}] を満たす表明ならば, 
      すべての状態 [st] について、[P' st] ならば [P st] となる。  *)
   
(* That is, [P] is the weakest precondition of [c] for [Q]
    if (a) [P] _is_ a precondition for [Q] and [c], and (b) [P] is the
    _weakest_ (easiest to satisfy) assertion that guarantees [Q] after
    [c]. *)
(** つまり、[P]は[Q]に対する[c]の最弱事前条件であるとは、(a) [P] は [Q] と [c] の事前条件
    で、かつ、(b) [P]は[c]の後で[Q]を保証する最弱の(_weakest_)(もっとも簡単に充足できる)
    表明である、ということです。*)

(* **** Exercise: 1 star (wp) *)
(** **** 練習問題: ★ (wp) *)
(* What are the weakest preconditions of the following commands
   for the following postconditions?
[[
     {{ ? }}  SKIP  {{ X = 5 }}

     {{ ? }}  X ::= Y + Z {{ X = 5 }}

     {{ ? }}  X ::= Y  {{ X = Y }}

     {{ ? }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

     {{ ? }}
     X ::= 5
     {{ X = 0 }}

     {{ ? }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
]]
*)
(** 以下のコマンドの以下の事後条件に対する最弱事前条件を示しなさい。
[[
     {{ ? }}  SKIP  {{ X = 5 }}

     {{ ? }}  X ::= Y + Z {{ X = 5 }}

     {{ ? }}  X ::= Y  {{ X = Y }}

     {{ ? }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}

     {{ ? }}
     X ::= 5
     {{ X = 0 }}

     {{ ? }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
]]
*)
(** [] *)

(* ####################################################### *)
(* ** Proof Rules *)
(** ** 証明規則 *)

(* The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of Hoare triples.  That is, the
    structure of a program's correctness proof should mirror the
    structure of the program itself.  To this end, in the sections
    below, we'll introduce one rule for reasoning about each of the
    different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules that are useful for gluing things
    together. *)
(** ホーア論理のゴールは、ホーアの三つ組の正しさを証明する"合成的"手法を提供することです。
    つまり、プログラムの正しさの証明の構造は、プログラムの構造をそのまま反映したものになる
    ということです。このゴールのために、以降の節では、Impのコマンドのいろいろな構文要素の
    それぞれ対して、その構文要素について推論するための規則を1つずつ導入します。代入文に1つ、
    合成文に1つ、条件文に1つ、等です。それに加えて、複数のものを結合するために有用な
    2つの"構造的"規則を導入します。*)

(* ####################################################### *)
(* *** Assignment *)
(** *** 代入 *)

(* The rule for assignment is the most fundamental of the Hoare logic
    proof rules.  Here's how it works.

    Consider this (valid) Hoare triple:
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
]]
    In English: if we start out in a state where the value of [Y]
    is [1] and we assign [Y] to [X], then we'll finish in a
    state where [X] is [1].  That is, the property of being equal
    to [1] gets transferred from [Y] to [X].

    Similarly, in
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
]]
    the same property (being equal to one) gets transferred to
    [X] from the expression [Y + Z] on the right-hand side of
    the assignment.

    More generally, if [a] is _any_ arithmetic expression, then
[[
       {{ a = 1 }}  X ::= a {{ X = 1 }}
]]
    is a valid Hoare triple.

    Even more generally, [a] is _any_ arithmetic expression and [Q] is
    _any_ property of numbers, then
[[
       {{ Q(a) }}  X ::= a {{ Q(X) }}
]]
    is a valid Hoare triple.

    Rephrasing this a bit gives us the general Hoare rule for
    assignment:
[[
      {{ Q where a is substituted for X }}  X ::= a  {{ Q }}
]]
    For example, these are valid applications of the assignment
    rule:
[[
      {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}

      {{ 3 = 3 }}  X ::= 3  {{ X = 3 }}

      {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
*)
(** 代入文の規則は、ホーア論理の証明規則の中で最も基本的なものです。
    この規則は次のように働きます。

    次の(正しい)ホーアの三つ組を考えます。
[[
       {{ Y = 1 }}  X ::= Y  {{ X = 1 }}
]]
    日本語で言うと、[Y]の値が[1]である状態から始めて、[X]を[Y]に代入するならば、
    [X]が[1]である状態になる、ということです。つまり、[1]である、という性質が
    [X]から[Y]に移された、ということです。

    同様に、
[[
       {{ Y + Z = 1 }}  X ::= Y + Z  {{ X = 1 }}
]]
    においては、同じ性質(1であること)が代入の右辺の[Y+Z]から[X]に移動されています。

    より一般に、[a]が「任意の」算術式のとき、
[[
       {{ a = 1 }}  X ::= a {{ X = 1 }}
]]
    は正しいホーアの三つ組になります。

    さらに一般化して、[a]が「任意の」算術式、[Q]が数についての「任意の」性質のとき、
[[
       {{ Q(a) }}  X ::= a {{ Q(X) }}
]]
    は正しいホーアの三つ組です。

    これを若干言い換えると、代入に対する一般ホーア規則になります:
[[
      {{ Q において X を a で置換したもの }}  X ::= a  {{ Q }}
]]
    例えば、以下は、代入規則の正しい適用です:
[[
      {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}

      {{ 3 = 3 }}  X ::= 3  {{ X = 3 }}

      {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
*)

(* We could try to formalize the assignment rule directly in Coq by
    treating [Q] as a family of assertions indexed by arithmetic
    expressions -- something like this:
[[
      Theorem hoare_asgn_firsttry :
        forall (Q : aexp -> Assertion) V a,
        {{fun st => Q a st}} (V ::= a) {{fun st => Q (AId V) st}}.
]]
    But this formulation is not very nice, for two reasons.
    First, it is not quite true! (As a counterexample, consider
    a [Q] that inspects the _syntax_ of its argument, such as
[[
    Definition Q (a:aexp) : Prop :=
       match a with
       | AID (Id 0) => fun st => False
       | _          => fun st => True
       end.
]]
    together with any [V = Id 0] because a precondition that reduces
    to [True] leads to a postcondition that is [False].)  And second,
    even if we could prove something similar to this, it would be
    awkward to use.  *)
(** [Q]を算術式を添字とする表明の族として扱うことで、代入規則を Coq で直接
    形式化してみることもできます。例えば次のようになります。
[[
      Theorem hoare_asgn_firsttry :
        forall (Q : aexp -> Assertion) V a,
        {{fun st => Q a st}} (V ::= a) {{fun st => Q (AId V) st}}.
]]
    しかし、この形式化は2つの理由であまり良くないのです。第一に、この式は本当に正しい
    とは言えないのです!(反例として、[Q]として自分の引数の「構文」を調べるものを考えて
    みましょう。次のようなものです:
[[
    Definition Q (a:aexp) : Prop :=
       match a with
       | AID (Id 0) => fun st => False
       | _          => fun st => True
       end.
]]
    このとき、代入文として、[V = Id 0] を考えると、事前条件は[True]となりますが、
    事後条件は[False]になります。)第二の理由は、たとえ同様のことが証明できたとしても、
    これは使いにくいのです。*)

(* A much smoother way of formalizing the rule arises from the
    following observation:

    - "[Q] where a is substituted for [X]" holds in a state [st] iff
      [Q] holds in the state [update st X (aeval st a)]. *)
(** 規則を形式化するはるかにスムーズな方法は、以下の洞察から得られます:
    - "[Q]において[X]を a で置換したもの"が状態[st]で成立する必要十分条件は、
      [Q]が状態 [update st X (aeval st a)] で成立することである。*)

(* That is, asserting that a substituted variant of [Q] holds in
    some state is the same as asserting that [Q] itself holds in
    a substituted variant of the state.  *)
(** つまり、ある状態で、[Q]を置換してできるものを表明することは、その状態を置換してできる
    状態で、[Q]を表明することと同じだということです。*)

(* Here is the definition of substitution in a state: *)
(** 状態の置換を次のように定義します: *)

Definition assn_sub V a Q : Assertion :=
  fun (st : state) =>
    Q (update st V (aeval st a)).

(** This gives us the formal proof rule for assignment:
[[[
      ------------------------------ (hoare_asgn)
      {{assn_sub V a Q}} V::=a {{Q}}
]]]
*)
(** これを使って、代入の証明規則を形式的に与えます:
[[[
      ------------------------------ (hoare_asgn)
      {{assn_sub V a Q}} V::=a {{Q}}
]]]
*)

Theorem hoare_asgn : forall Q V a,
  {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(* Here's a first formal proof using this rule. *)
(** この規則を使った最初の形式的証明が次のものです。*)

Example assn_sub_example :
  {{fun st => 3 = 3}}
  (X ::= (ANum 3))
  {{fun st => asnat (st X) = 3}}.
Proof.
  assert ((fun st => 3 = 3) =
          (assn_sub X (ANum 3) (fun st => asnat (st X) = 3))).
  Case "Proof of assertion".
    unfold assn_sub. reflexivity.
  rewrite -> H. apply hoare_asgn.  Qed.

(* This proof is a little clunky because the [hoare_asgn] rule
    doesn't literally apply to the initial goal: it only works with
    triples whose precondition has precisely the form [assn_sub Q V a]
    for some [Q], [V], and [a].  So we have to start with asserting a
    little lemma to get the goal into this form.

    Doing this kind of fiddling with the goal state every time we
    want to use [hoare_asgn] would get tiresome pretty quickly.
    Fortunately, there are easier alternatives.  One simple one is
    to state a slightly more general theorem that introduces an
    explicit equality hypothesis: *)
(** この証明はあまり綺麗ではありません。なぜなら、[hoare_asgn]規則が最初のゴールに
    直接適用されてはいないからです。この規則は、事前条件が、何らかの[Q]、[V]、[a]について
    [assn_sub Q V a]という形をしているときのみに適用できます。このため、ゴールを
    この形にするためのちょっとした補題から始めなければならないのです。

    [hoare_asgn]を使おうとするときに毎回ゴール状態に対してこのような小細工を
    するのは、すぐにいやになります。幸運なことに、より簡単な方法があります。
    その一つは、明示的な等式の形の仮定を導く、いくらか一般性の高い定理を示すことです: *)

Theorem hoare_asgn_eq : forall Q Q' V a,
     Q' = assn_sub V a Q ->
     {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H. rewrite H. apply hoare_asgn.  Qed.

(* With this version of [hoare_asgn], we can do the proof much
    more smoothly. *)
(** [hoare_asgn]のこのバージョンを使うことで、証明をよりスムーズに行うことができます。*)

Example assn_sub_example' :
  {{fun st => 3 = 3}}
  (X ::= (ANum 3))
  {{fun st => asnat (st X) = 3}}.
Proof.
  apply hoare_asgn_eq. reflexivity.  Qed.

(* **** Exercise: 2 stars (hoare_asgn_examples) *)
(** **** 練習問題: ★★ (hoare_asgn_examples) *)
(* Translate these informal Hoare triples...
[[
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
   ...into formal statements and use [hoare_asgn_eq] to prove
   them. *)
(** 次の非形式的なホーアの三つ組...
[[
       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}
]]
   ...を、形式的記述に直し、[hoare_asgn_eq]を使って証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 3 stars (hoarestate2) *)
(** **** 練習問題: ★★★ (hoarestate2) *)
(* The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
[[
      {{ True }} X ::= a {{ X = a }}
]]
    Explain what is wrong with this rule.

    (* FILL IN HERE *)
*)
(** 代入規則は、最初に見たとき、ほとんどの人が後向きの規則であるように見えます。もし今でも
    後向きに見えるならば、前向きバージョンの規則を考えてみるのも良いかもしれません。
    次のものは自然に見えます:
[[
      {{ True }} X ::= a {{ X = a }}
]]
    この規則の問題点を指摘しなさい。

    (* FILL IN HERE *)
*)
(** [] *)

(* **** Exercise: 3 stars, optional (hoare_asgn_weakest) *)
(** **** 練習問題: ★★★, optional (hoare_asgn_weakest) *)
(* Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)
(** [hoare_asgn]規則の事前条件が、本当に最弱事前条件であることを示しなさい。*)

Theorem hoare_asgn_weakest : forall P V a Q,
  {{P}} (V ::= a) {{Q}} ->
  forall st, P st -> assn_sub V a Q st.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(* *** Consequence *)
(** *** 帰結 *)

(* The discussion above about the awkwardness of applying the
    assignment rule illustrates a more general point: sometimes the
    preconditions and postconditions we get from the Hoare rules won't
    quite be the ones we want -- they may (as in the above example) be
    logically equivalent but have a different syntactic form that
    fails to unify with the goal we are trying to prove, or they
    actually may be logically weaker (for preconditions) or
    stronger (for postconditions) than what we need.

    For instance, while
[[
      {{3 = 3}} X ::= 3 {{X = 3}},
]]
    follows directly from the assignment rule, the more natural triple
[[
      {{True}} X ::= 3 {{X = 3}}.
]]
    does not.  This triple is also valid, but it is not an instance of
    [hoare_asgn] (or [hoare_asgn_eq]) because [True] and [3 = 3] are
    not syntactically equal assertions.

    In general, if we can derive [{{P}} c {{Q}}], it is valid to
    change [P] to [P'] as long as [P'] is strong enough to imply [P],
    and change [Q] to [Q'] as long as [Q] implies [Q'].

    This observation is captured by the following _Rule of
    Consequence_.
[[[
                {{P'}} c {{Q'}}
         P implies P' (in every state)
         Q' implies Q (in every state)
         -----------------------------  (hoare_consequence)
                {{P}} c {{Q}}
]]]
   For convenience, we can state two more consequence rules -- one for
   situations where we want to just strengthen the precondition, and
   one for when we want to just weaken the postcondition.
[[[
                {{P'}} c {{Q}}
         P implies P' (in every state)
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
         Q' implies Q (in every state)
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
]]]
 *)
(** 代入規則の適用のぎこちなさに関する上記の議論は、より一般的なポイントを示しています。
    ホーア規則から得られる事前条件と事後条件は欲しいものではないことがしばしばあるのです。
    (上の例のように)それらは論理的に同値ですが、構文的に違う形をしているために、
    証明しようと思うゴールと単一化することができないのです。あるいは、(事前条件について)
    必要なものより論理的に弱かったり、(事後条件について)論理的に強かったりするのです。

    例えば、
[[
      {{3 = 3}} X ::= 3 {{X = 3}},
]]
    が代入規則に直接従うのに対して、より自然な三つ組
[[
      {{True}} X ::= 3 {{X = 3}}.
]]
    はそうではないのです。この三つ組も正しいのですが、[hoare_asgn] 
    (または [hoare_asgn_eq]) のインスタンスではないのです。
    なぜなら、[True] と [3 = 3] は、構文的に等しい表明ではないからです。

    一般に、[{{P}} c {{Q}}] が導出できるとき、[P']ならば[P]が言えるだ
    け[P']が強いならば[P]を[P']に置き換えることは正しく、また[Q]ならば
    [Q']が言えるならば、[Q]を[Q']に置き換えることは正しいのです。

    この洞察をまとめたものが、次の帰結規則(_Rule of Consequence_)です。
[[[
                {{P'}} c {{Q'}}
         P implies P' (in every state)
         Q' implies Q (in every state)
         -----------------------------  (hoare_consequence)
                {{P}} c {{Q}}
]]]
   便宜上、さらに2つの帰結規則を用意します。1つは事前条件を強めるだけのもの、もう1つは
   事後条件を弱めるだけのものです。
[[[
                {{P'}} c {{Q}}
         P implies P' (in every state)
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
         Q' implies Q (in every state)
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
]]]
 *)

(* Here are the formal versions: *)
(** 以下が形式化版です: *)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q.  apply (Hht st st'). assumption.
  apply HPP'. assumption.  Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  (forall st, P st -> P' st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  apply hoare_consequence with (P' := P') (Q' := Q);
    try assumption.
  intros st H. apply H.  Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  apply hoare_consequence with (P' := P) (Q' := Q');
    try assumption.
  intros st H. apply H.  Qed.

(* For example, we might use (the "[_pre]" version of) the
    consequence rule like this:
[[
                {{ True }} =>
                {{ 1 = 1 }}
    X ::= 1
                {{ X = 1 }}
]]
    Or, formally...
*)
(** (例えば、("[_pre]"版の)帰結規則を次のように使うことができます:
[[
                {{ True }} =>
                {{ 1 = 1 }}
    X ::= 1
                {{ X = 1 }}
]]
    あるいは、形式化すると...
*)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => asnat (st X) = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := (fun st => 1 = 1)).
  apply hoare_asgn_eq. reflexivity.
  intros st H. reflexivity.  Qed.


(* ####################################################### *)
(** *** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature
    of Coq.  Having to write [P'] explicitly in the example above
    is a bit annoying because the very next thing we are going to
    do -- applying the [hoare_asgn] rule -- is going to determine
    exactly what it should be.  We can use [eapply] instead of
    [apply] to tell Coq, essentially, "The missing part is going
    to be filled in later." *)

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => asnat (st X) = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn_eq. reflexivity. (* or just [apply hoare_asgn.] *)
  intros st H. reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H]
    except that, instead of failing if unifying the goal with the
    conclusion of [H] does not determine how to instantiate all
    of the variables appearing in the premises of [H], [eapply H]
    will replace these variables with _existential variables_
    (written [?nnn]) as placeholders for expressions that will be
    determined (by further unification) later in the proof.

    There is also an [eassumption] tactic that works similarly. *)

(* ####################################################### *)
(** *** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property P:
[[[
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
]]]
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *)
(** *** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:
[[[
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
]]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); try assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in "backwards" order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule. *)

(** Informally, a nice way of recording a proof using this rule
    is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:
[[
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- decoration for Q
    SKIP
      {{ X = n }}
]]
*)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  Case "right part of seq".
    apply hoare_skip.
  Case "left part of seq".
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H.  subst.  reflexivity. Qed.

(** **** Exercise: 2 stars (hoare_asgn_example4) *)
(** Translate this decorated program into a formal proof:
[[
                   {{ True }} =>
                   {{ 1 = 1 }}
    X ::= 1;
                   {{ X = 1 }} =>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
]]
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1); Y ::= (ANum 2))
  {{fun st => asnat (st X) = 1 /\ asnat (st Y) = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (swap_exercise) *)
(** Write an Imp program [c] that swaps the values of [X] and [Y]
    and show (in Coq) that it satisfies the following
    specification:
[[
      {{X <= Y}} c {{Y <= X}}
]]
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (hoarestate1) *)
(** Explain why the following proposition can't be proven:
[[
      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}} (X ::= (ANum 3); Y ::= a)
         {{fun st => asnat (st Y) = n}}.
]]
*)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** *** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  Certainly, if the same assertion [Q] holds after
    executing either branch, then it holds after the whole
    conditional.  So we might be tempted to write:
[[[
              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}
]]]
   However, this is rather weak. For example, using this rule,
   we cannot show that:
[[
     {{True}}
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1
     FI
     {{ X <= Y }}
]]
   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches.

   But, actually, we can say something more precise.  In the "then"
   branch, we know that the boolean expression [b] evaluates to
   [true], and in the "else" branch, we know it evaluates to [false].
   Making this information available in the premises of the lemma
   gives us more information to work with when reasoning about the
   behavior of [c1] and [c2] (i.e., the reasons why they establish the
   postcondtion [Q]).
[[[
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
]]]
*)

(** To interpret this rule formally, we need to do a little work.

    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression, which
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  Case "b is true".
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example :
    {{fun st => True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
    {{fun st => asnat (st X) <= asnat (st Y)}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  Case "Then".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, update. simpl. intros.
    inversion H.
       symmetry in H1; apply beq_nat_eq in H1.
       rewrite H1.  omega.
  Case "Else".
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, update; simpl; intros. omega.
Qed.

(* ####################################################### *)
(** *** Loops *)

(** Finally, we need a rule for reasoning about while loops.  Suppose
    we have a loop
[[
      WHILE b DO c END
]]
    and we want to find a pre-condition [P] and a post-condition
    [Q] such that
[[
      {{P}} WHILE b DO c END {{Q}}
]]
    is a valid triple.

    First of all, let's think about the case where [b] is false
    at the beginning, so that the loop body never executes at
    all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write
[[
      {{P}} WHILE b DO c END {{P}}.
]]
    But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little:
[[
      {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule:
[[[
                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
    The proposition [P] is called an _invariant_.

    This is almost the rule we want, but again it can be improved
    a little: at the beginning of the loop body, we know not only
    that [P] holds, but also that the guard [b] is true in the
    current state.  This gives us a little more information to
    use in reasoning about [c].  Here is the final version of the
    rule:
[[[
               {{P /\ b}} c {{P}}
        -----------------------------------  [hoare_while]
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]]
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on He, because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  ceval_cases (induction He) Case; try (inversion Heqwcom); subst.

  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false.  assumption.

  Case "E_WhileLoop".
    apply IHHe2.  reflexivity.
    apply (Hhoare st st'); try assumption.
      split. assumption. apply bexp_eval_true. assumption.  Qed.

Example while_example :
    {{fun st => asnat (st X) <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => asnat (st X) = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn,  assn_sub. intros.  rewrite update_eq. simpl.
     inversion H as [_ H0].  simpl in H0. apply ble_nat_true in H0.
     omega.
  unfold bassn. intros. inversion H as [Hle Hb]. simpl in Hb.
     remember (ble_nat (asnat (st X)) 2) as le.  destruct le.
     apply ex_falso_quodlibet. apply Hb; reflexivity.
     symmetry in Heqle. apply ble_nat_false in Heqle. omega.
Qed.

(** We can also use the while rule to prove the following Hoare
    triple, which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  Case "Loop body preserves invariant".
    apply hoare_post_true. intros st. apply I.
  Case "Loop invariant and negated guard imply postcondition".
    simpl. intros st [Hinv Hguard].
    apply ex_falso_quodlibet. apply Hguard. reflexivity.
  Case "Precondition implies invariant".
    intros st H. constructor.  Qed.

(** Actually, this result shouldn't be surprising.  If we look back at
    the definition of [hoare_triple], we can see that it asserts
    something meaningful _only_ when the command terminates. *)

Print hoare_triple.

(** If the command doesn't terminate, we can prove anything we like
    about the post-condition.  Here's a more direct proof of the same
    fact: *)

Theorem always_loop_hoare' : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra.
Qed.

(** Hoare rules that only talk about terminating commands are often
    said to describe a logic of "partial" correctness.  It is also
    possible to give Hoare rules for "total" correctness, which build
    in the fact that the commands terminate. *)

(* ####################################################### *)
(** *** Exercise: Hoare Rules for [REPEAT] *)

Module RepeatExercise.

(** **** Exercise: 4 stars (hoare_repeat) *)
(** In this exercise, we'll add a new constructor to our language of
    commands: [CRepeat].  You will write the evaluation rule for
    [repeat] and add a new hoare logic theorem to the language for
    programs involving it.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CRepeat" ].

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n V,
      aeval st a1 = n ->
      ceval st (V ::= a1) (update st V n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* FILL IN HERE *)
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
(* FILL IN HERE *)
].

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '||' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st || st') -> P st -> Q st'.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

(** Now state and prove a theorem, [hoare_repeat], that expresses an
     appropriate proof rule for [repeat] commands.  Use [hoare_while]
     as a model. *)

(* FILL IN HERE *)

End RepeatExercise.
(** [] *)

(* ####################################################### *)
(** ** Decorated Programs *)

(** The whole point of Hoare Logic is that it is compositional -- the
    structure of proofs exactly follows the structure of programs.
    This fact suggests that we we could record the essential ideas of
    a proof informally (leaving out some low-level calculational
    details) by decorating programs with appropriate assertions around
    each statement.  Such a _decorated program_ carries with it
    an (informal) proof of its own correctness.

   For example, here is a complete decorated program:
[[
      {{ True }} =>
      {{ x = x }}
    X ::= x;
      {{ X = x }} =>
      {{ X = x /\ z = z }}
    Z ::= z;
      {{ X = x /\ Z = z }} =>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} =>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1
        {{ Z - X = z - x }}
    END;
      {{ Z - X = z - x /\ ~ (X <> 0) }} =>
      {{ Z = z - x }} =>
      {{ Z + 1 = z - x + 1 }}
    Z ::= Z + 1
      {{ Z = z - x + 1 }}
]]
*)

(** Concretely, a decorated program consists of the program text
    interleaved with assertions.  To check that a decorated program
    represents a valid proof, we check that each individual command is
    _locally_ consistent with its accompanying assertions in the
    following sense:

    - [SKIP] is locally consistent if its precondition and
      postcondition are the same
[[
          {{ P }}
          SKIP
          {{ P }}
]]
    - The sequential composition of commands [c1] and [c2] is locally
      consistent (with respect to assertions [P] and [R]) if [c1]
      is (with respect to [P] and [Q]) and [c2] is (with respect to
      [Q] and [R]):
[[
          {{ P }}
          c1;
          {{ Q }}
          c2
          {{ R }}
]]

    - An assignment is locally consistent if its precondition is
      the appropriate substitution of its postcondition:
[[
          {{ P where a is substituted for X }}
          X ::= a
          {{ P }}
]]
    - A conditional is locally consistent (with respect to assertions
      [P] and [Q]) if the assertions at the top of its "then" and
      "else" branches are exactly [P/\b] and [P/\~b] and if its "then"
      branch is locally consistent (with respect to [P/\b] and [Q])
      and its "else" branch is locally consistent (with respect to
      [P/\~b] and [Q]):
[[
          {{ P }}
          IFB b THEN
            {{ P /\ b }}
            c1
            {{ Q }}
          ELSE
            {{ P /\ ~b }}
            c2
            {{ Q }}
          FI
]]

    - A while loop is locally consistent if its postcondition is
      [P/\~b] (where [P] is its precondition) and if the pre- and
      postconditions of its body are exactly [P/\b] and [P]:
[[
          {{ P }}
          WHILE b DO
            {{ P /\ b }}
            c1
            {{ P }}
          END
          {{ P /\ ~b }}
]]

    - A pair of assertions separated by [=>] is locally consistent if
      the first implies the second (in all states):
[[
          {{ P }} =>
          {{ P' }}
]]
*)

(* ####################################################### *)
(** * Reasoning About Programs with Hoare Logic *)

(* ####################################################### *)
(** ** Example: Slow Subtraction *)

(** Informally:
[[
      {{ X = x /\ Z = z }} =>
      {{ Z - X = z - x }}
    WHILE X <> 0 DO
        {{ Z - X = z - x /\ X <> 0 }} =>
        {{ (Z - 1) - (X - 1) = z - x }}
      Z ::= Z - 1;
        {{ Z - (X - 1) = z - x }}
      X ::= X - 1
        {{ Z - X = z - x }}
    END
      {{ Z - X = z - x /\ ~ (X <> 0) }} =>
      {{ Z = z - x }}
]]
*)

(** Formally: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= AMinus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition subtract_slowly_invariant x z :=
  fun st => minus (asnat (st Z)) (asnat (st X)) = minus z x.

Theorem subtract_slowly_correct : forall x z,
  {{fun st => asnat (st X) = x /\ asnat (st Z) = z}}
  subtract_slowly
  {{fun st => asnat (st Z) = minus z x}}.
Proof.
  (* Note that we do NOT unfold the definition of hoare_triple
     anywhere in this proof!  The goal is to use only the hoare
     rules.  Your proofs should do the same. *)

  intros x z. unfold subtract_slowly.
  (* First we need to transform the pre and postconditions so
     that hoare_while will apply.  In particular, the
     precondition should be the loop invariant. *)
  eapply hoare_consequence with (P' := subtract_slowly_invariant x z).
  apply hoare_while.

  Case "Loop body preserves invariant".
    (* Split up the two assignments with hoare_seq - using eapply
       lets us solve the second one immediately with hoare_asgn *)
    eapply hoare_seq. apply hoare_asgn.
    (* Now for the first assignment, transform the precondition
       so we can use hoare_asgn *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    (* Finally, we need to justify the implication generated by
       hoare_consequence_pre (this bit of reasoning is elided in the
       informal proof) *)
    unfold subtract_slowly_invariant, assn_sub, update, bassn. simpl.
    intros st [Inv GuardTrue].
    (* There are several ways to do the case analysis here...this
       one is fairly general: *)
    remember (beq_nat (asnat (st X)) 0) as Q; destruct Q.
     inversion GuardTrue.
     symmetry in HeqQ.  apply beq_nat_false in HeqQ.
     omega. (* slow but effective! *)
  Case "Initial state satisfies invariant".
    (* This is the subgoal generated by the precondition part of our
       first use of hoare_consequence.  It's the first implication
       written in the decorated program (though we elided the actual
       proof there). *)
    unfold subtract_slowly_invariant.
    intros st [HX HZ]. omega.
  Case "Invariant and negated guard imply postcondition".
   (* This is the subgoal generated by the postcondition part of
      out first use of hoare_consequence.  This implication is
      the one written after the while loop in the informal proof. *)
    intros st [Inv GuardFalse].
    unfold subtract_slowly_invariant in Inv.
    unfold bassn in GuardFalse. simpl in GuardFalse.
    (* Here's a slightly different alternative for the case analysis that
       works out well here (but is less general)... *)
    destruct (asnat (st X)).
      omega.
      apply ex_falso_quodlibet.   apply GuardFalse. reflexivity.
    Qed.

(* ####################################################### *)
(** ** Exercise: Reduce to Zero *)

(** Here is a while loop that is so simple it needs no invariant:
[[
          {{ True }}
        WHILE X <> 0 DO
            {{ True /\ X <> 0 }} =>
            {{ True }}
          X ::= X - 1
            {{ True }}
        END
          {{ True /\ X = 0 }} =>
          {{ X = 0 }}
]]
   Your job is to translate this proof to Coq.  It may help to look
   at the [slow_subtraction] proof for ideas.
*)

(** **** Exercise: 2 stars (reduce_to_zero_correct) *)
Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct :
  {{fun st => True}}
  reduce_to_zero
  {{fun st => asnat (st X) = 0}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ####################################################### *)
(** ** Exercise: Slow Addition *)

(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z. *)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(** **** Exercise: 3 stars (add_slowly_decoration) *)
(** Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (add_slowly_formal) *)
(** Now write down your specification of [add_slowly] formally, as a
    Coq [Hoare_triple], and prove it valid. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Example: Parity *)

(** Here's another, slightly trickier example.  Make sure you
    understand the decorated program completely.  Understanding
    all the details of the Coq proof is not required, though it
    is not actually very hard -- all the required ideas are
    already in the informal version. *)
(**
[[
    {{ X = x }} =>
    {{ X = x /\ 0 = 0 }}
  Y ::= 0;
    {{ X = x /\ Y = 0 }} =>
    {{ (Y=0 <-> ev (x-X)) /\ X<=x }}
  WHILE X <> 0 DO
      {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
      {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    Y ::= 1 - Y;
      {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    X ::= X - 1
      {{ Y=0 <-> ev (x-X) /\ X<=x }}
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
    {{ Y=0 <-> ev x }}
]]
*)

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition find_parity_invariant x :=
  fun st =>
       asnat (st X) <= x
    /\ (asnat (st Y) = 0 /\ ev (x - asnat (st X)) \/ asnat (st Y) = 1 /\ ~ev (x - asnat (st X))).

(* It turns out that we'll need the following lemma... *)
Lemma not_ev_ev_S_gen: forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      apply ex_falso_quodlibet. apply H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    inversion IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra.
      apply H. apply ev_SS. apply contra.  Qed.

Lemma not_ev_ev_S : forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.

Theorem find_parity_correct : forall x,
  {{fun st => asnat (st X) = x}}
  find_parity
  {{fun st => asnat (st Y) = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
  apply hoare_seq with (Q := find_parity_invariant x).
  eapply hoare_consequence.
  apply hoare_while with (P := find_parity_invariant x).
  Case "Loop body preserves invariant".
    eapply hoare_seq.
    apply hoare_asgn.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *.
    rewrite update_eq.
    rewrite (update_neq Y X); auto.
    rewrite (update_neq X Y); auto.
    rewrite update_eq.
    simpl in GuardTrue. destruct (asnat (st X)).
      inversion GuardTrue. simpl.
    split. omega.
    inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                     [right|left]; (split; simpl; [omega |]).
    apply ev_not_ev_S in H2.
    replace (S (x - S n)) with (x-n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
  Case "Precondition implies invariant".
    intros st H. assumption.
  Case "Invariant implies postcondition".
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (asnat (st X)).
      split; intro.
        inversion Inv2.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
           assumption.
           inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'.
        inversion Inv2.
           inversion H0. assumption.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
           apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
  Case "invariant established before loop".
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst.
    split.
    omega.
    replace (asnat (st X) - asnat (st X)) with 0 by omega.
    left. split. reflexivity.
    apply ev_0.  Qed.

(** **** Exercise: 3 stars (wrong_find_parity_invariant) *)
(** A plausible first attempt at stating an invariant for [find_parity]
    is the following. *)

Definition find_parity_invariant' x :=
  fun st =>
    (asnat (st Y)) = 0 <-> ev (x - asnat (st X)).

(** Why doesn't this work?  (Hint: Don't waste time trying to answer
    this exercise by attempting a formal proof and seeing where it
    goes wrong.  Just think about whether the loop body actually
    preserves the property.) *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Example: Finding Square Roots *)

Definition sqrt_loop : com :=
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion :=
  fun st =>
       ((asnat (st Z)) * (asnat (st Z))) <= x
    /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st =>
       asnat (st X) = x
    /\ ((asnat (st Z)) * (asnat (st Z))) <= x.

Theorem random_fact_1 : forall st,
     (S (asnat (st Z))) * (S (asnat (st Z))) <= asnat (st X) ->
     bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                       (APlus (ANum 1) (AId Z)))
                (AId X)) st.
Proof.
  intros st Hle.  unfold bassn. simpl.
  destruct (asnat (st X)) as [|x'].
  Case "asnat (st X) = 0".
    inversion Hle.
  Case "asnat (st X) = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (ble_nat (plus (asnat (st Z))
                      ((asnat (st Z)) * (S (asnat (st Z))))) x')
      as ble.
    destruct ble. reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble.
    unfold not in Heqble. apply Heqble in Hle. inversion Hle.
Qed.

Theorem random_fact_2 : forall st,
     bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                       (APlus (ANum 1) (AId Z)))
                (AId X)) st ->
       asnat (aeval st (APlus (ANum 1) (AId Z)))
     * asnat (aeval st (APlus (ANum 1) (AId Z)))
     <= asnat (st X).
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (asnat (st X)) as [| x'].
  Case "asnat (st X) = 0".
    inversion Hble.
  Case "asnat (st X) = S x'".
    apply ble_nat_true in Hble. omega. Qed.

Theorem sqrt_com_correct : forall x,
  {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
Proof.
  intros x.
  apply hoare_seq with (Q := fun st => asnat (st X) = x).
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (Q := fun st => asnat (st X) = x
                                      /\ asnat (st Z) = 0).

    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
      apply hoare_while with (P := sqrt_inv x).

      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
        apply hoare_asgn. intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        inversion H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; auto.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.

      SSCase "invariant is true initially".
        intros st H. inversion H as [HX HZ].
        unfold sqrt_inv. split. assumption.
        rewrite HZ. simpl. omega.

      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        inversion H as [HX HP].
        unfold sqrt_inv in HX.  inversion HX as [HX' Harith].
        split. assumption.
        intros contra. apply HP. clear HP.
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.

    SCase "Z set to 0".
      eapply hoare_consequence_pre. apply hoare_asgn.
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq; auto.
      rewrite update_eq; auto.

  Case "assignment of X".
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H.
    unfold assn_sub. rewrite update_eq; auto.  Qed.

(** **** Exercise: 3 stars, optional (sqrt_informal) *)
(** Write a decorated program corresponding to the above
    correctness proof. *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Exercise: Factorial *)

Module Factorial.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Recall the factorial Imp program: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

(** **** Exercise: 3 stars, optional (fact_informal) *)
(** Decorate the [fact_com] program to show that it satisfies the
    specification given by the pre and postconditions below.  Just as
    we have done above, you may elide the algebraic reasoning about
    arithmetic, the less-than relation, etc., that is (formally)
    required by the rule of consequence:

(* FILL IN HERE *)
[[
    {{ X = x }}
  Z ::= X;
  Y ::= 1;
  WHILE Z <> 0 DO
    Y ::= Y * Z;
    Z ::= Z - 1
  END
    {{ Y = real_fact x }}
]]
*)
(** [] *)


(** **** Exercise: 4 stars, optional (fact_formal) *)
(** Prove formally that fact_com satisfies this specification,
    using your informal proof as a guide.  You may want to state
    the loop invariant separately (as we did in the examples). *)

Theorem fact_com_correct : forall x,
  {{fun st => asnat (st X) = x}} fact_com
  {{fun st => asnat (st Y) = real_fact x}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Factorial.

(* ####################################################### *)
(** ** Reasoning About Programs with Lists *)

(** **** Exercise: 3 stars (list_sum) *)
(** Here is a direct definition of the sum of the elements of a list,
    and an Imp program that computes the sum. *)

Definition sum l := fold_right plus 0 l.

Definition sum_program :=
  Y ::= ANum 0;
  WHILE (BIsCons (AId X)) DO
    Y ::= APlus (AId Y) (AHead (AId X)) ;
    X ::= ATail (AId X)
  END.

(** Provide an _informal_ proof of the following specification of
    [sum_program] in the form of a decorated version of the
    program. *)

Definition sum_program_spec := forall l,
  {{ fun st => aslist (st X) = l }}
  sum_program
  {{ fun st => asnat (st Y) = sum l }}.

(* FILL IN HERE *)
(** [] **)

(** Next, let's look at a _formal_ Hoare Logic proof for a program
    that deals with lists.  We will verify the following program,
    which checks if the number [Y] occurs in the list [X], and if so sets
    [Z] to [1].
*)

Definition list_member :=
  WHILE BIsCons (AId X) DO
    IFB (BEq (AId Y) (AHead (AId X))) THEN
      Z ::= (ANum 1)
    ELSE
      SKIP
    FI;
    X ::= ATail (AId X)
  END.

Definition list_member_spec := forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.

(** The proof we will use, written informally, looks as follows:
[[
    {{ X = l /\ Y = n /\ Z = 0 }} =>
    {{ Y = n /\ exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p) }}
  WHILE (BIsCons X)
  DO
      {{ Y = n /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
               /\ (BIsCons X) }}
    IFB (Y == head X) THEN
        {{ Y = n
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
           /\ (BIsCons X)
           /\ Y == AHead X }} =>
        {{ Y = n /\ (exists p, p ++ tail X = l
                    /\ (1 = 1 <-> appears_in n p)) }}
      Z ::= 1
        {{ Y = n /\ (exists p, p ++ tail X = l
        /\ (Z = 1 <-> appears_in n p)) }}
    ELSE
        {{ Y = n
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
           /\ (BIsCons X)
           /\ ~ (Y == head X) }} =>
        {{ Y = n
           /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
      SKIP
        {{ Y = n
           /\ (exists p, p ++ tail X = l /\ (Z = 1 <-> appears_in n p)) }}
    FI;
    X ::= ATail X
        {{ Y = n
           /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)) }}
  END
     {{ Y = n
        /\ (exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p))
        /\ ~ (BIsCons X) }} =>
     {{ Z = 1 <-> appears_in n l }}
]]

  The only interesting part of the proof is the choice of loop invariant:
[[
      exists p, p ++ X = l /\ (Z = 1 <-> appears_in n p)
]]
  This states that at each iteration of the loop, the original list
  [l] is equal to the append of the current value of [X] and some
  other list [p] which is not the value of any variable in the
  program, but keeps track of enough information from the original
  state to make the proof go through. (Such a [p] is sometimes called
  a "ghost variable").

  In order to show that such a list [p] exists, in each iteration we
  add the head of [X] to the _end_ of [p]. This needs the function
  [snoc], from Poly.v. *)

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil      =>  [ v ]
  | cons h t => h :: (snoc t v)
  end.

Lemma snoc_equation : forall (A : Type) (h:A) (x y : list A),
  snoc x h ++ y = x ++ h :: y.
Proof.
  intros A h x y.
  induction x.
    Case "x = []". reflexivity.
    Case "x = cons". simpl. rewrite IHx. reflexivity.
Qed.

(** The main proof uses various lemmas. *)

Lemma appears_in_snoc1 : forall a l,
  appears_in a (snoc l a).
Proof.
  induction l.
    Case "l = []". apply ai_here.
    Case "l = cons". simpl. apply ai_later. apply IHl.
Qed.

Lemma appears_in_snoc2 : forall a b l,
  appears_in a l ->
  appears_in a (snoc l b).
Proof.
  induction l; intros H; inversion H; subst; simpl.
    Case "l = []". apply ai_here.
    Case "l = cons". apply ai_later. apply IHl. assumption.
Qed.

Lemma appears_in_snoc3 : forall a b l,
   appears_in a (snoc l b) ->
   (appears_in a l \/ a = b).
Proof.
   induction l; intros H.
   Case "l = []". inversion H.
     SCase "ai_here". right. reflexivity.
     SCase "ai_later". left. assumption.
   Case "l = cons". inversion H; subst.
     SCase "ai_here". left. apply ai_here.
     SCase "ai_later". destruct (IHl H1).
       left. apply ai_later. assumption.
       right. assumption.
Qed.

Lemma append_singleton_equation : forall (x : nat) l l',
  (l ++ [x]) ++ l' = l ++ x :: l'.
Proof.
  intros x l l'.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma append_nil : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma beq_true__eq : forall n n',
  beq_nat n n' = true ->
  n = n'.
Proof.
  induction n; destruct n'.
  Case "n = 0, n' = 0".     reflexivity.
  Case "n = 0, n' = S _".   simpl. intros H. inversion H.
  Case "n = S, n' = 0".     simpl. intros H. inversion H.
  Case "n = S, n' = S".     simpl. intros H.
                            rewrite (IHn n' H). reflexivity.
Qed.

Lemma beq_nat_refl : forall n,
  beq_nat n n = true.
Proof.
  induction n.
    reflexivity.
    simpl. assumption.
Qed.

Theorem list_member_correct : forall l n,
  {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  list_member
  {{ fun st => st Z = VNat 1 <-> appears_in n l }}.
Proof.
  intros l n.
  eapply hoare_consequence.
  apply hoare_while with (P := fun st =>
     st Y = VNat n
     /\ exists p, p ++ aslist (st X) = l
                  /\ (st Z = VNat 1 <-> appears_in n p)).
    (* The loop body preserves the invariant: *)
    eapply hoare_seq.
    apply hoare_asgn.
    apply hoare_if.
    Case "If taken".
      eapply hoare_consequence_pre.
      apply hoare_asgn.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      unfold assn_sub. split.
      (* (st Y) is still n *)
        rewrite update_neq; try reflexivity.
        rewrite update_neq; try reflexivity.
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
          rewrite <- Heqx in H9. inversion H9.

          exists (snoc p h).
          rewrite update_eq.
          unfold aeval. rewrite update_neq; try reflexivity.
          rewrite <- Heqx.
          split.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            rewrite update_eq.
            split.
              simpl.
              unfold bassn in H10. unfold beval in H10.
              unfold aeval in H10. rewrite H1 in H10.
              rewrite <- Heqx in H10. simpl in H10.
              rewrite (beq_true__eq _ _ H10).
              intros. apply appears_in_snoc1.

              intros. reflexivity.
    Case "If not taken".
      eapply hoare_consequence_pre. apply hoare_skip.
      unfold assn_sub.
      intros st [[[H1 [p [H2 H3]]] H9] H10].
      split.
      (* (st Y) is still n *)
        rewrite update_neq; try reflexivity.
        assumption.
      (* and the interesting part of the invariant is preserved: *)
        (* X has to be a cons *)
        remember (aslist (st X)) as x.
        destruct x as [|h x'].
          unfold bassn in H9. unfold beval in H9. unfold aeval in H9.
          rewrite <- Heqx in H9. inversion H9.

          exists (snoc p h).
          split.
            rewrite update_eq.
            unfold aeval. rewrite <- Heqx.
            rewrite snoc_equation. assumption.

            rewrite update_neq; try reflexivity.
            split.
              intros. apply appears_in_snoc2. apply H3. assumption.

              intros.  destruct (appears_in_snoc3 _ _ _ H).
              SCase "later".
                inversion H3 as [_ H3'].
                apply H3'. assumption.
              SCase "here (absurd)".
                subst.
                unfold bassn in H10. unfold beval in H10. unfold aeval in H10.
                rewrite <- Heqx in H10. rewrite H1 in H10.
                simpl in H10. rewrite beq_nat_refl in H10.
                apply ex_falso_quodlibet. apply H10. reflexivity.
  (* The invariant holds at the start of the loop: *)
  intros st [H1 [H2 H3]].
  rewrite H1. rewrite H2. rewrite H3.
  split.
    reflexivity.
    exists []. split.
      reflexivity.
      split; intros H; inversion H.
  (* At the end of the loop the invariant implies the right thing. *)
  simpl.   intros st [[H1 [p [H2 H3]]] H5].
  (* x must be [] *)
  unfold bassn in H5. unfold beval in H5. unfold aeval in H5.
  destruct (aslist (st X)) as [|h x'].
    rewrite append_nil in H2.
    rewrite <- H2.
    assumption.

    apply ex_falso_quodlibet. apply H5. reflexivity.
Qed.

(** **** Exercise: 4 stars, optional (list_reverse) *)
(** Recall the function [rev] from Poly.v, for reversing lists. *)

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => []
  | cons h t => snoc (rev t) h
  end.

(** Write an Imp program [list_reverse_program] that reverses
    lists. Formally prove that it satisfies the following
    specification:
[[
    forall l : list nat,
      {{ X =  l /\ Y = nil }}
      list_reverse_program
      {{ Y = rev l }}.
]]
    You may find the lemmas [append_nil] and [rev_equation] useful.
*)

Lemma rev_equation : forall (A : Type) (h : A) (x y : list A),
  rev (h :: x) ++ y = rev x ++ h :: y.
Proof.
  intros. simpl. apply snoc_equation.
Qed.

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** * Formalizing Decorated Programs *)

(** The informal conventions for decorated programs amount to a way of
    displaying Hoare triples in which commands are annotated with
    enough embedded assertions that checking the validity of the
    triple is reduced to simple algebraic calculations showing that
    some assertions were stronger than others.

    In this section, we show that this informal presentation style can
    actually be made completely formal.  *)

(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of commands that includes embedded assertions.  We call the
    new commands _decorated commands_, or [dcom]s. *)

Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI'"
      := (DCIf b P d P' d')
      (at level 80, right associativity)  : dcom_scope.
Notation "'=>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (DCPre P d)
      (at level 90)  : dcom_scope.
Notation "d '=>' {{ P }}"
      := (DCPost d P)
      (at level 91, right associativity)  : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

(** To avoid clashing with the existing [Notation] definitions
    for ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we wrap examples with the
    declaration [% dcom] to signal that we want the notations to be
    interpreted in this scope.

    Careful readers will note that we've defined two notations for the
    [DCPre] constructor, one with and one without a [=>].  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. *)

Example dec_while : dcom := (
    {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0)))
  DO
       {{ fun st => ~(asnat (st X) = 0) }}
      X ::= (AMinus (AId X) (ANum 1))
       {{ fun _ => True }}
  END
    {{ fun st => asnat (st X) = 0 }}
) % dcom.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _          => SKIP
  | DCSeq d1 d2       => (extract d1 ; extract d2)
  | DCAsgn V a _      => V ::= a
  | DCIf b _ d1 _ d2  => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _   => WHILE b DO extract d END
  | DCPre _ d         => extract d
  | DCPost d _        => extract d
  end.

(** The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as
[[
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
]]
    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded in [d]

       - The _pre_-condition is supplied by the context. *)

(** In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn V a Q            => Q
  | DCIf  _ _ d1 _ d2       => post d1
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(** We can define a similar function that extracts the "initial
    precondition" from a decorated program. *)

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn V a Q            => fun st => True
  | DCIf  _ _ t _ e         => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

(** This function is not doing anything sophisticated like calculating
    a weakest precondition; it just recursively searches for an
    explicit annotation at the very beginning of the program,
    returning default answers for programs that lack an explicit
    precondition (like a bare assignment or [SKIP]).

    Using [pre] and [post], and assuming that we adopt the convention
    of always supplying an explicit precondition annotation at the
    very beginning of our decorated programs, we can express what it
    means for a decorated program to be correct as follows: *)

Definition dec_correct (d:dcom) :=
  {{pre d}} (extract d) {{post d}}.

(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified (by some process looking
    at the decorated program) to see that the decorations are
    logically consistent and thus add up to a proof of correctness. *)

(** ** Extracting Verification Conditions *)

(** First, a bit of notation: *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(** We will write [P ~~> Q] (in ASCII, [P ~][~> Q]) for [assert_implies
    P Q]. *)

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

(** Next, the key definition.  The function [verification_conditions]
    takes a [dcom] [d] together with a precondition [P] and returns a
    _proposition_ that, if it can be proved, implies that the triple
    [{{P}} (extract d) {{post d}}] is valid.  It does this by walking
    over [d] and generating a big conjunction including all the "local
    checks" that we listed when we described the informal rules for
    decorated programs.  (Strictly speaking, we need to massage the
    informal rules a little bit to add some uses of the rule of
    consequence, but the correspondence should be clear.) *)

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          =>
      (P ~~> Q)
  | DCSeq d1 d2      =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn V a Q      =>
      (P ~~> assn_sub V a Q)
  | DCIf b P1 t P2 e  =>
      ((fun st => P st /\ bassn b st) ~~> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ~~> P2)
      /\ (post t = post e)
      /\ verification_conditions P1 t
      /\ verification_conditions P2 e
  | DCWhile b Pbody d Ppost      =>
      (* post d is the loop invariant and the initial precondition *)
      (P ~~> post d)
      /\ ((fun st => post d st /\ bassn b st) <~~> Pbody)
      /\ ((fun st => post d st /\ ~(bassn b st)) <~~> Ppost)
      /\ verification_conditions (fun st => post d st /\ bassn b st) d
  | DCPre P' d         =>
      (P ~~> P') /\ verification_conditions P' d
  | DCPost d Q        =>
      verification_conditions P d /\ (post d ~~> Q)
  end.

(** And now, the key theorem, which captures the claim that the
    [verification_conditions] function does its job correctly.  Not
    surprisingly, we need all of the Hoare Logic rules in the
    proof. *)
(** We have used _in_ variants of several tactics before to
    apply them to values in the context rather than the goal. An
    extension of this idea is the syntax [tactic in *], which applies
    [tactic] in the goal and every hypothesis in the context.  We most
    commonly use this facility in conjunction with the [simpl] tactic,
    as below. *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq".
    inversion H as [H1 H2]. clear H.
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn".
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [HQeq [HThen HElse]]]]; clear H.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. apply HThen. assumption.
      simpl. rewrite HQeq.
      eapply hoare_consequence_pre. apply IHd2. apply HElse. assumption.
  Case "While".
    rename a into Pbody. rename a0 into Ppost.
    inversion H as [Hpre [Hbody [Hpost Hd]]]; clear H.
    eapply hoare_consequence.
    apply hoare_while with (P := post d).
      apply IHd. apply Hd.
      assumption. apply Hpost.
  Case "Pre".
    inversion H as [HP Hd]; clear H.
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(** ** Examples *)

(** The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)

Eval simpl in (verification_conditions (fun st => True) dec_while).
(* ====>
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st)
     <~~> (fun st : state => asnat (st X) <> 0)) /\
    ((fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st)
     <~~> (fun st : state => asnat (st X) = 0)) /\
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st)
     ~~> assn_sub X (AMinus (AId X) (ANum 1)) (fun _ : state => True) *)

(** We can certainly work with them using just the tactics we have so
    far, but we can make things much smoother with a bit of
    automation.  We first define a custom [verify] tactic that applies
    splitting repeatedly to turn all the conjunctions into separate
    subgoals and then uses [omega] and [eauto] (a handy
    general-purpose automation tactic that we'll discuss in detail
    later) to deal with as many of them as possible. *)

Tactic Notation "verify" :=
  try apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; simpl in *;
  intros;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  try eauto; try omega.

(** What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct.  For example: *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify; destruct (asnat (st X)).
    inversion H0.
    unfold not. intros. inversion H1.
    apply ex_falso_quodlibet. apply H. reflexivity.
    reflexivity.
    reflexivity.
    apply ex_falso_quodlibet. apply H0. reflexivity.
    unfold not. intros. inversion H0.
    inversion H.
Qed.

(** Another example (formalizing a decorated program we've seen
    before): *)

Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
    {{ fun st => asnat (st X) = x /\ asnat (st Z) = z }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => asnat (st Z) - asnat (st X) = z - x
                 /\ bassn (BNot (BEq (AId X) (ANum 0))) st }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => asnat (st Z) - (asnat (st X) - 1) = z - x }} ;
     X ::= AMinus (AId X) (ANum 1)
       {{ fun st => asnat (st Z) - asnat (st X) = z - x }}
  END
    {{ fun st =>   asnat (st Z)
                 - asnat (st X)
                 = z - x
              /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st }}
    =>
    {{ fun st => asnat (st Z) = z - x }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall x z,
  dec_correct (subtract_slowly_dec x z).
Proof.
  intros. verify.
    rewrite <- H.
    assert (H1: update st Z (VNat (asnat (st Z) - 1)) X = st X).
      apply update_neq. reflexivity.
    rewrite -> H1. destruct (asnat (st X)) as [| X'].
      inversion H0. simpl. rewrite <- minus_n_O. omega.
    destruct (asnat (st X)).
      omega.
      apply ex_falso_quodlibet. apply H0. reflexivity.
Qed.

(** **** Exercise: 3 stars (slow_assignment_dec) *)

(** A roundabout way of assigning a number currently stored in [X] to
   the variable [Y] is to start [Y] at [0], then decrement [X] until it
   hits [0], incrementing [Y] at each step.

   Here is an informal decorated program that implements this idea
   given a parameter [x]: *)

(**
[[
      {{ True }}
    X ::= x
      {{ X = x }} ;
    Y ::= 0
      {{ X = x /\ Y = 0 }} ;
    WHILE X <> 0 DO
        {{ X + Y = x /\ X > 0 }}
      X ::= X - 1
        {{ Y + X + 1 = x }} ;
      Y ::= Y + 1
        {{ Y + X = x }}
    END
      {{ Y = x /\ X = 0 }}
]]
*)

(** Write a corresponding function that returns a value of type [dcom]
    and prove it correct. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (factorial_dec)  *)
(** Remember the factorial function we worked with before: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** Following the pattern of [subtract_slowly_dec], write a decorated
    Imp program that implements the factorial function, and prove it
    correct. *)

(* FILL IN HERE *)
(** [] *)

(** Finally, for a bigger example, let's redo the proof of
    [list_member_correct] from above using our new tools.

    Notice that the [verify] tactic leaves subgoals for each use of
    [hoare_consequence] -- that is, for each [=>] that occurs in the
    decorated program. Each of these implications relies on a fact
    about lists, for example that [l ++ [] = l]. In other words, the
    Hoare logic infrastructure has taken care of the boilerplate
    reasoning about the execution of imperative programs, while the
    user has to prove lemmas that are specific to the problem
    domain (e.g. lists or numbers). *)

Definition list_member_dec (n : nat) (l : list nat) : dcom := (
    {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  WHILE BIsCons (AId X)
  DO {{ fun st => st Y = VNat n
               /\ (exists p, p ++ aslist (st X) = l
               /\ (st Z = VNat 1 <-> appears_in n p))
               /\ bassn (BIsCons (AId X)) st }}
    IFB (BEq (AId Y) (AHead (AId X))) THEN
        {{ fun st =>
          ((st Y = VNat n
            /\ (exists p, p ++ aslist (st X) = l
                /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st =>
            st Y = VNat n
            /\ (exists p, p ++ tail (aslist (st X)) = l
                 /\ (VNat 1 = VNat 1 <-> appears_in n p)) }}
      Z ::= ANum 1
        {{ fun st => st Y = VNat n
             /\ (exists p, p ++ tail (aslist (st X)) = l
                  /\ (st Z = VNat 1 <-> appears_in n p)) }}
   ELSE
        {{ fun st =>
          ((st Y = VNat n
            /\ (exists p, p ++ aslist (st X) = l
                  /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ ~bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st =>
          st Y = VNat n
          /\ (exists p, p ++ tail (aslist (st X)) = l
               /\ (st Z = VNat 1 <-> appears_in n p)) }}
      SKIP
        {{ fun st => st Y = VNat n
            /\ (exists p, p ++ tail (aslist (st X)) = l
                 /\ (st Z = VNat 1 <-> appears_in n p)) }}
   FI ;
   X ::= (ATail (AId X))
     {{ fun st  =>
         st Y = VNat n /\
         (exists p : list nat, p ++ aslist (st X) = l
           /\ (st Z = VNat 1 <-> appears_in n p)) }}
  END
   {{ fun st =>
     (st Y = VNat n
       /\ (exists p, p ++ aslist (st X) = l
            /\ (st Z = VNat 1 <-> appears_in n p)))
     /\ ~bassn (BIsCons (AId X)) st }}
   =>
   {{ fun st => st Z = VNat 1 <-> appears_in n l }}
) %dcom.

Theorem list_member_correct' : forall n l,
  dec_correct (list_member_dec n l).
Proof.
  intros n l.
  verify.
  Case "The loop precondition holds.".
    exists []. simpl. split.
      rewrite H. reflexivity.
      rewrite H1. split; inversion 1.
  Case "IF taken".
    destruct H2 as  [p [H3 H4]].
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      simpl. split.
         rewrite snoc_equation. assumption.
         split.
           rewrite H in H0.
           simpl in H0.
           rewrite (beq_true__eq _ _ H0).
           intros. apply appears_in_snoc1.
           intros. reflexivity.
  Case "If not taken".
    destruct H2 as [p [H3 H4]].
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      split.
        rewrite snoc_equation. assumption.
        split.
          intros. apply appears_in_snoc2. apply H4. assumption.
          intros Hai.  destruct (appears_in_snoc3 _ _ _ Hai).
          SCase "later". apply H4. assumption.
          SCase "here (absurd)".
            subst.
            simpl in H0. rewrite H in H0. rewrite beq_nat_refl in H0.
            apply ex_falso_quodlibet. apply H0. reflexivity.
  Case "Loop postcondition implies desired conclusion (->)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
  Case "loop postcondition implies desired conclusion (<-)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
Qed.


