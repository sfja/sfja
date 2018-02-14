(** * Logic_J: Coqにおける論理 *)
(* * Logic: Logic in Coq *)

(* $Date: 2011-06-22 10:06:32 -0400 (Wed, 22 Jun 2011) $ *)

Require Export Prop_J.

(* Coq's built-in logic is extremely small: [Inductive] definitions,
    universal quantification ([forall]), and implication ([->]) are
    primitive, but all the other familiar logical connectives --
    conjunction, disjunction, negation, existential quantification,
    even equality -- can be defined using just these. *)
(**
   Coqにあらかじめ組み込まれた論理は極めて小さく、帰納的定義([Inductive])、
   全称量化([forall])、含意([->])だけがプリミティブです。しかしそれ以外の論理結合子
   （かつ、または、否定、存在量化子、等号など）も、組み込みのものを用いて定義できます。
*)

(* ########################################################### *)
(* * Quantification and Implication *)
(** * 全称量化 と 含意 *)

(* In fact, [->] and [forall] are the _same_ primitive!  Coq's [->]
    notation is actually just a shorthand for [forall].  The [forall]
    notation is more general, because it allows us to _name_ the
    hypothesis. *)
(**
   実は、[->] と [forall] は 同じものです! Coqの [->] 記法は [forall] の
   短縮記法に過ぎません。仮定に名前をつけることができることから、
   [forall]記法の方が一般的です。
*)

(* For example, consider this proposition: *)
(** 例えば次の命題を考えてみましょう。 *)

Definition funny_prop1 := forall n, forall (E : ev n), ev (n+4).

(* If we had a proof term inhabiting this proposition, it would be a
    function with two arguments: a number [n] and some evidence that
    [n] is even.  But the name [E] for this evidence is not used in
    the rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name.  We could write it like this instead: *)

(**
   もしもこの命題に含まれる証明項があったら、その項は二つの引数
   （一つは、数字[n]、もう一つは[n]が偶数であることの根拠[E]）を持つ
   関数になっているはずです。
   しかし根拠となる[E]は[funny_prop1]の中では使われていませんから、これに
   わざわざ [E] という名前をつけることはちょっと馬鹿げています。
   このような場合は、次のように書くこともできます。
*)

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n+4).

(* Or we can write it in more familiar notation: *)
(** また、より親しみ深い記法では次のようにも書けます。 *)

Definition funny_prop1'' := forall n, ev n -> ev (n+4).

(* This illustrates that "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(** これはつまり "[P -> Q]" は単に "[forall (_:P), Q]" の糖衣構文に過ぎないと
いうことを示しています。 *)

(* ########################################################### *)
(*  * Conjunction *)
(** * 論理積、連言（Conjunction、AND） *)

(*  The logical conjunction of propositions [P] and [Q] is
    represented using an [Inductive] definition with one
    constructor. *)
(** 命題 [P] と [Q] の論理積（ [logical conjunction] ）は、コンストラクタを
    一つしか持たない [Inductive] を使った定義で表せます。 *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

(*  Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)
(** 注意してほしいのは、前の章で取り上げた関数 [ev] の定義と同様に、
    この定義もパラメータ化された命題になっていることです。ただしこの場合はパラメータ
    自身も数値ではなく命題です。 *)

(*  The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q].

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

(** この定義の内容を直感的に理解するのに、そうややこしく考える必要はありません。
    [and P Q] に根拠を与えるには、[P] の根拠と [Q] の根拠が必要
    だということです。もっと精確に言えば、

    - もし [p] が [P] の根拠で、[q] が [Q] の根拠であるなら、[conj p q] を [and P Q] の根拠とすることができる。

    - これは [and P Q] に根拠を与える唯一の方法であること、
      即ち、もし [and P Q] の根拠が与えられたならば、
      その根拠が [conj p q] の形をしており、さらに [p] が [P] の根拠であることと
      [q] が [Q] の根拠であることがわかるということです。

   今後論理積をよく使うことになるので、
   もっと馴染みのある、中置記法を導入することにしましょう。 *)

Notation "P /\ Q" := (and P Q) : type_scope.

(*  (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)
(** （[type_scope] という注釈は、この記法が値にではなく、
    命題に現れるものであることを、Coqに伝えています。） *)

(*  Consider the "type" of the constructor [conj]: *)
(** コンストラクタ [conj] の型はどのようなものか考えてみましょう。 *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(*  Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)
(** conjが四つの引数（ [P] 、[Q] という命題と、[P] 、[Q] の根拠）をとることに注目して下さい。 *)

(*  Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

(** 
    基本的なことから色々なことを組み立てていくエレガントさはさておき、
    このような方法でconjunctionを定義することの利点は、これを含む
    文を、既に知っているタクティックで証明できることです。
    例えば、もしゴールが論理積を含んでいる場合、このたった一つの
    コンストラクタ[conj]を適用するだけで証明できます。
    それは、[conj]の型を見ても分かるように現在のゴールを解決してから
    conjunctionの二つの部分を別々に証明するべきサブゴールにします。
 *)

Theorem and_example :
  (ev 0) /\ (ev 4).
Proof.
  apply conj.
  (* Case "left". *) apply ev_0.
  (* Case "right". *) apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(*  Let's take a look at the proof object for the above theorem. *)
(** 上の定理の証明オブジェクトをよく観察してみてください。 *)

Print and_example.
(* ===>  conj (ev 0) (ev 4) ev_0 (ev_SS 2 (ev_SS 0 ev_0))
            : ev 0 /\ ev 4 *)

(*  Note that the proof is of the form
[[
    conj (ev 0) (ev 4) (...pf of ev 0...) (...pf of ev 4...)
]]
    which is what you'd expect, given the type of [conj]. *)
    
(** この型に注目してください。
[[
    conj (ev 0) (ev 4) (... ev 0 の証明 ...) (... ev 4 の証明 ...)
]]
    さっき見た [conj] と同じ形をしているのが分かるでしょう。 *)

(*  Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)
(** [apply conj] とするかわりに [split] タクティックでも同じことができます。 *)

Theorem and_example' :
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(*  Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and put this evidence into the
    proof context. *)
(** 逆に、[inversion] タクティックを、コンテキストにある論理積の形を
    した仮定に使うことで、それの構築に使われた根拠を取り出し、
    コンテキストに加えることができます。 *)
Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.  Qed.

(** **** 練習問題: ★, optional (proj2) *)
Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ].
  split.
    (* Case "left". *) apply HQ.
    (* Case "right".*) apply HP.  Qed.

(*  Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easy to understand.  Examining it
    shows that all that is really happening is taking apart a record
    containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)
(** この定理の証明を理解しやすくするため、再び [Case] タクティックに
    ついて話します。  この証明で起こっていることをよく観察すると、
    P and Q の根拠となっている命題を抽出して、そこから逆向きに証明を
    再構築していることが分かるでしょう。
 *)
Print and_commut.
(* ===>
   and_commut =
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(*  **** Exercise: 2 stars (and_assoc) *)
(** **** 練習問題: ★★ (and_assoc) *)
(*  In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks [H : P /\ (Q /\ R)] down into [HP: P], [HQ :
    Q], and [HR : R].  Finish the proof from there: *)
(** 次の証明では、[inversion]が、入れ子構造になった命題[H : P /\ (Q /\ R)]を
    どのように[HP: P], [HQ : Q], [HR : R] に分解するか、という点に注意しなが
    がら証明を完成させなさい。
 *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, recommended (even_ev) *)
(*  Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in the last chapter.  Notice that
   the left-hand conjunct here is the statement we are actually
   interested in; the right-hand conjunct is needed in order to make
   the induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)
(**
   今度は、前の章で棚上げしていた [even] と [ev] の等価性をが別の方向から
   証明してみましょう。
   ここで左側のandは我々が実際に注目すべきものです。右のandは帰納法の仮定と
   なって帰納法による証明に結びついていくことになるでしょう。なぜこれが必要と
   なるかは、左側のandをそれ自身で証明しようとして、行き詰まってみると
   かるでしょう。
 *)

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* ヒント: nに帰納法を使います. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★ *)
(** 次の命題の証明を示すオブジェクトを作成しなさい。 *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  (* FILL IN HERE *) admit.
(** [] *)

(** ** Iff （両含意）*)

(*  The familiar logical "if and only if" is just the
    conjunction of two implications. *)
(** この、"if and only if（～である時、その時に限り）" で表される
    「両含意」という論理は馴染みのあるもので、次の二つの
    「ならば（含意）」をandでつないだものです。
 *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** 練習問題: ★ (iff_properties) *)
(*  Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)
(** 上の、 [<->] が対称であることを示す証明 ([iff_sym]) を参考に、それが反射的で
    あること、推移的であることを証明しなさい。
 *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** ヒント: もしコンテキストに iff を含む仮定があれば、 
    [inversion] を使ってそれを二つの含意の式に分割することができます。
    (なぜそうできるのか考えてみましょう。) *)
(** [] *)

(** **** 練習問題: ★★ (MyProp_iff_ev) *)
(*  We have seen that the families of propositions [MyProp] and [ev]
    actually characterize the same set of numbers (the even ones).
    Prove that [MyProp n <-> ev n] for all [n].  Just for fun, write
    your proof as an explicit proof object, rather than using
    tactics. (_Hint_: if you make use of previously defined thoerems,
    you should only need a single line!) *)

(** ここまで、[MyProp] や [ev] が これらの命題がある種の数値を特徴づける（偶数、などの）
    ことを見てきました。
    次の [MyProp n <-> ev n] が任意の [n]で成り立つことを証明しなさい。
    お遊びのつもりでかまわないので、その証明を、単純明快な証明、タクティックを
    使わないような証明に書き換えてください。（ヒント：以前に使用した定理をうまく
    使えば、１行だけでかけるはずです！）
 *)

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  (* FILL IN HERE *) admit.
(** [] *)

(*  Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)
(** Coqのいくつかのタクティックは、証明の際に低レベルな操作を避けるため
    [iff] を特別扱いします。 特に [rewrite] を [iff] に使うと、
    単なる等式以上のものとして扱ってくれます。 *)

(* ############################################################ *)
(*  * Disjunction *)
(** * 論理和、選言（Disjunction、OR） *)

(*  Disjunction ("logical or") can also be defined as an
    inductive proposition. *)
(** 論理和（Disjunction、OR）も、帰納的な命題として定義できます。 *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

(* Consider the "type" of the constructor [or_introl]: *)
(** コンストラクタ [or_introl] の型が何か考えてください。 *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(*  It takes 3 inputs, namely the propositions [P],[Q] and
    evidence of [P], and returns as output, the evidence of [P /\ Q].
    Next, look at the type of [or_intror]: *)
(** このコンストラクタは三つの入力（ [P]、[Q] と名付けられた
    命題に加え、[P] の根拠）を引数にとり、[P /\ Q] の根拠を返します。
    次に、[or_intror] の型を見てみましょう。 *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(*  It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)
(** ほとんど [or_introl] と同じように見えますが、[P] ではなく [Q] の
    根拠が要求されています。
 *)

(*  Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for! -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)
(** 直観的には、命題 [P \/ Q] に根拠を与える方法は二つあることがわかります。

    - [P] の根拠を与える。（そしてそれが [P] の根拠であることを伝える。
    これがコンストラクタ [or_introl] の機能です）か、

    - [Q] の根拠をコンストラクタ [or_intror] に与える。 *)

(* Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)
(**  [P \/ Q] は二つのコンストラクタを持っているので、 [P \/ Q] の形の仮定に
    [inversion] を適用すると二つのサブゴールが生成されます。
 *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". apply or_intror. apply HP.
    Case "left". apply or_introl. apply HQ.  Qed.

(*  From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)
(** 次のように、[apply or_introl] 、 [apply or_intror] の代わりに [left] 、
     [right] という短縮版のタクティックを使うこともできます。
 *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "right". right. apply HP.
    Case "left". left. apply HQ.  Qed.

(*  **** Exercise: 2 stars, optional (or_commut'') *)
(** **** 練習問題: ★★ optional (or_commut'') *)

(*  Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)
(** [or_commut] の証明オブジェクトがどのようになるか、書き出してみて
    ください。（ただし、定義済みの証明オブジェクトを [Print] を使って
    見てみたりしないこと。）
 *)

(* FILL IN HERE *)
(** [] *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(*  **** Exercise: 2 stars, recommended (or_distributes_over_and_2) *)
(** **** 練習問題: ★★, recommended (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (or_distributes_over_and) *)
(** **** 練習問題: ★ (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(*  ** Relating [/\] and [\/] with [andb] and [orb] *)
(** ** [/\] 、 [\/] の[andb] 、[orb] への関連付け *)

(*  We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are obviously analogs, in some sense, of the logical connectives
    [/\] and [\/].  This analogy can be made more precise by the
    following theorems, which show how to translate knowledge about
    [andb] and [orb]'s behaviors on certain inputs into propositional
    facts about those inputs. *)
(** 我々はすでに、Coqの計算における型([Type]) と論理の命題 ([Prop]) との
    類似性について見てきました。ここではもう一つ、bool 型を扱う [andb] と
    [orb] が、[/\] と [\/] とのつながりともいうべきある種の類似性を
    持っていることに触れましょう。
    この類似性は、次の定理を見ればもっとはっきりします。これは、
    [andb] や [orb] が、ある入力に対する振る舞いを、その入力に対する命題に
    どのように変換するかを示したものです。
 *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(*  **** Exercise: 1 star (bool_prop) *)
(** **** 練習問題: ★ (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################### *)
(*  * Falsehood *)
(** * 偽であるということ *)

(*  Logical falsehood can be represented in Coq as an inductively *)
(** 論理学でいうところの「偽」は、Coqでは「帰納的に定義されてはいるが
    コンストラクタを一つも持たない命題」として定義されています。
 *)

Inductive False : Prop := .

(*  Intuition: [False] is a proposition for which there is no way
    to give evidence. *)
(** 直観的な理解: [False] は、根拠を示す方法を一つも持たない命題 *)

(*  **** Exercise: 1 star (False_ind_principle) *)
(** **** 練習問題: ★ (False_ind_principle) *)
(*  Can you predict the induction principle for falsehood? *)
(** 「偽」に関する帰納法の原理を何か思いつくことができますか？ *)

(* Check False_ind. *)
(** [] *)

(*  Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)
(** [False] にはコンストラクタがないので、[False] の意味するところのものを
    反転（invert）してもサブゴールが生成されません。このことはつまり、
    「偽」からはどんなゴールも証明できる、ということです。
 *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.  Qed.

(*  How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)
(** これはどういうことでしょうか？ [inversion] タクティックは仮定 [contra] を
    その取りうるケースに分解し、それぞれにサブゴールを生成します。ここで
     [contra] が [False] の根拠となっているため、そこから取りうるケースは
     存在しません。このため、証明に値するサブゴールがなくなり、そこで
     証明が終わってしまうのです。
 *)

(*  Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)
(** 逆に、[False] を証明する唯一の方法は、コンテキストに何か
    矛盾がないかを探すことです。*)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(*  Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)
(** 実際、 [False_implies_nonsense] の証明は、特定の意味を持つ証明すべきこと
    を何も持っていないので、任意の [P] に対して簡単に一般化できます。 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

(*  The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)
(** ラテン語の 「_ex falso quodlibet_ 」は、文字通り「偽からはあなたの
    望むものすべてがもたらされる」というような意味です。この定理は、
    「 _principle of explosion_ 」としても知られています。 *)

(* #################################################### *)
(*  ** Truth *)
(** ** 真であるということ *)

(*  Since we have defined falsehood in Coq, we might wonder whether it
    is possible to define truth in the same way.  Naturally, the
    answer is yes. *)
(** Coqで「偽」を定義することができたので、同じ考え方で「真」を定義することが
    できるか、ということが次の関心事になります。もちろん、その答えは「Yes」です。
 *)

(*  **** Exercise: 2 stars (True_induction) *)
(** **** 練習問題: ★★ (True_induction) *)
(*  Define [True] as another inductively defined proposition.  What
    induction principle will Coq generate for your definition?  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.  Alternatively, you may find it easiest
    to start with the induction principle and work backwards to the
    inductive definition.) *)
(** [True] を、帰納的な命題として定義しなさい。あなたの定義に対してCoqはどのような
    帰納法の原理を生成してくれるでしょうか。 （直観的には [True] はただ当たり前のように
    根拠を示される命題であるべきです。代わりに、帰納法の原理から帰納的な定義を逆に
    たどっていくほうが近道だと気づくかもしれません。）
 *)

(* FILL IN HERE *)
(** [] *)

(*  However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)
(** しかしながら、[False] とは違い、広い意味で解釈すると [True] には
    理論的な意味で奇妙なところがあります。ゴールの証明に使うには当たり前すぎ
    （それゆえつまらない）、仮定として有意義な情報を与えてくれないのです。
 *)

(* #################################################### *)
(*  * Negation *)
(** * 否定 *)

(*  The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)
(** 命題 [P] の論理的な補集合というべきものは、 [not P] もしくは短縮形として
     [~P] と表されます。 *)

Definition not (P:Prop) := P -> False.

(*  The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)
(** 直観的には 「もし[P] がtrueでないなら、すべてが（ [False] でさえ）仮定 [P] 
    から導かれるということです。. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(*  It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)
(** Coqで否定を扱えるようになるにはある程度慣れが必要です。
    たとえ何かがどう見ても真に思える場合でも、そのことをCoqに納得させるのは
    最初のうちはなかなか大変です。ウォームアップのつもりで、否定のに関する
    馴染みのある定理を取り上げてみましょう。
 *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(*  **** Exercise: 2 stars, recommended (double_neg_inf) *)
(** **** 練習問題: ★★, recommended (double_neg_inf) *)
(*  Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)
(** [double_neg] の非形式的な証明を書きなさい。: 


   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   [] *)

(*  **** Exercise: 2 stars, recommended (contrapositive) *)
(** **** 練習問題: ★★, recommended (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (not_both_true_and_false) *)
(** **** 練習問題: ★ (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem five_not_even :
  ~ ev 5.
Proof.
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(*  **** Exercise: 1 star ev_not_ev_S *)
(** **** 練習問題: ★ ev_not_ev_S *)
(*  Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)
(** 定理 [five_not_even] は、「５は偶数ではない」というようなとても当たり前の
    事実を確認するものです。今度はもう少し面白い例です。 *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H. (* not n! *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 1 star (informal_not_PNP) *)
(** **** 練習問題: ★ (informal_not_PNP) *)
(*  Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)
(** 命題 [forall P : Prop, ~(P /\ ~P)] の形式的でない証明を（英語で）書きなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  Note that some theorems that are true in classical logic
    are _not_ provable in Coq's "built in" constructive logic... *)
(** このうちいくつかは、古典論理ではtrueと判断できるにもかかわらず、Coqに組み込まれた機能だけでは
    証明できないものがあるので注意が必要です。
 *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for [P]. *)
  (* どうなっているのでしょうか？ [P] の証明に必要な根拠をどうしても編み出すことができません。 *)
  Admitted.

(*  **** Exercise: 5 stars, optional (classical_axioms) *)
(** **** 練習問題: ★★★★★, optional (classical_axioms) *)
(* For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)
(**  さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を
    取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられている
    もの（Coqにビルトインされている構成的論理の対極にあるもの）です。
    これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、
    矛盾なく「証明されていない公理」として道具に加えることができます。
    これら五つの命題が等価であることを証明しなさい。 *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
(** [] *)

(* ########################################################## *)
(*  ** Inequality *)
(** ** 不等であるということ*)

(*  Saying [x <> y] is just the same as saying [~(x = y)]. *)
(** [x <> y] というのは、[~(x = y)] と同じことです。 *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(*  Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)
(** 不等性は、その中に「否定」を含んでいるため、やはりその扱いには
    ある程度の慣れが必要です。ここで一つ有用なトリックをお見せしましょう。
    もし、証明すべきゴールがあり得ない式（例えば[false = true]というような文）
    であった場合は、[ex_falso_quodlibet] という補題をapplyで適用すると、ゴールを
    [False]にすることができます。このことを覚えておけば、コンテキストの中の [~P]
    という形の仮定を使うことがとても簡単になります。特に、[x<>y] という形の仮定の
    場合はに有用です。 *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

(*  **** Exercise: 2 stars, recommended (not_eq_beq_false) *)
(** **** 練習問題: ★★, recommended (not_eq_beq_false) *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars, optional (beq_false_not_eq) *)
(** **** 練習問題: ★★, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ############################################################ *)
(*  * Existential Quantification *)
(** * 存在量化子 *)

(*  Another critical logical connective is _existential
    quantification_.  We can capture what this means with the
    following definition: *)
(** もう一つの論理的接続詞は、存在量化子（ _existential
    quantification_ ）です。これは、次のような定義でその意味を
    とらえることができます。 *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(*  That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P].

    For example, consider this existentially quantified proposition: *)

(** この [ex] は、型引数 [X] とそれに関する属性 [P] によって決まる命題です。
    「 [P] を満たす [x] が存在する」という主張に根拠を与えるため、
    ある特定の値 [x] （「証拠」と呼ぶことにします）を具体的に示すことで
     [P x] の根拠を得ることができます。つまりこれは、 [x] が性質  [P] を
     持っていることの根拠です。

    例として、このような存在量化子を持つ命題を見てみましょう。: *)

Definition some_nat_is_even : Prop :=
  ex nat ev.

(*  To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)
(** この、命題を証明するためには、証拠として特定の値（この場合4）を
    与え、それが偶数である根拠を示す必要があります。 
 *)

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(*  Coq's notation definition facility can be used to introduce
    more familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)
(** Coqの容易な表記法の定義は、存在量化された命題を記述するための、より
    馴染みやすい表記を、ビルトインされたを全称量化子と同レベルで実現しています。
    そのおかげで、「偶数となる自然数が存在する」ことを示す命題を [ex nat ev] と
    書く代わりに、たとえば [exists x:nat, ev x] のように書くことができます。
    （これを理解するためにCoqの「表記法」がどのように作用しているかを完全に
    理解しないといけない、ということではありません。）
 *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(*  We can use the same set of tactics as always for
    manipulating existentials.  For example, if to prove an
    existential, we [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)
(** 存在を示す必要がある場合には、だいたいいつも同じようなタクティックの
    組み合わせが使われます。例えば、ある値の存在を証明する場合には、その値を
    コンストラクタ [ex_intro] に [apply] すればいいのです。[ex_intro] の前提
    はその結論に現れないうような変数（これが「証拠」となります）を必要とするため、
    [apply] を使用する際にはその値をきちんと提示することが必要になります。 *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.  Qed.

(*  Note, again, that we have to explicitly give the witness. *)
(** もう一度書きますが、ここでは具体的な値を証拠として用意する必要があります。 *)

(*  Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)
(** [apply ex_intro with (witness:=e)] と書く代わりに、短縮形として [exists e]
    と記述することもできます。どちらも同じ意味です。 *)

Example exists_example_1' : exists n,
     n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.  Qed.

(*  Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
(** 逆に、コンテキストに置かれた仮定の中に存在を示すものがある場合は、
    それを [inversion] タクティックで取り除くことができます。
    変数に名前を付けるため [as...] パターンを使っていることに注目
    してください。Coqはそれを「証拠」につける名前とし、仮定が証拠を保持する
    根拠をそこから得ます。 （名前をきちんと選ばないと、Coqはそれを単なる
    証拠としか考えることができず、その先の証明で混乱してしまいます。）
 *)

Theorem exists_example_2 : forall n,
     (exists m, n = 4 + m) ->
     (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.  Qed.

(*  **** Exercise: 1 star (english_exists) *)
(** **** 練習問題: ★ (english_exists) *)
(*  In English, what does the proposition
[[
      ex nat (fun n => ev (S n))
]]
    mean? *)
(** 英語では、以下の命題は何を意味しているでしょうか？
[[
      ex nat (fun n => ev (S n))
]]
 *)

(* FILL IN HERE *)

(*  Complete the definition of the following proof object: *)
(** 次の証明オブジェクトの定義を完成させなさい *)

Definition p : ex nat (fun n => ev (S n)) :=
(* FILL IN HERE *) admit.
(** [] *)

(*  **** Exercise: 1 star (dist_not_exists) *)
(** **** 練習問題: ★ (dist_not_exists) *)
(*  Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)
(** "全ての [x] について[P] が成り立つ" ということと " [P] を満たさない [x] は
    存在しない" ということが等価であることを証明しなさい。 *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, optional (not_exists_dist) *)
(** **** 練習問題: ★★★, optional (not_exists_dist) *)
(*  The other direction requires the classical "law of the excluded
    middle": *)
(** 反対の向きは、古典論理の「排中律（law of the excluded middle）」が
    必要です。 *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 2 stars (dist_exists_or) *)
(** **** 練習問題: ★★ (dist_exists_or) *)
(*  Prove that existential quantification distributes over
    disjunction. *)
(** 存在量化子が論理和において分配法則を満たすことを証明しなさい。 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* Print dist_exists_or. *)



(* ###################################################### *)
(*  * Equality *)
(** * 等しいということ（同値性） *)

(*  Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (We enclose the definition in a
    module to avoid confusion with the standard library equality,
    which we have used extensively already.) *)
(** Coqには、等価という関係すら組み込まれていませんから、次のように帰納的に定義
    してやります（ここではこれまで散々使った標準ライブラリでの定義と衝突すること
    を防ぐために、モジュールの中で定義することにします。） *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

(*  Standard infix notation (using Coq's type argument synthesis): *)
(** 次に定義するのは、標準的な中置記法です（Coqの型引数合成を使用しています）。 *)

Notation "x = y" := (eq _ x y)
                    (at level 70, no associativity) : type_scope.

(*  This is a bit subtle.  The way to think about it is that, given a
    set [X], it defines a _family_ of propositions "[x] is equal to
    [y]," indexed by pairs of values ([x] and [y]) from [X].  There is
    just one way of constructing evidence for members of this family:
    applying the constructor [refl_equal] to a type [X] and a value [x
    : X] yields evidence that [x] is equal to [x]. *)
(** この例は少し難解かもしれません。これがどういうものかを考えると、
    集合 [X] が与えられると、「集合 [X] に属する値 ([x] and [y]) にインデックス
    された、[x] は [y] に等しい」というような命題の _集団_ を定義してくれる
    ということです。この集団に属する命題に根拠を与えるためには、一つの
    方法しかありません。それは、コンストラクタ [refl_equal] に型 [X] とその値
    [x : X] を適用し、[x] が [x] と等しいという根拠を生成することです。
 *)
(*  Here is a slightly different definition -- the one that actually
    appears in the Coq standard library. *)
(** 次の定義は少し違った形になっています。 -- Coqの標準ライブラリでは
    こちらの定義が採用されています。 *)

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y)
                     (at level 70, no associativity) : type_scope.

(*  **** Exercise: 3 stars, optional (two_defs_of_eq_coincide) *)
(** **** 練習問題: ★★★, optional (two_defs_of_eq_coincide) *)
(*  Verify that the two definitions of equality are equivalent. *)
(** これら二つの定義が等価であることを確認しなさい。 *)

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  The advantage of the second definition is that the induction
    principle that Coq derives for it is precisely the familiar
    principle of _Leibniz equality_: what we mean when we say "[x] and
    [y] are equal" is that every property on [P] that is true of [x]
    is also true of [y]. *)
(** 二つ目の定義の優れたところは、Coqが生成する帰納法の原理が正確に
    「ライプニッツの同値関係（ _Leibniz equality_ ）」と親和している点です。
    それはつまり、「[x] と [y] が等しいということは、 任意の命題 [P] が
     [x] でtrueとなるならば [y] でもtrueとなる」ということです。
 *)

Check eq'_ind.
(* ===>  forall (X : Type) (x : X) (P : X -> Prop),
             P x -> forall y : X, x =' y -> P y *)

(*  One important consideration remains.  Clearly, we can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes.
    Indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval simpl], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.

    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)
(** 一つ大事なことが残っています。確かに [refl_equal] は [2 = 2] というような
    証明に根拠を与えることに使えます。 [1 + 1 = 2] はどうでしょうか？
    答えは Yes です。実際、これらは証明としてはほとんど同じようなものだと
    言えます。 その理由は Coq が二つの式がシンプルな計算ルールによって交換可能である
    ことをを示し、それを"同値である"として処理しているからです。
    このルールは [Eval simpl] と同じものです。ただしこれには、
    関数適用の評価、定義のインライン化、[match] の簡約が含まれています。

    タクティックを使った同値性の証明では、 [simpl] を使うことで暗黙的にこの
    交換ルールに触れています（[reflexivity] のような他のタクティックでも、明示的に、
    もしくは暗黙的に含まれています）。このことは、次のような明示的な証明オブジェクトで
    確認することができます。
 *)

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.
Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

(* ####################################################### *)
(* ** Inversion, Again *)
(** ** Inversion 再び *)

(*  We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,

      - adds these equalities to the context of the subgoal, and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal.

   _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)
(** これまでにも [inversion] が等値性にからむ仮定や帰納的に定義された命題に対して
    使われるところを見てきました。今度もやることは変わりませんが、もう少し近くまで
    寄って [inversion] の振る舞いを観察してみましょう。

    一般的に [inversion] タクティックは、

    - 帰納的に定義された型 [P] の命題 [H] をとる。

    - その型 [P] の定義にある各コンストラクタ [C] が、

      - [H] が [C] から成っていると仮定するような新しいサブゴールを作る。

      - [C] の引数（前提）を、追加の仮定としてサブゴールのコンテキストに加える。

      - [C] の結論（戻り値の型）を現在のゴールとmatchして、 [C] を適用できるような一連の等式算出する。

      - そしてこれらの等式をサブゴールのコンテキストに加えてから、

      - もしこの等式が充足可能でない場合（[S n = O] というような式を含むなど）は、
        即座にサブゴールを解決する。

   例 :  [or] で構築された仮定を反転（ invert ）すると、[or] に二つのコンストラクタが
   あるため二つのサブゴールが生成されます。コンストラクタ ([P \/ Q]) の結果
   （戻り値の型）は [P] や [Q] の形からくる制約を付けません。そのため追加の等式が
   サブゴールのコンテキストに加えられることはありません。


   例 : [and] で構築された仮定を反転（ invert ）すると、[and] にはコンストラクタが
   一つしかないため、サブゴールも一つしか生成されません。やはり、コンストラクタ 
   ([P /\ Q]) の結果（戻り値の型）は [P] や [Q] の形からくる制約を付けず、追加の等式が
   サブゴールのコンテキストに加えられることはありません。このコンストラクタは引数を二つ
   とりますが、それらはサブゴールのコンテキストに現れます。


   例 : [eq] で構築された仮定を反転（ invert ）すると、これにもやはりコンストラクタが
   一つしかないため、サブゴールも一つしか生成されません。しかしこの場合 
   コンストラクタ [refl_equal] の形は我々にもう少し情報を与えてくれます。
   それは、[eq] の二つの引数は同じでなければならないという点です。
    [inversion] タクティックはこの事実をコンテキストに加えてくれます。
 *)

(* ####################################################### *)
(*  * Relations as Propositions *)
(** * 命題としての関係 *)

(*  A proposition parameterized numbers (such as [ev]) can be
    thought of as a _property_ -- i.e., it defines a subset of [nat],
    namely those numbers for which the proposition is provable.  In
    the same way, a two-argument proposition can be thought of as a
    _relation_ -- i.e., it defines a set of pairs for which the
    proposition is provable. *)
(** [ev] のように数値でパラメータ化された命題は、属性（ _property_ ）と
    見なすこともできます。つまり、それに属する値についてその命題が証明可能である
    ような [nat] の部分集合の定義と見ることができるということです。
    同様に、引数（パラメータ）を二つ持つ命題は、その二つの「関係」を表していると
    考えられます。つまり、その命題について証明可能な値のペアの集合の定義、
    というわけです。
 *)

Module LeFirstTry.

(*  We've already seen an inductive definition of one
    fundamental relation: equality.  Another useful one is the "less
    than or equal to" relation on numbers: *)
(** これまでにもすでに、帰納的に定義された関係の基本的なものは出てきていました。
    等値性がそれです。他にも、よく使われるものとして「等しいかまたは小さい」
    という関係があります。
 *)

(*  This definition should be fairly intuitive.  It says that
    there are two ways to give evidence that one number is less than
    or equal to another: either observe that they are the same number,
    or give evidence that the first is less than or equal to the
    predecessor of the second. *)
(** この定義はかなり直観的なものになります。これは、ある数値がもう一つの
    数値より小さいかまたは等しい、ということを示すには二つの方法があることを
    示しています。一つはそれらが同じ数であるかどうかを確認すること。もう
    一つは最初の数が、二つ目の数の一つ前の数より小さいかまたは等しい、
    ということの根拠を得ることです。
 *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

(*  This is a reasonable definition of the [<=] relation, but we
    can streamline it a little by observing that the left-hand
    argument [n] is the same everywhere in the definition, so we can
    actually make it a "general parameter" to the whole definition,
    rather than an argument to each constructor.  This is similar to
    what we did in our second definition of the [eq] relation,
    above. *)
(** これはこれで [<=] という関係の妥当な定義だと言えます。しかし少し観察してみると
    定義の左側のに現れる [n] は全て同じだということがわかります。ということは、
    個々のコンストラクタにではなく定義全体に全称量化子を使うことが
    できるということです。このことは先程 [eq] という関係の二番目の定義でやったことと
    同じです。
 *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(*  The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle.
    (The same was true of our second version of [eq].) *)
(** 少し対称性が損なわれたようにも見えますが、この二番目の定義の方がいいのです。
    なぜでしょうか？それは、こちらのほうがよりシンプルな帰納法の原理を
    生成してくれるからです（ [eq] の二番目の定義にも同じことが言えます）。
 *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(*  By contrast, the induction principle that Coq calculates for the
    first definition has a lot of extra quantifiers, which makes it
    messier to work with when proving things by induction.  Here is
    the induction principle for the first [le]: *)
(** 一方、最初の定義に Coq が生成する帰納法の原理には、もっと多くの量化子が
    含まれることになります。これでは、帰納法を使った証明がごちゃごちゃしてしまいます。
    これが [le] の最初の定義で生成された帰納法の原理です。
 *)

(* le_ind :
     forall P : nat -> nat -> Prop,
     (forall n : nat, P n n) ->
     (forall n m : nat, le n m -> P n m -> P n (S m)) ->
     forall n n0 : nat, le n n0 -> P n n0 *)

(*  Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in the previous chapter.  We can [apply] the constructors to
    prove [<=] goals (e.g., to show that [3<=3] or [3<=6]), and we can
    use tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)
(** コンストラクタ [le_n] と [le_S] を使った [<=] にからむ証明は、前章の [eq] が
    そうであったように、属性についての証明のいくつかのパターンに倣っています。
    [<=] の形をしたゴール（例えば [3<=3] や [3<=6] など）に、そのコンストラクタを
    apply することができますし、inversion のようなタクティックを使って
    （[~(2 <= 1)] の証明をしようとする際のように） コンテキストに [<=] を含む
    仮定から情報を抽出することもできます。
 *)

(*  Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations. *)
(** 
    ここで、定義が正しくなされているのかのチェックをしてみましょう。（注意して
    欲しいのは、ここでやることが、最初のレクチャーで書いてもらった、ある種の
    シンプルな「ユニットテスト」のようなものですが、今回のものは以前のものと
    ちょっと違います。今回のものには、[simpl] や [reflexivity] はほとんど
    役に立ちません。簡約だけで証明できるようなものではないからです。
 *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  ~ (2 <= 1).
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H1.  Qed.

(*  The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)
(** 「より小さい」という関係（ [n < m] ）は、[le] を使って定義できます。 *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(*  Here are a few more simple relations on numbers: *)
(** 他にも、数値の関係についていくつか見てみましょう。 *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(*  **** Exercise: 2 stars, recommended (total_relation) *)
(** **** 練習問題: ★★, recommended (total_relation) *)
(*  Define an inductive relation [total_relation] that holds
    between every pair of natural numbers. *)
(** 二つの自然数のペア同士の間に成り立つ帰納的な関係 [total_relation] を
    定義しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 2 stars (empty_relation) *)
(** **** 練習問題: ★★ (empty_relation) *)
(*  Define an inductive relation [empty_relation] (on numbers)
    that never holds. *)
(** 自然数の間では決して成り立たない関係 [empty_relation] を帰納的に
    定義しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 3 stars, recommended (R_provability) *)
(** **** 練習問題: ★★★, recommended (R_provability) *)
Module R.
(*  We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)
(** 次は三つや四つの値の間に成り立つ関係を同じように定義してみましょう。
    例えば、次のような数値の三項関係が考えられます。 *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(*  - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(* FILL IN HERE *)
[]
*)
(**  - 次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
      - [R 1 1 2]
      - [R 2 2 6]

    - この関係 [R] の定義からコンストラクタ [c5] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。

    - この関係 [R] の定義からコンストラクタ [c4] を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。


(* FILL IN HERE *)
[]
*)

(*  **** Exercise: 3 stars, optional (R_fact) *)
(** **** 練習問題: ★★★, optional (R_fact) *)
(*  State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)
(** 関係 [R] の、等値性に関する特性をあげ、それを証明しなさい。 それは、
    もし [R m n o] が true なら [m] についてどんなことが言えるでしょうか？
    [n] や [o] についてはどうでしょうか？その逆は？
 *)

(* FILL IN HERE *)
(** [] *)

End R.

(*  **** Exercise: 3 stars, recommended (all_forallb) *)
(** **** 練習問題: ★★★, recommended (all_forallb) *)
(*  Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)
(** リストに関する属性 [all] を定義しなさい。それは、型 [X] と属性 [P : X -> Prop]
    をパラメータとし、 [all X P l]  が「リスト [l] の全ての要素が
    属性 [P} を満たす」とするものです。
 *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  (* FILL IN HERE *)
.

(*  Recall the function [forallb], from the exercise
[forall_exists_challenge] in [Poly.v]: *)
(** [Poly.v] の練習問題 [forall_exists_challenge] に出てきた関数 [forallb] 
    を思い出してみましょう。
 *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(*  Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
(** 属性 [all] を使って関数 [forallb] の仕様を書き、それを満たすことを証明
    しなさい。できるだけその仕様が厳格になるようにすること。

    関数 [forallb] の重要な性質が、あなたの仕様から洩れている、ということは
    ありませんか？ *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 4 stars, optional (filter_challenge) *)
(** **** 練習問題: ★★★★, optional (filter_challenge) *)
(*  One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,
[[
    [1,4,6,2,3]
]]
    is an in-order merge of
[[
    [1,6,2]
]]
    and
[[
    [4,3].
]]
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)
(** Coq の主な目的の一つは、プログラムが特定の仕様を満たしていることを
    証明することです。それがどういうことか、[filter] 関数の定義が仕様を満たすか証明
    してみましょう。まず、その関数の仕様を非形式的に書き出してみます。

    集合 [X] と関数 [test: X->bool]、リスト[l] とその型 [list X] を想定する。
    さらに、[l] が二つのリスト [l1] と [l2] が順序を維持したままマージされたもので、
    リスト [l1] の要素はすべて [test] を満たし、 [l2] の要素はすべて満たさないと
    すると、[filter test l = l1] が成り立つ。

    リスト [l] が [l1] と [l2] を順序を維持したままマージしたものである、とは、
    それが [l1] と [l2] の要素をすべて含んでいて、しかも 互いに入り組んではいても
    [l1] 、 [l2] の要素が同じ順序になっている、ということです。例えば、

[[
    [1,4,6,2,3]
]]
    は、以下の二つを順序を維持したままマージしたものです。
[[
    [1,6,2]
]]
    と、
[[
    [4,3]
]]
    課題は、この仕様をCoq の定理の形に書き直し、それを証明することです。
    （ヒント：まず、一つのリストが二つのリストをマージしたものとなっている、
    ということを示す定義を書く必要がありますが、これは帰納的な関係であって、
    [Fixpoint] で書くようなものではありません。）
 *)

(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 5 stars, optional (filter_challenge_2) *)
(** **** 練習問題: ★★★★★, optional (filter_challenge_2) *)

(*  A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)
(** [filter] の振る舞いに関する特性を別の切り口で表すとこうなります。
    「[test] の結果が [true] なる要素だけでできた、リスト [l] の
    すべての部分リストの中で、[filter test l] が最も長いリストである。」
    これを形式的に記述し、それを証明しなさい。
 *)
    
(* FILL IN HERE *)
(** [] *)

(*  **** Exercise: 4 stars, optional (no_repeats) *)
(** **** 練習問題: ★★★★, optional (no_repeats) *)
(*  The following inductively defined proposition... *)
(** 次の、帰納的に定義された命題は、 *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(*  ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l].

    Here's a pair of warm-ups about [appears_in].
*)
(** 値 [a] がリスト [l] の要素として少なくとも一度は現れるということを
    言うための、精確な方法を与えてくれます。

    次の二つは[appears_in] に関するウォームアップ問題です。
*)

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)
(** では、 [appears_in] を使って命題 [disjoint X l1 l2] を定義してください。
    これは、型 [X] の二つのリスト [l1] 、 [l2] が共通の要素を持たない場合
    にのみ証明可能な命題です。
 *)
 
(* FILL IN HERE *)

(*  Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)
(** 次は、 [appears_in] を使って帰納的な命題 [no_repeats X l] を定義して
    ください。これは, 型 [X] のリスト [l] の中のどの要素も、他の要素と
    異なっている場合のみ証明できるような命題です。例えば、 
    [no_repeats nat [1,2,3,4]] や [no_repeats bool []] は証明可能ですが、 
    [no_repeats nat [1,2,1]] や [no_repeats bool [true,true]] は証明
    できないようなものです。
 *)

(* FILL IN HERE *)

(*  Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)
(** 最後に、[disjoint]、 [no_repeats]、 [++] （リストの結合）の三つを使った、
    何か面白い定理を考えて、それを証明してください。
 *)

(* FILL IN HERE *)
(** [] *)

(* ######################################################### *)
(*  ** Digression: More Facts about [<=] and [<] *)
(** ** 少し脱線: [<=] と [<] についてのさらなる事実*)

(*  Let's pause briefly to record several facts about the [<=]
    and [<] relations that we are going to need later in the
    course.  The proofs make good practice exercises. *)
(** ここで少し新しいことを中断して、 [<=] や [<] といった関係についての
    事実をいくつか書き溜めていくことにしましょう。それらはここから先に進む際に
    必要になってくるばかりでなく、その証明自体がとてもよい練習問題に
    なってくれます。 *)

(*  **** Exercise: 2 stars, optional (le_exercises) *)
(** **** 練習問題: ★★, optional (le_exercises) *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.  generalize dependent n.  induction m.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(*  **** Exercise: 3 stars, recommended (nostutter) *)
(** **** 練習問題: ★★★, recommended (nostutter) *)
(*  Formulating inductive definitions of predicates is an important skill
    you'll need in this course.

    Try to solve this exercise without any help at all.   If you do receive
    assistance from anyone, please say so specifically in a comment.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.)
*)
(** 述語の帰納的な定義を定式化できるようになるというのは、これから先の学習に
    必要なスキルになってきます。

    この練習問題は、何の力も借りず自力で解いてください。
    もし誰かの力を借りてしまった場合は、そのことをコメントに書いておいて
    ください。

    同じ数値が連続して現れるリストを "stutters" （どもったリスト）と
    呼ぶことにします。述語 "[nostutter mylist]" は、 [mylist]  が「どもった
    リスト」でないことを意味しています。[nostutter] の帰納的な定義を記述しなさい。
    （これは以前の練習問題に出てきた [no_repeats] という述語とは異なるものです。
    リスト [1,4,1] は repeats ではありますが stutter ではありません。）
 *)
Inductive nostutter:  list nat -> Prop :=
 (* FILL IN HERE *)
.

(*  Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.

    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)
(** できた定義が、以下のテストを通過することを確認してください。
    通過できないものがあったら、定義を修正してもかまいません。
    あなたの書いた定義が、正しくはあるけれど私の用意した模範解答と異なって
    いるかもしれません。その場合、このテストを通過するために別の
    証明を用意する必要があります。

    以下の Example にコメントとして提示された証明には、色々な種類の 
    [nostutter] の定義に対応できるようにするため、まだ説明していない
    タクティックがいくつか使用されています。 まずこれらのコメントをはずしただけの
    状態で確認できればいいのですが、もしそうしたいなら、これらの証明をもっと
    基本的なタクティックで書き換えて証明してもかまいません。
 *)
Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) Admitted.
(*
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
(* FILL IN HERE *) Admitted.
(*
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(*  **** Exercise: 4 stars, optional (pigeonhole principle) *)
(** **** 練習問題: ★★★★, optional (pigeonhole principle) *)
(*  The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)
(** 「鳩の巣定理（ "pigeonhole principle" ）」は、「数えるあげる」という
    ことについての基本的な事実を提示しています。「もし [n] 個の鳩の巣に
    [n] 個より多い数のものを入れようとするなら、どのような入れ方をしても
    いくつかの鳩の巣には必ず一つ以上のものが入ることになる。」というもので、
    この、数値に関する見るからに自明な事実を証明するにも、なかなか自明とは言えない
    手段が必要になります。我々は既にそれを知っているのですが...
 *)

(*  First a pair of useful lemmas... (we already proved this for lists
    of naturals, but not for arbitrary lists.) *)
(** まず、補題を二つほど証明しておきます。（既に数値のリストについては
    証明済みのものですが、任意のリストについてはのものはまだないので）
 *)

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *) Admitted.

(*  Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)
(** そして、述語 [repeats] の定義をします（以前の練習問題 [no_repeats] に
    類似したものです）。それは [repeats X l] が、「 [l] の中に少なくとも一組の
    同じ要素（型 [X] の）を含む」という主張となるようなものです。
 *)

Inductive repeats {X:Type} : list X -> Prop :=
  (* FILL IN HERE *)
.

(*  Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)
(** この「鳩の巣定理」を定式化する方法を一つ挙げておきましょう。
    リスト [l2] が鳩の巣に貼られたラベルの一覧を、リスト [l1] はそのラベルの、
    アイテムへの割り当ての一覧を表しているとします。もしラベルよりも沢山の
    アイテムがあったならば、少なくとも二つのアイテムに同じラベルが貼られている
    ことになります。おそらくこの証明には「排中律（ [excluded_middle] ）」が
    必要になるでしょう。 *)

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle ->
  (forall x, appears_in x l1 -> appears_in x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.  intros X l1. induction l1.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ##################################################### *)
(*  * Optional Material *)
(** * 選択課題 *)

(* ################################################### *)
(*  ** Induction Principles for [/\] and [\/] *)
(** ** [/\] や [\/] のための帰納法の原理 *)

(*  The induction principles for conjunction and disjunction are a
    good illustration of Coq's way of generating simplified induction
    principles for [Inductive]ly defined propositions, which we
    discussed in the last chapter.  You try first: *)
(** 論理積（連言）や論理和（連言）に関する帰納法の原理は、帰納的に定義された
    命題に対して簡約された帰納法の原理を Coq が生成する方法をとてもよく示しています。
    これについては最後の章でお話しします。とりあえずこれに挑戦してみてください。
 *)

(*  **** Exercise: 1 star (and_ind_principle) *)
(** **** 練習問題: ★ (and_ind_principle) *)
(*  See if you can predict the induction principle for conjunction. *)
(** 連言（ conjunction ）についての帰納法の原理を予想して、確認しなさい。 *)

(* Check and_ind. *)
(** [] *)

(*  **** Exercise: 1 star (or_ind_principle) *)
(** **** 練習問題: ★ (or_ind_principle) *)
(*  See if you can predict the induction principle for disjunction. *)
(** 選言（ disjunction ）についての帰納法の原理を予想して、確認しなさい。 *)

(* Check or_ind. *)
(** [] *)

Check and_ind.

(*  From the inductive definition of the proposition [and P Q]
[[
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
    we might expect Coq to generate this induction principle
[[
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
]]
    but actually it generates this simpler and more useful one:
[[
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
]]
    In the same way, when given the inductive definition of [or P Q]
[[
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
]]
    instead of the "maximal induction principle"
[[
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
]]
    what Coq actually generates is this:
[[
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]]
*)
(** 命題 [and P Q] の帰納的な定義から、 
[[
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
]]
    我々は Coq がこのような帰納法の原理を生成することを期待します。
[[
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
]]
    しかし実際には、もっとシンプルで使いやすいものが生成されます。
[[
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
]]
    同様に、 [or P Q] の帰納的な定義が与えられると、
[[
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
]]
    以下のような、原則通りの帰納法の原理を制する代わりに、
[[
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
]]
    Coq はこのような帰納法の原理が生成されます。
[[
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]]
*)

(* ######################################################### *)
(*  ** Explicit Proof Objects for Induction *)
(** ** 帰納法のための明白な証明オブジェクト *)


(*  Although tactic-based proofs are normally much easier to
    work with, the ability to write a proof term directly is sometimes
    very handy, particularly when we want Coq to do something slightly
    non-standard.  *)
(** タクティックを使った証明は一般に簡単に済むことが多いですが、証明式を
    直接書いてしまえるなら、そうしたほうが簡単な場合もあります。特に、
    Coq にちょっとだけ変わった方法をとらせたい時はそうです。
 *)

(*  Recall the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)
(** [nat] の帰納的な定義からCoqが自動的に生成した自然数に関する帰納法の
    原理を思い出してください。
 *)

(* Check nat_ind. *)
(** ===>
   nat_ind : forall P : nat -> Prop,
      P 0%nat ->
      (forall n : nat, P n -> P (S n)) ->
      forall n : nat, P n  *)

(*  There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)
(** この帰納法についての補題には何のタネも仕掛けもありません。
    これは単に、証明を必要とする Coq の別の補題です。Coq はこれにも
    自動的に証明を生成してくれます。
 *)

Print nat_ind.  Print nat_rect.
(* ===> (after some manual inlining)
   nat_ind =
    fun (P : nat -> Type)
        (f : P 0%nat)
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n as n0 return (P n0) with
            | 0%nat => f
            | S n0 => f0 n0 (F n0)
            end.
*)

(*  We can read this as follows:
     Suppose we have evidence [f] that [P] holds on 0,  and
     evidence [f0] that [forall n:nat, P n -> P (S n)].
     Then we can prove that [P] holds of an arbitrary nat [n] via
     a recursive function [F] (here defined using the expression
     form [Fix] rather than by a top-level [Fixpoint]
     declaration).  [F] pattern matches on [n]:
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0]
         to obtain evidence that [P n0] holds; then it applies [f0]
         on that evidence to show that [P (S n)] holds.
    [F] is just an ordinary recursive function that happens to
    operate on evidence in [Prop] rather than on terms in [Set].

    Aside to those interested in functional programming: You may
    notice that the [match] in [F] requires an annotation [as n0
    return (P n0)] to help Coq's typechecker realize that the two arms
    of the [match] actually return the same type (namely [P n]).  This
    is essentially like matching over a GADT (generalized algebraic
    datatype) in Haskell.  In fact, [F] has a _dependent_ type: its
    result type depends on its argument; GADT's can be used to
    describe simple dependent types like this.

    We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too.  Recall our desire to
    prove that

    [forall n : nat, even n -> ev n].

    Attempts to do this by standard induction on [n] fail, because the
    induction principle only lets us proceed when we can prove that
    [even n -> even (S n)] -- which is of course never provable.  What
    we did earlier in this chapter was a bit of a hack:

    [Theorem even_ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].

    We can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":

 *)
(** ===> (after some manual inlining)
   nat_rect =
    fun (P : nat -> Type)
        (f : P 0%nat)
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n as n0 return (P n0) with
            | 0%nat => f
            | S n0 => f0 n0 (F n0)
            end.
*)
(** これは次のように読めます :
     [P] が 0 の場合に成り立つという根拠 [f] と [forall n:nat, P n -> P (S n)]
     の根拠 [f0] があると仮定します。
     そうすると、 [P] が任意の自然数 [n] で成り立つことを、再帰的に定義された
     関数 [F] （ここでは、トップレベルで使われる [Fixpoint] ではなく、
      [Fix] を使って定義されています）を使って示すことができます。
     [F] は [n] について以下のようなパターンマッチをしています：
      - もし 0 ならば、 [F] は [f] を [P n] が成り立つことの根拠とする。
      - もし [S n0] ならば、[F] は [P n0] が成り立つ根拠を手に入れるために、[n0] を持ってそれ自身を再帰呼び出しする。そうして得た根拠が [f0] に適用され [P (S n)] が成り立つことが示される。
    [F] は、集合 [Set] ではなく、根拠  [Prop] を操作することになっただけの
    普通の再帰的な関数です。

    関数型プログラミングが少し面白くなるような脇道です。もしかするとあなたは
    関数 [F] の [match] が、アノテーション [as n0 return (P n0)] を必要としている
    ことに気づいたかもしれません。それは Coq の型チェッカが二つの [match] の
    枝が、実は同じ型 [P n] を返すことを明確にするために必要なものなのですが、
    これは本質的に Haskell の GADT (generalized algebraic datatype) と同じものです。
    実際、 [F] は依存型（ _dependent_ type ）をしており、その結果の型はその引数に
    依存します。 GADT はこのような単純な依存型を表現する際に使えます。
    
    我々は、 [nat_ind] の証明に使用したこのようなアプローチを、
    標準的でない（ _non-standard_ ）帰納法の原理を証明する際にも使うことができます。
    以前このような証明をしようとしていたことを思い出してください。
    
    [forall n : nat, even n -> ev n].

    これを、通常の [n] に対する帰納法でやろうとしても失敗してしまいます。
    なぜなら、この帰納法の原理は [even n -> even (S n)] を証明しようとする
    時にしかうまく機能してくれないからです。これはもちろん証明不能な命題です。
    このような場合、前の章ではちょっとした小技を使いました。

    [Theorem even_ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].

    これについては、標準的でない帰納法の原理（二つずつ、となるような）を
    定義して証明することで、より良い証明が得られます。
 *)

 Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P (S(S n))) ->
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n:nat) := match n return P n with
                             0 => P0
                           | 1 => P1
                           | S (S n') => PSS n' (f n')
                          end.

(*  Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive (try
     it!).

     The [induction ... using] tactic gives a convenient way to
     specify a non-standard induction principle like this. *)
(** 一度これを手にいれてしまえば、今回のような帰納法の原理を使った
    証明全般にこれを使うことができます。これを補題としてタクティックを
    使うと、さらに直観に反したものになります（試してみてください！）。
     
     [induction ... using] タクティックは、このように標準的でない
     帰納法の原理を取る際に便利です。
 *)

Lemma even_ev' : forall n, even n -> ev n.
Proof.
 intros.
 induction n as [ | |n'] using nat_ind2.
  Case "even 0".
    apply ev_0.
  Case "even 1".
    inversion H.
  Case "even (S(S n'))".
    apply ev_SS.
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H.
Qed.

(* ######################################################### *)
(*  ** The Coq Trusted Computing Base *)
(** ** Coq の信頼できるコンピューティング基盤 *)

(*  One issue that arises with any automated proof assistant is "why
    trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard Correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on.

    There are a few additional wrinkles:

    - Since Coq types can themselves be expressions, the checker must
      normalize these (by using the conversion rules) before
      comparing them.

    - The checker must make sure that [match] expressions are
      _exhaustive_.  That is, there must be an arm for every possible
      constructor.  To see why, consider the following alleged proof
      object:
[[
      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end.
]]
      All the types here match correctly, but the [match] only
      considers one of the possible constructors for [or].  Coq's
      exhaustiveness check will reject this definition.

    - The checker must make sure that each [fix] expression
      terminates.  It does this using a syntactic check to make sure
      that each recursive call is on a subexpression of the original
      argument.  To see why this is essential, consider this alleged
      proof:
[[
          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n.
]]
      Again, this is perfectly well-typed, but (fortunately) Coq will
      reject it. *)
(** ここで一つの疑問が起こってきます。自動化された証明支援系が
    「なぜ信用できるのか？」という疑問です。つまり、これらの実装に
    バグがあるなら、その証明にも疑いを持たざるを得ません。

    このような考えを完全に排除することはできませんが、Coq カリー・ハワード同型対応を
    その基礎に置いているという事実は Coq 自身の強い基礎ともなっています。
    なぜなら、命題は型であり、証明は項であり、まだ証明されていない命題が
    妥当かどうかを調べることは、項の型をチェックする（ _type-checking_ ）ことに
    等しいからです。型チェッカは十分に信頼できるほど小さく率直に書かれた
    プログラムであり、それこそが Coq の「信頼できるコンピューティング基盤」と
    なっています。その「信頼性が必要となる一部のコード」は正確に動き、また
    十分に小さいのです。
    
    型チェッカの役割とはなんでしょうか？その一番の役割は、各々の関数の適用で、
    予想された型と実際の型が一致していることを確認することです。つまり、
     [match] の各枝の式が、帰納的な型のコンストラクタと対応しており、すべてが
     同じ型を返すようになっているか、などです。
    
    しかしこれには若干の弱点もあります。

    - Coq の型はそれ自身が式となっているため、その型チェッカがそれらを比較する前際に、変換ルールに基づいて正規化しなければならない。

    - 型チェッカは、 [match] の式が「尽くされている（_exhaustive_ ）ことを確認しなければならない。つまり、その型ににあるコンストラクタに対応する枝をすべて持っていなければならい。その理由は、次に提示された証明オブジェクトについて考えればわかるはずです。
      
[[
      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end.
]]
      この定義では、型は正しく一致していますが、 [match] が [or] の一方の
      コンストラクタのことしか考えていません。Coq は、このようなケースがないか
      をチェックし、このような定義を拒絶します。

    - 型チェッカは、各 [fix] の式が終了することを確認しなければならない。これは文法レベルで「各々の再帰呼び出しに元々の引数にわたってきた式の部分式が渡されていること」をチェックをすることで実現されている。この理由の本質的なところを理解するために次の証明について考えてください。
[[
          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n.
]]
      やはり、これも型について何も問題はありませんが、残念なことに Coq はこの定義を
      拒絶します。 *)

(*  Note that the soundness of Coq depends only on the correctness of
    this typechecking engine, not on the tactic machinery.  If there
    is a bug in a tactic implementation (and this certainly does
    happen!), that tactic might construct an invalid proof term.  But
    when you type [Qed], Coq checks the term for validity from
    scratch.  Only lemmas whose proofs pass the type-checker can be
    used in further proof developments.  *)
(** Coq の「確実さ」は、タクティックの仕組みではなく、型チェックの仕組みに
    よってもたらされていることに注目してください。もしタクティックの実装に
    バグがあれば（実際にこれはあったことです！）、タクティックは間違った証明
    を構築してしまうでしょう。しかし、[Qed] を入力した時点で、Coq はその正しさを
    １から検証しなおします。型チェッカを通過した補題のみ、その後の証明の
    構築に使える定理となることができるのです。
 *)


