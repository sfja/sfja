(** * Stlc_J: 単純型付きラムダ計算 *)
(* * Stlc: The Simply Typed Lambda-Calculus *)

(* $Date: 2011-06-09 16:11:42 -0400 (Thu, 09 Jun 2011) $ *)


Require Export Types_J.

(* ###################################################################### *)
(* * The Simply Typed Lambda-Calculus *)
(** * 単純型付きラムダ計算 *)

(* The simply typed lambda-calculus (STLC) is a tiny core calculus
    embodying the key concept of _functional abstraction_, which shows
    up in pretty much every real-world programming language in some
    form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as above when formalizing
    of this calculus (syntax, small-step semantics, typing rules) and
    its main properties (progress and preservation).  The new
    technical challenges (which will take some work to deal with) all
    arise from the mechanisms of _variable binding_ and
    _substitution_. *)
(** 単純型付きラムダ計算(Simply Typed Lambda-Calculus, STLC)は、
    関数抽象(_functional abstraction_)を具現する、小さな、核となる計算体系です。
    関数抽象は、ほとんどすべての実世界のプログラミング言語に何らかの形
    (関数、手続き、メソッド等)で現れます。

    ここでは、この計算体系(構文、スモールステップ意味論、
    型付け規則)とその性質(進行と保存)の形式化を、
    これまでやったのとまったく同じパターンで行います。
    (扱うためにいくらかの作業が必要になる)新しい技術的挑戦は、
    すべて変数束縛(_variable binding_)と置換(_substitution_)の機構から生じます。*)

(* ###################################################################### *)
(* ** Overview *)
(** ** 概観 *)

(* The STLC is built on some collection of _base types_ -- booleans,
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
(** STLC は基本型(_base types_)の何らかの集まりの上に構成されます。
    基本型はブール型、数値、文字列などです。
    実際にどの基本型を選択するかは問題ではありません。
    どう選択しても、言語の構成とその理論的性質はまったく同じように導かれます。
    これから、簡潔にするため、しばらくは[Bool]だけとしましょう。
    この章の終わりには、さらに基本型を追加する方法がわかるでしょう。
    また後の章では、純粋なSTLCに、組、レコード、サブタイプ、
    変更可能状態などの他の便利な構成要素をとり入れてよりリッチなものにします。

    ブール値から始めて3つのものを追加します:
        - 変数
        - 関数抽象
        - (関数)適用

    これから、以下の抽象構文コンストラクタが出てきます
    (ここではこれを非形式的BNF記法で書き出します。後に形式化します。):
<<
       t ::= x                       変数
           | \x:T.t1                 関数抽象
           | t1 t2                   関数適用
           | true                    定数 true
           | false                   定数 false
           | if t1 then t2 else t3   条件式
>>
    関数抽象 [\x:T.t1] の [\]記号はよくギリシャ文字のラムダ(λ)で記述されます
    (これがラムダ計算の名前の由来です)。
    変数[x]は関数のパラメータ(_parameter_)、
    項[t1]は関数の本体(_body_)と呼ばれます。
    付記された [:T] は関数が適用される引数の型を定めます。

    例をいくつか:

      - [\x:Bool. x]

        ブール値の恒等関数。

      - [(\x:Bool. x) true]

        ブール値[true]に適用された、ブール値の恒等関数。

      - [\x:Bool. if x then false else true]

        ブール値の否定関数。

      - [\x:Bool. true]

        すべての(ブール値の)引数に対して[true]を返す定数関数。

      - [\x:Bool. \y:Bool. x]

        2つのブール値をとり、最初のものを返す2引数関数。
        (なお、Coqと同様、2引数関数は、実際には本体が1引数関数である1引数関数です。)

      - [(\x:Bool. \y:Bool. x) false true]

        2つのブール値をとり、最初のものを返す2引数関数を、ブール値[false]と[true]
        に適用したもの。
        なお、Coqと同様、関数適用は左結合です。つまり、この式は
        [((\x:Bool. \y:Bool. x) false) true] と構文解析されます。

      - [\f:Bool->Bool. f (f true)]

        (ブール値からブール値への)「関数」[f]を引数にとる高階関数。
        この高階関数は、[f]を[true]に適用し、その値にさらに[f]を適用します。

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)]

        上記高階関数を、常に[false]を返す定数関数に適用したもの。

    最後のいくつかの例で示されたように、STLCは高階(_higher-order_)関数の言語です。
    他の関数を引数として取る関数や、結果として他の関数を返す関数を書き下すことができます。

    別の注目点は、名前を持つ(_named_)関数を定義する基本構文を、STLCは何も持っていないことです。
    すべての関数は「名無し」("anonymous")です。
    後の[MoreStlc_J]章で、この体系に名前を持つ関数を追加することが簡単であることがわかるでしょう。
    実のところ、基本的な命名と束縛の機構はまったく同じです。

    STLCの型には[Bool]が含まれます。
    この型はブール値定数[true]と[false]、および結果がブール値になるより複雑な計算の型です。
    それに加えて「関数型」(_arrow types_)があります。
    これは関数の型です。
<<
      T ::= Bool
          | T1 -> T2
>>
    例えば:

      - [\x:Bool. false] は型 [Bool->Bool] を持ちます。

      - [\x:Bool. x] は型 [Bool->Bool] を持ちます。

      - [(\x:Bool. x) true] は型 [Bool] を持ちます。

      - [\x:Bool. \y:Bool. x] は型 [Bool->Bool->Bool] 
        (つまり [Bool -> (Bool->Bool)])を持ちます。

      - [(\x:Bool. \y:Bool. x) false] は型 [Bool->Bool] を持ちます。

      - [(\x:Bool. \y:Bool. x) false true] は型 [Bool] を持ちます。

      - [\f:Bool->Bool. f (f true)] は型 [(Bool->Bool) -> Bool] を持ちます。

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)] は型 [Bool] を持ちます。
*)

(* ###################################################################### *)
(* ** Syntax *)
(** ** 構文 *)

Module STLC.

(* ################################### *)
(* *** Types *)
(** *** 型 *)

Inductive ty : Type :=
  | ty_Bool  : ty
  | ty_arrow : ty -> ty -> ty.

(* ################################### *)
(* *** Terms *)
(** *** 項 *)

Inductive tm : Type :=
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

(* Something to note here is that an abstraction [\x:T.t] (formally,
    [tm_abs x T t]) is always annotated with the type ([T]) of its
    parameter.  This is in contrast to Coq (and other functional
    languages like ML, Haskell, etc.), which use _type inference_ to
    fill in missing annotations. *)
(** ここで注目すべきは、関数抽象 [\x:T.t] (形式的には [tm_abs x T t])
    には常にパラメータの型([T])が付記されることです。
    これは Coq(あるいは他のML、Haskellといった関数型言語)と対照的です。
    それらは、付記がないものを型推論で補完します。*)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
  | Case_aux c "tm_abs" | Case_aux c "tm_true"
  | Case_aux c "tm_false" | Case_aux c "tm_if" ].

(* Some examples... *)
(** いくつかの例... *)

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

(* (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)
(** (これらを[Definition]ではなく[Notation]とすることで、
    [auto]に扱いやすくしています。) *)

(* ###################################################################### *)
(* ** Operational Semantics *)
(** ** 操作的意味論 *)

(* To define the small-step semantics of STLC terms, we begin -- as
    always -- by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)
(** STLC項のスモールステップ意味論を定義するために、いつものように、
    値の集合を定義することから始めます。
    次に、自由変数(_free variables_)と置換(_substitution_)という、
    重大な概念を定義します。これらは関数適用式の簡約規則に使われます。
    そして最後に、スモールステップ関係自体を与えます。*)

(* ################################### *)
(* *** Values *)
(** *** 値 *)

(* To define the values of the STLC, we have a few cases to consider.

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
(** STLCの値を定義するために、いくつかの場合を考えなければなりません。

    最初に、言語のブール値については、状況は明確です:
    [true]と[false]だけが値です。([if]式は決して値ではありません。)

    二番目に、関数適用は明らかに値ではありません。
    関数適用は関数が何らかの引数に対して呼ばれたことを表しているのですから、
    明らかにこれからやることが残っています。

    三番目に、関数抽象については選択肢があります:

      - [\a:A.t1] が値であるのは、[t1]が値であるときのみである、
        とすることができます。
        つまり、関数の本体が
        (どのような引数に適用されるかわからない状態で可能な限り)
        簡約済みであるときのみ、ということです。

      - あるいは、[\a:A.t1] は常に値である、とすることもできます。
        [t1]が値であるかどうかに関係なく、です。
        言いかえると、簡約は関数抽象で止まる、とすることです。

    Coq は最初の選択肢を取っています。例えば、
[[
         Eval simpl in (fun a:bool => 3 + 4)
]]
    は [fun a:bool => 7] となります。
    しかし実際の関数型プログラミング言語のほとんどは、
    第二の選択肢を取っています。
    つまり、関数の本体の簡約は、関数が実際に引数に適用されたときにのみ開始されます。
    ここでは、同様に第二の選択肢を選びます。

    最後に、関数抽象の中を簡約することを選択しなかったため、
    変数が値であるかをどうかを心配する必要はなくなります。なぜなら、
    プログラムの簡約は常に「外側から内側に」行われ、
    [step]関係は常に閉じた(自由変数を持たない)項だけを対象とするからです。*)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tm_abs x T t)
  | t_true :
      value tm_true
  | t_false :
      value tm_false.

Hint Constructors value.

(* ###################################################################### *)
(* *** Free Variables and Substitution *)
(** *** 自由変数と置換 *)

(* Now we come to the heart of the matter: the operation of
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
(** これから問題の核心に入ります: 項の変数を別の項で置換する操作です。

    この操作は後で関数適用の操作的意味論を定義するために使います。
    関数適用では、関数本体の中の関数パラメータを引数項で置換することが必要になります。
    例えば、
[[
       (\x:Bool. if x then true else x) false
]]
    は、関数の本体のパラメータ[x]を[false]で置換することで、[false]に簡約されます。
    一般に、ある項[t]の変数[x]の出現を、与えらえた項[s]で置換できることが必要です。
    非形式的な議論では、これは通常 [ [s/x]t ] と書き、「[t]の[x]を[s]で置換する」と読みます。

    いくつかの例を示します:

      - [[true / a] (if a then a else false)] は [if true then true else false]
        となります。

      - [[true / a] a] は [true] となります。

      - [[true / a] (if a then a else b)] は [if true then true else b]
        となります。

      - [[true / a] b] は [b] となります。

      - [[true / a] false] は [false] となります(何もしない置換です)。

      - [[true / a] (\y:Bool. if y then a else false)] は
        [\y:Bool. if y then true else false] となります。

      - [[true / a] (\y:Bool. a)] は [\y:Bool. true] となります。

      - [[true / a] (\y:Bool. y)] は [\y:Bool. y] となります。

      - [[true / a] (\a:Bool. a)] は [\a:Bool. a] となります。

    最後の例はとても重要です。[\a:Bool. a] の [a] を [true] で置換したものは、
    [\a:Bool. true] に「なりません」! 理由は、[\a:Bool. a] の本体の [a] 
    は関数抽象で束縛されている(_bound_)からです。
    この[a]は新しいローカルな名前で、たまたまグローバルな名前[a]と同じ綴りであったものです。

    以下が、非形式的な定義です...
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
    ... そして形式的には: *)

Fixpoint subst (s:tm) (x:id) (t:tm) : tm :=
  match t with
  | tm_var x' => if beq_id x x' then s else t
  | tm_abs x' T t1 => tm_abs x' T (if beq_id x x' then t1 else (subst s x t1))
  | tm_app t1 t2 => tm_app (subst s x t1) (subst s x t2)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst s x t1) (subst s x t2) (subst s x t3)
  end.

(* Technical note: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested in defining the [step] relation on
    closed terms here, we can avoid this extra complexity. *)
(** 技術的注釈: 置換は、もし[s]、つまり他の項の変数を置換する項が、
    それ自身に自由変数を含むときを考えると、
    定義がよりトリッキーなものになります。
    ここで興味があるのは閉じた項についての[step]関係の定義のみなので、
    そのさらなる複雑さは避けることができます。*)

(* ################################### *)
(* *** Reduction *)
(** *** 簡約 *)

(* The small-step reduction relation for STLC follows the same
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
(** STLCのスモールステップ簡約関係は、これまで見てきたものと同じパターンに従います。
    直観的には、関数適用を簡約するため、最初に左側をリテラル関数になるまで簡約します。
    次に左側(引数)を値になるまで簡約します。そして最後に関数の本体の束縛変数を引数で置換します。
    この最後の規則は、非形式的には次のように書きます:
[[
      (\a:T.t12) v2 ==> [v2/a]t12
]]
    これは伝統的にベータ簡約("beta-reduction")と呼ばれます。

    非形式的に:
[[
                     ---------------------------                    (ST_AppAbs)
                     (\a:T.t12) v2 ==> [v2/a]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              t2 ==> t2'
                           ----------------                        (ST_App2)
                           v1 t2 ==> v1 t2'
]]
   (これに通常のブール値の規則をプラスします)。

   形式的には:
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
(* *** Examples *)
(** *** 例 *)

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

(* Again, we can use the [normalize] tactic from above to simplify
    the proof. *)
(** 再び、上述の[normalize]タクティックを使って、証明を簡単にすることができます。*)

Lemma step_example2' :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  normalize.
Qed.

(* **** Exercise: 2 stars (step_example3) *)
(** **** 練習問題: ★★ (step_example3) *)
(* Try to do this one both with and without [normalize]. *)
(** 次の証明を[normalize]を使う方法と使わない方法の両方で行ないなさい。*)

Lemma step_example3 :
       (tm_app (tm_app idBBBB idBB) idB)
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* ** Typing *)
(** ** 型付け *)

(* ################################### *)
(* *** Contexts *)
(** *** コンテキスト *)

(* Question: What is the type of the term "[x y]"?

    Answer: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place "typing judgment", informally
    written [Gamma |- t : T], where [Gamma] is a "typing context"
    -- a mapping from variables to their types.

    We hide the definition of partial maps in a module since it is
    actually defined in SfLib. *)
(** 問い: 項 "[x y]" の型は何でしょう？

    答え: それは [x] と [y] の型に依存します!

    つまり、項に型を付けるためには、
    その自由変数の型についてどういう仮定をしなければならないかを知る必要があります。

    このために、3つのものの間の型付けジャッジメント("typing judgment")を用意します。
    これを非形式的には [Gamma |- t : T] と記述します。ここで
    [Gamma] は「型付けコンテキスト」("typing context")、つまり、
    変数から型への写像です。

    モジュールにおける部分写像の定義は隠蔽します。
    なぜなら、実際には SfLib で定義されているからです。*)

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
(* *** Typing Relation *)
(** *** 型付け関係 *)

(* Informally:
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
(** 非形式的に:
[[
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
]]
記法 [ Gamma , x:T ] は「部分写像[Gamma]を拡張して[x]を[T]に写像するようにしたもの」を表します。
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
(* *** Examples *)
(** *** 例 *)

Example typing_example_1 :
  has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(* Note that since we added the has_type constructors to the
    hints database, auto can actually solve this one immediately.
    *)
(** has_typeコンストラクタをヒントデータベースに追加したことから、
    これを auto は直接解くことができることに注意します。*)

Example typing_example_1' :
  has_type empty (tm_abs a ty_Bool (tm_var a)) (ty_arrow ty_Bool ty_Bool).
Proof. auto.  Qed.

Hint Unfold beq_id beq_nat extend.

(* Written informally, the next one is:
[[
     empty |- \a:A. \b:A->A. b (b a))
           : A -> (A->A) -> A.
]]
*)
(** 非形式的に書くと
[[
     empty |- \a:A. \b:A->A. b (b a))
           : A -> (A->A) -> A.
]]
となるものが次の例です:
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

(* **** Exercise: 2 stars, optional *)
(** **** 練習問題: ★★, optional *)
(* Prove the same result without using [auto], [eauto], or
    [eapply]. *)
(** [auto]、[eauto]、[eapply] を使わずに同じ結果を証明しなさい。*)

Example typing_example_2_full :
  has_type empty
    (tm_abs a ty_Bool
       (tm_abs b (ty_arrow ty_Bool ty_Bool)
          (tm_app (tm_var b) (tm_app (tm_var b) (tm_var a)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars (typing_example_3) *)
(** **** 練習問題: ★★ (typing_example_3) *)
(* Formally prove the following typing derivation holds:
[[
   empty |- (\a:Bool->B. \b:Bool->Bool. \c:Bool.
               b (a c))
         : T.
]]
*)
(** 次の型付けが成立することを形式的に証明しなさい:
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

(* We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\a:Bool. \b:Bool, a b] -- i.e.,
[[
    ~ exists T,
        empty |- (\a:Bool. \b:Bool, a b) : T.
]]
*)
(** 項が「型付けできない」ことを証明することもできます。
    例えば [\a:Bool. \b:Bool, a b] に型をつける型付けが存在しないこと、
    つまり、
[[
    ~ exists T,
        empty |- (\a:Bool. \b:Bool, a b) : T.
]]
    を形式的にチェックしましょう。
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

(* **** Exercise: 3 stars (typing_nonexample_3) *)
(** **** 練習問題: ★★★ (typing_nonexample_3) *)
(* Another nonexample:
[[
    ~ (exists S, exists T,
          empty |- (\a:S. a a) : T).
]]
*)
(** 別の型を持たない例:
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

(* **** Exercise: 1 star (typing_statements) *)
(** **** 練習問題: ★ (typing_statements) *)

(* Which of the following propositions are provable?
       - [b:Bool |- \a:Bool.a : Bool->Bool]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. b a) : T]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. a b) : T]

       - [exists S, a:S |- (\b:Bool->Bool. b) a : S]

       - [exists S, exists T,  a:S |- (a a a) : T]

[]
*)
(** 以下のうち証明できるのものを挙げなさい。
       - [b:Bool |- \a:Bool.a : Bool->Bool]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. b a) : T]

       - [exists T,  empty |- (\b:Bool->Bool. \a:Bool. a b) : T]

       - [exists S, a:S |- (\b:Bool->Bool. b) a : S]

       - [exists S, exists T,  a:S |- (a a a) : T]

[]
*)

(* **** Exercise: 1 star, optional (more_typing_statements) *)
(** **** 練習問題: ★, optional (more_typing_statements) *)

(* Which of the following propositions are provable?  For the
    ones that are, give witnesses for the existentially bound
    variables.
       - [exists T,  empty |- (\b:B->B->B. \a:B, b a) : T]

       - [exists T,  empty |- (\a:A->B, \b:B-->C, \c:A, b (a c)):T]

       - [exists S, exists U, exists T,  a:S, b:U |- \c:A. a (b c) : T]

       - [exists S, exists T,  a:S |- \b:A. a (a b) : T]

       - [exists S, exists U, exists T,  a:S |- a (\c:U. c a) : T]

[]
*)
(** 以下の命題のうち証明できるものを挙げなさい。証明できるものについては、
    存在限量された変数に入る具体的な値を示しなさい。
       - [exists T,  empty |- (\b:B->B->B. \a:B, b a) : T]

       - [exists T,  empty |- (\a:A->B, \b:B-->C, \c:A, b (a c)):T]

       - [exists S, exists U, exists T,  a:S, b:U |- \c:A. a (b c) : T]

       - [exists S, exists T,  a:S |- \b:A. a (a b) : T]

       - [exists S, exists U, exists T,  a:S |- a (\c:U. c a) : T]

[]
*)

(* ###################################################################### *)
(* ** Properties *)
(** ** 性質 *)

(* ###################################################################### *)
(* *** Free Occurrences *)
(** *** 自由な出現 *)

(* A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].  For example:
      - [y] appears free, but [x] does not, in [\x:T->U. x y]
      - both [x] and [y] appear free in [(\x:T->U. x y) x]
      - no variables appear free in [\x:T->U. \y:T. x y]  *)
(** 変数[x]が項 t に自由に出現する(_appears free in_ a term _t_)とは、
    [t]が[x]の出現を含み、その出現が[x]のラベルが付けられた関数抽象のスコープ内にないことです。
    例えば:
      - [\x:T->U. x y] において[y]は自由に現れますが[x]はそうではありません。
      - [(\x:T->U. x y) x] においては[x]と[y]はともに自由に現れます。
      - [\x:T->U. \y:T. x y] においては自由に現れる変数はありません。*)

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

(* A term in which no variables appear free is said to be _closed_. *)
(** 自由に現れる変数を持たない項を「閉じている」(_closed_)と言います。 *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(* *** Substitution *)
(** *** 置換 *)

(* We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)
(** 最初に、自由変数と型付けコンテキストを結び付ける技術的な補題が必要になります。
    変数[x]が項[t]に自由に現れ、[t]がコンテキスト[Gamma]で型付けされるならば、
    [Gamma]は[x]に型を付けなければなりません。*)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.

(* _Proof_: We show, by induction on the proof that [x] appears free
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
(** 「証明」: [x]が[t]に自由に現れることの証明についての帰納法によって、
      すべてのコンテキスト[Gamma]について、
      [t]が[Gamma]のもとで型付けされるならば[Gamma]は[x]に型をつけることを示す。

      - 最後の規則が [afi_var] の場合、[t = x] である。そして、[t]が[Gamma]
        で型付けされるという仮定から、そのまま、[Gamma]で[x]に型付けされることが言える。

      - 最後の規則が [afi_app1] の場合、[t = t1 t2] で[x]は[t1]に自由に出現する。
        [t]が[Gamma]のもとで型付けされることから、型付け規則から[t1]も型付けされることになる。
        従って帰納仮定より[Gamma]は[x]に型を付ける。

      - 他のほとんどの場合も同様である。[x]が[t]の部分項に自由に現れ、
        [t]が[Gamma]で片付けされることから、[x]が出現している[t]の部分項は同様に[Gamma]
        で型付けされる。従って帰納仮定より求めるべき結果が得られる。

      - 残るのは、最後の規則が [afi_abs] の場合だけである。この場合、
        [t = \y:T11.t12] で[x]は[t12]に自由に現れる。
        また[x]は[y]と異なっている。前の場合との違いは、
        [t]は[Gamma]のもとで型付けされているが、
        その本体[t12]は [(Gamma, y:T11)] のもとで型付けされているという点である。
        このため、帰納仮定は、拡張されたコンテキスト [(Gamma, y:T11)] で[x]
        に型付けされる、という主張になる。
        [Gamma]のもとで[x]に型が付けられるという結論を得るため、
        [x]と[y]が異なっているという点に注意して、補題[extend_neq]を使う。*)

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

(* Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)
(** 次に、空コンテキストで型付けされる任意の項は閉じている(自由変数を持たない)、
    という事実を必要とします。*)

(* **** Exercise: 2 stars (typable_empty__closed) *)
(** **** 練習問題: ★★ (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T,
    has_type empty t T  ->
    closed t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Sometimes, when we have a proof [Gamma |- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)
(** しばしば、証明 [Gamma |- t : T] があるとき、コンテキスト[Gamma]
    を別のコンテキスト[Gamma']に置換する必要が出てきます。
    これはどのような場合に安全でしょうか？
    直観的には、[t]に自由に現れるすべての変数について、[Gamma']が
    [Gamma]と同じ型を割当てることが少なくとも必要です。
    実際、この条件だけが必要になります。*)

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     has_type Gamma' t S.

(* _Proof_: By induction on a derivation of [Gamma |- t : T].

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
(** 「証明」: [Gamma |- t : T] の導出についての帰納法を使う。

      - 導出の最後の規則が[T_Var]のとき、[t = x] かつ [Gamma x = T] である。
        仮定から [Gamma' x = T] であるから、[T_Var] より [Gamma' |- t : T] となる。

      - 最後の規則が [T_Abs] のとき、[t = \y:T11. t12] かつ [T = T11 -> T12]
        かつ [Gamma, y:T11 |- t12 : T12] である。
        帰納法の仮定は、任意のコンテキスト[Gamma'']について、
        もし [Gamma, y:T11] と [Gamma''] が [t12]
        内のすべての自由変数に同じ型を割り当てるならば、
        [t12] は [Gamma''] のもとで型[T12]を持つ、である。
        [Gamma']を、[t]内の自由変数について[Gamma]
        と同じ割当てをするコンテキストとする。
        示すべきことは [Gamma' |- \y:T11. t12 : T11 -> T12] である。

        [T_Abs] より、[Gamma', y:T11 |- t12 : T12] を示せば十分である。
        帰納仮定(ただし [Gamma'' = Gamma', y:T11] とする)より、
        [Gamma, y:T11] と [Gamma', y:T11] が
        [t12]内に自由に現れるすべての変数について割当てが一致することを示せば十分である。

        [t12]に自由に出現する任意の変数は[y]であるか、それ以外の変数かである。
        [Gamma, y:T11] と [Gamma', y:T11] は明らかに[y]については一致する。
        それ以外の場合、[t12]に自由に出現する[y]以外の任意の変数は
        [t = \y:T11. t12] にも自由に現れることに注意すると、[Gamma] と [Gamma']
        がそのような変数について割当てが一致するという仮定より、
        [Gamma, y:T11] と [Gamma', y:T11] も一致する。

      - 最後の規則が [T_App] の場合、[t = t1 t2] かつ [Gamma |- t1 : T2 -> T]
        かつ [Gamma |- t2 : T2] である。
        帰納法の仮定の1つは、すべてのコンテキスト[Gamma']について、
        [Gamma']と[Gamma]が[t1]のすべての自由変数について同じ割当てをするならば、
        [Gamma']のもとで[t1]は型 [T2 -> T] を持つ、となる。
        [t2]についても同様の帰納仮定がある。
        証明すべきことは、[Gamma']が[Gamma]と [t1 t2] 
        のすべての自由変数について同一の割当てをするという仮定の上で、
        [Gamma']のもとでも [t1 t2] が型[T]を持つ、ということである。
        [T_App]より、[t1] と [t2] がそれぞれ
        [Gamma']と[Gamma]のもとで同じ型を持つことを示せば十分である。
        しかし、[t1]のすべての自由変数は [t1 t2] でも自由変数であり、
        [t2]の自由変数についても同様である。ゆえに、2つの帰納仮定から求める結果が得られる。
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

(* Now we come to the conceptual heart of the proof that reduction
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
(** ついに、簡約が型を保存することの証明の概念的な核心です。
    つまり、「置換」が型を保存することを調べます。

    非形式的には、置換補題(_Substitution Lemma_)と呼ばれる補題は次のことを主張します:
    項[t]が自由変数[x]を持ち、[x]が型[U]を持つという仮定のもとで[t]に型[T]が付けられるとする。
    また、別の項[v]について、[v]が型[U]を持つことが示されるとする。このとき、
    [v]は[t]の型付けに関する[x]についての上述の仮定を満たすことから、[t]におけるそれぞれの
    [x]の出現を[v]で置換することはできるはずであり、
    その置換によって型が[T]のままである新しい項を得る。*)
(* (訳注：冒頭の "Formally" は "Informally" の間違いと文脈から判断。) *)
   

(* _Lemma_: If [Gamma,x:U |- t : T] and [|- v : U], then [Gamma |-
    [v/x]t : T]. *)
(** 「補題」: もし [Gamma,x:U |- t : T] かつ [|- v : U] ならば [Gamma |-
    [v/x]t : T]. *)

Lemma substitution_preserves_typing : forall Gamma x U v t T,
     has_type (extend Gamma x U) t T ->
     has_type empty v U   ->
     has_type Gamma (subst v x t) T.

(* One technical subtlety in the statement of the lemma is that we
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
(** 補題の主張について技術的に巧妙な点の1つは、[v]に型[U]を割当てるのが
    「空」コンテキストであることです。言い換えると、[v]が閉じていると仮定しています。
    この仮定は[T_Abs]の場合の証明を
    (この場面でとりうる別の仮定である [Gamma |- v : U] を仮定するのに比べて)
    大幅に簡単にします。
    なぜなら、コンテキスト不変補題(the context invariance lemma)が、
    どんなコンテキストでも[v]が型[U]を持つことを示すからです。
    [v]内の自由変数が
    [T-Abs]によってコンテキストに導入された変数と衝突することを心配する必要はありません。

    「証明」: [t]についての帰納法によって、すべての [T] と [Gamma] について
    [Gamma,x:U |- t : T] かつ [|- v : U] ならば、[Gamma |- [v/x]t : T]
    であることを証明する。

      - [t]が変数のとき、[t]が[x]であるか否かによって2つの場合がある。

          - [t = x] の場合、[Gamma, x:U |- x : T] という事実から、
            [U = T] になる。
            ここで示すべきことは、空コンテキストのもとで[v]が型 [U = T] という仮定の上で、
            [Gamma]のもとで [[v/x]x = v] が型[T]を持つことである。
            これは、コンテキスト不変補題、
            つまり、閉じた項が空コンテキストのもとで型[T]を持つならば、
            その項は任意のコンテキストのもとで型[T]を持つ、ということから得られる。

          - [t]が[x]以外の変数[y]である場合、[y]の型は[Gamma,x:U]のもとでも
            [Gamma]のもとでも変わらないということに注意するだけでよい。

      - [t]が関数抽象 [\y:T11. t12] のとき、帰納仮定から、すべての[Gamma']と[T']について、
        [Gamma',x:U |- t12 : T'] かつ [|- v : U] ならば [Gamma' |- [v/x]t12 : T']
        となる。
        特に [Gamma,y:T11,x:U |- t12 : T12] かつ [|- v : U] ならば
        [Gamma,y:T11 |- [v/x]t12 : T12] となる。
        [x]と[y]が同じ変数か否かでまた2つの場合がある。

        最初に [x = y] とすると、置換の定義から [[v/x]t = t] である。
        これから [Gamma |- t : T] を示すだけで良い。しかし、[Gamma,x:U |- t : T]
        であって、[\y:T11. t12]に[y]は自由に出現することはないから、
        コンテキスト不変補題から [Gamma |- t : T] となる。

        次に [x <> y] とする。型付け関係の反転から [Gamma,x:U,y:T11 |- t12 :
        T12] であり、これとコンテキスト不変補題から [Gamma,y:T11,x:U |- t12 : T12]
        となる。これから帰納仮定を使って、[Gamma,y:T11 |- [v/x]t12 : T12] が得られる。
        [T_Abs]から [Gamma |- \y:T11. [v/x]t12 : T11->T12] となり、
        置換の定義から([x <> y] に注意すると)求める
        [Gamma |- \y:T11. [v/x]t12 : T11->T12] が得られる。

      - [t] が関数適用 [t1 t2] のときは、結果は置換の定義と帰納法の仮定から直ぐに
        得られる。

      - 他の場合は、関数適用の場合と同様である。

    別の技術的な注: この証明は、
    型の導出についての帰納法ではなく項についての帰納法を使うことが議論をより簡単にするという、
    珍しいものです。この理由は、仮定 [has_type (extend Gamma x U) t T] 
    がある意味で完全に一般化されていないからです。
    ある意味というのは、型関係の1つの「スロット」、つまりコンテキストが、
    単に1つの変数ではないということです。
    このことにより、Coq がもともと持っている帰納法のタクティックでは必要な帰納法の仮定が導かれません。
    これを回避することは可能ですが、そのために必要な一般化はちょっとトリッキーです。
    これに対して項[t]は完全に一般化されています。*)

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

(* The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [v/x] t ] -- the result is the same either
    way. *)
(** 置換補題は一種の「交換性」("commutation" property)と見なせます。
    直観的には、置換と型付けはどの順でやってもよいということを主張しています。
    (適切なコンテキストのもとで)
    項[t]と[v]に個別に型付けをしてから置換によって両者を組合せても良いし、
    置換を先にやって後から [ [v/x] t ] に型をつけることもできます。
    どちらでも結果は同じです。*)

(* ###################################################################### *)
(* *** Preservation *)
(** *** 保存 *)

(* We now have the tools we need to prove _preservation_: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)
(** さて、(型の)保存(_preservation_)を証明する道具立ては揃いました。
    保存とは、閉じた項[t]が型[T]を持ち、[t']への評価ステップを持つならば、
    [t']はまた型[T]を持つ閉じた項である、という性質です。
    言い換えると、スモールステップ評価関係は型を保存するということです。
*)

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.

(* _Proof_: by induction on the derivation of [|- t : T].

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
(** 「証明」: [|- t : T] の導出についての帰納法を使う。

    - まず最後の規則が [T_Var]、[T_Abs]、[T_True]、[T_False] 
      である場合は外して良い。なぜなら、これらの場合、
      [t]はステップを進むことができないからである。

    - 導出の最後の規則が [T_App] のとき、[t = t1 t2] である。
      このとき、[t1 t2] が [t'] にステップを進めたことを示すのに使われた規則について、
      3つの場合が考えられる。

        - [t1 t2] が[ST_App1]によってステップを進めた場合、
          [t1]がステップを進めたものを[t1']とする。すると帰納仮定より
          [t1']は[t1]と同じ型を持ち、したがって、[t1' t2] は [t1 t2] と同じ型を持つ。

        - [ST_App2]の場合は同様である。

        - [t1 t2] が[ST_AppAbs]によってステップを進めた場合、
          [t1 = \x:T11.t12] であり、
          [t1 t2] は [subst t2 x t12] にステップする。
          すると置換が型を保存するという事実から求める結果となる。

    - 導出の最後の規則が [T_If] のとき、[t = if t1 then t2 else t3] であり、
      やはり[t]のステップについて3つの場合がある。

        - [t]が[t2]または[t3]にステップした場合、結果は直ぐである。なぜなら
          [t2]と[t3]は[t]と同じ型だからである。

        - そうでない場合、[t]は[ST_If]でステップする。このとき、
          帰納法の仮定から直接求める結果が得られる。
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

(* **** Exercise: 2 stars, recommended (subject_expansion_stlc) *)
(** **** 練習問題: ★★, recommended (subject_expansion_stlc) *)
(* An exercise earlier in this file asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That
    is, is it always the case that, if [t ==> t'] and [has_type
    t' T], then [has_type t T]?  If so, prove it.  If not, give a
    counter-example.

(* FILL IN HERE *)
[]
*)
(** このファイルの前の練習問題で、
    算術式とブール式の簡単な言語についての主部展開性についてききました
    (訳注:実際には Types_J.v内の練習問題)。
    STLCでこの性質は成立するでしょうか？つまり、
    [t ==> t'] かつ [has_type t' T] ならば [has_type t T] 
    ということが常に言えるでしょうか？
    もしそうならば証明しなさい。そうでなければ、反例を挙げなさい。

(* FILL IN HERE *)
[]
*)

(* ###################################################################### *)
(* *** Progress *)
(** *** 進行 *)

(* Finally, the _progress_ theorem tells us that closed, well-typed
    terms are never stuck: either a well-typed term is a value, or
    else it can take an evaluation step.
*)
(** 最後に、
    「進行」定理(the _progress_ theorem)は閉じた、
    型が付けられる項は行き詰まらないことを示します。
    つまり、型が付けられる項は、値であるか、または評価ステップを進むことができるか、どちらかです。
*)

Theorem progress : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.

(* _Proof_: by induction on the derivation of [|- t : T].

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
(** 「証明」: [|- t : T] の導出についての帰納法による。

    - 導出の最後の規則は[T_Var]ではありえない。なぜなら、
      空コンテキストにおいて変数には型付けできないからである。

    - [T_True]、[T_False]、[T_Abs]の場合は自明である。
      なぜなら、これらの場合 [t]は値だからである。

    - 導出の最後の規則が[T_App]の場合、[t = t1 t2] であり、
      [t1]および[t2]はどちらも空コンテキストで型付けされる。
      特に型[T2]があって、[|- t1 : T2 -> T] かつ [|- t2 : T2] となる。
      帰納法の仮定から、[t1]は値であるか、評価ステップを進むことができる。

        - [t1]が値のとき、[t2]を考えると、
          帰納仮定からさらに値である場合と評価ステップを進む場合がある。

            - [t2]が値のとき、[t1]は値で関数型であるから、ラムダ抽象である。
              ゆえに、[t1 t2] は [ST_AppAbs] でステップを進むことができる。

            - そうでなければ、[t2]はステップを進むことができる。したがって
              [ST_App2]で [t1 t2] もステップを進むことができる。

        - [t1]がステップを進むことができるとき、[ST_App1] で [t1 t2] 
          もステップを進むことができる。

    - 導出の最後の規則が[T_If]のとき、[t = if t1 then t2 else t3] で
      [t1] は型[Bool]を持つ。帰納仮定より[t1]は値かステップを進むことができるかどちらかである。

        - [t1]が値のとき、その型が[Bool]であることから[t1]は[true]または[false]である。
          [true]ならば[t]は[t2]に進み、そうでなければ[t3]に進む。

        - そうでないとき、[t1]はステップを進むことができる。したがって([ST_If]より)
          [t]もステップを進むことができる。

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

(* **** Exercise: 3 stars, optional (progress_from_term_ind) *)
(** **** 練習問題: ★★★, optional (progress_from_term_ind) *)
(* Show that progress can also be proved by induction on terms
    instead of types. *)
(** 型についての帰納法ではなく項についての帰納法でも進行の証明ができることを示しなさい。*)

Theorem progress' : forall t T,
     has_type empty t T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  tm_cases (induction t) Case; intros T Ht; auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(* *** Uniqueness of Types *)
(** *** 型の一意性 *)

(* **** Exercise: 3 stars (types_unique) *)
(** **** 練習問題: ★★★ (types_unique) *)
(* Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** STLCの別の好ましい性質は、型が唯一であることです。
    つまり、与えらえた項については(与えられたコンテキストで)
    高々1つの型しか型付けされません。*)
(* Formalize this statement and prove it. *)
(** この主張を形式化し、証明しなさい。*)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(* ** Additional Exercises *)
(** ** さらなる練習問題 *)

(* **** Exercise: 1 star (progress_preservation_statement) *)
(** **** 練習問題: ★ (progress_preservation_statement) *)
(* Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)
(** なにも見ることなく、単純型付きラムダ計算の進行定理と保存定理を書き下しなさい。*)
(** [] *)

(* **** Exercise: 2 stars, optional (stlc_variation1) *)
(** **** 練習問題: ★★, optional (stlc_variation1) *)
(* Suppose we add the following new rule to the evaluation
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
(** STLCの評価関係に次の新しい規則を加えたとします:
[[
      | T_Strange : forall x t,
           has_type empty (tm_abs x Bool t) Bool
]]
    この規則を加えても真であるSTLCの性質は以下のうちどれでしょうか？
    それぞれについて、「真のまま」または「偽に変わる」と書きなさい。
    偽に変わるものについては、反例を挙げなさい。

      - [step]の決定性

      - 進行

      - 保存      

[]
*)

(* **** Exercise: 2 stars (stlc_variation2) *)
(** **** 練習問題: ★★ (stlc_variation2) *)
(* Suppose we remove the rule [ST_App1] from the [step]
    relation. Which of the three properties in the previous
    exercise become false in the absence of this rule? For each
    that becomes false, give a counterexample.

[]
*)
(** [step]関係から[ST_App1]規則を除いたとします。
    このとき前の練習問題の3つの性質のうち、偽になるものはどれでしょう？
    偽になるものについては、反例を挙げなさい。

[]
*)

End STLC.

(* ###################################################################### *)
(* ###################################################################### *)
(* * Exercise: STLC with Arithmetic *)
(** * 練習問題: 算術を持つSTLC *)

(* To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)
(** STLCが実際のプログラミング言語の核として機能することを見るため、
    数値についての具体的な基本型と定数、いくつかの基本操作を追加しましょう。*)

Module STLCArith.

(* ###################################################################### *)
(* ** Syntax and Operational Semantics *)
(** ** 構文と操作的意味論 *)

(* To types, we add a base type of natural numbers (and remove
    booleans, for brevity) *)
(** 型について、自然数を基本型として加えます(そして簡潔さのためブール型を除きます)。 *)

Inductive ty : Type :=
  | ty_arrow : ty -> ty -> ty
  | ty_Nat   : ty.

(* To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing... *)
(** 項について、自然数の定数、1つ前をとる関数、1つ後をとる関数、積算、ゼロか否かのテスト...
    を加えます。 *)

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

(* **** Exercise: 4 stars, recommended (STLCArith) *)
(** **** 練習問題: ★★★★, recommended (STLCArith) *)
(* Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties of the original STLC to deal
      with the new syntactic forms.  Make sure Coq accepts the whole file. *)
(** 算術を拡張したSTLCの定義と性質の形式化を完成させなさい。特に:

    - STLCについてここまでやってきたこと(定義から進行定理まで)の全体をコピーして、
      ファイルのこの部分にペーストしなさい。

    - [subst]操作と[step]関係の定義を拡張して、算術の操作の適切な節を含むようにしなさい。

    - オリジナルのSTLCの性質の証明を拡張して、新しい構文を扱うようにしなさい。
      Coq がその証明を受理することを確認しなさい。*)

(* FILL IN HERE *)
(** [] *)

End STLCArith.

