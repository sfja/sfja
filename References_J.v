(** * References_J: 変更可能な参照の型付け *)
(* * References: Typing Mutable References *)

(* $Date: 2011-06-03 13:58:55 -0400 (Fri, 03 Jun 2011) $ *)


Require Export Smallstep_J.

(* So far, we have considered a variety of _pure_ language features,
    including functional abstraction, basic types such as numbers and
    booleans, and structured types such as records and variants.  These
    features form the backbone of most programming languages -- including
    purely functional languages such as Haskell, "mostly functional"
    languages such as ML, imperative languages such as C, and
    object-oriented languages such as Java.

    Most practical programming languages also include various _impure_
    features that cannot be described in the simple semantic framework
    we have used so far.  In particular, besides just yielding
    results, evaluation of terms in these languages may assign to
    mutable variables (reference cells, arrays, mutable record fields,
    etc.), perform input and output to files, displays, or network
    connections, make non-local transfers of control via exceptions,
    jumps, or continuations, engage in inter-process synchronization
    and communication, and so on.  In the literature on programming
    languages, such "side effects" of computation are more generally
    referred to as _computational effects_.

    In this chapter, we'll see how one sort of computational
    effect -- mutable references -- can be added to the calculi we have
    studied.  The main extension will be dealing explicitly with a
    _store_ (or _heap_).  This extension is straightforward to define;
    the most interesting part is the refinement we need to make to the
    statement of the type preservation theorem. *)
(** ここまでは、いろいろな「純粋な」(_pure_)言語機能を考えてきました。
    関数抽象、数値やブール値などの基本型、レコードやバリアントのような構造型などです。
    これらの機能はほとんどのプログラミング言語のバックボーンを構成しています。
    その言語の中にはHaskellのような純粋な関数型言語、MLのような
    「ほとんど関数型の」("mostly functional")言語、Cのような命令型言語、
    Javaのようなオブジェクト指向言語を含みます。

    ほとんどの実際のプログラミング言語は、
    ここまで使ってきた単純な意味論の枠組みでは記述できない様々な「不純な」(_impure_)
    機能も持っています。特に、これらの言語では項を評価することで、単に結果を得る他に、
    変更可能な変数(あるいは参照セル、配列、変更可能なレコードフィールド、等)に代入したり、
    ファイルや画面やネットワークに入出力したり、例外やジャンプ、
    継続によってローカルな枠を越えて制御を移したり、プロセス間の同期や通信を行ったりします。
    プログラミング言語についての文献では、
    これらの計算の副作用("side effects")はより一般に計算作用(_computational effects_)
    と参照されます。

    この章では、
    ここまで学習してきた計算体系に一つの計算作用「変更可能な参照」を追加する方法を見ます。
    主要な拡張は、記憶状態(_store_、あるいはヒープ(_heap_))を明示的に扱うことです。
    この拡張は直接的に定義できます。
    一番興味深い部分は、型保存定理の主張のために必要なリファインメント(refinement)です。 *)

(* ###################################################################### *)
(* ** Definitions *)
(** ** 定義 *)

(* Pretty much every programming language provides some form of
    assignment operation that changes the contents of a previously
    allocated piece of storage.  (Coq's internal language is a rare
    exception!)

    In some languages -- notably ML and its relatives -- the
    mechanisms for name-binding and those for assignment are kept
    separate.  We can have a variable [x] whose _value_ is the number
    [5], or we can have a variable [y] whose value is a
    _reference_ (or _pointer_) to a mutable cell whose current
    contents is [5].  These are different things, and the difference
    is visible to the programmer.  We can add [x] to another number,
    but not assign to it.  We can use [y] directly to assign a new
    value to the cell that it points to (by writing [y:=84]), but we
    cannot use it directly as an argument to an operation like [+].
    Instead, we must explicitly _dereference_ it, writing [!y] to
    obtain its current contents.

    In most other languages -- in particular, in all members of the C
    family, including Java -- _every_ variable name refers to a mutable
    cell, and the operation of dereferencing a variable to obtain its
    current contents is implicit.

    For purposes of formal study, it is useful to keep these
    mechanisms separate.  The development in this chapter will closely
    follow ML's model.  Applying the lessons learned here to C-like
    languages is a straightforward matter of collapsing some
    distinctions and rendering some operations such as dereferencing
    implicit instead of explicit.

    In this chapter, we study adding mutable references to the
    simply-typed lambda calculus with natural numbers. *)
(** ほとんどすべてのプログラミング言語が、
    記憶領域に以前に置かれた内容を変更する何らかの代入操作を持っています
    (Coqの内部言語は稀な例外です!)。

    いくつかの言語(特にMLやその親戚)では、
    名前束縛の機構と代入の機構を区別しています。
    「値」として数値[5]を持つ変数[x]を持つことも、
    現在の内容が[5]である変更可能なセルへの参照(_reference_、
    またはポインタ(_pointer_))を値とする変数[y]を持つこともできます。
    この2つは別のものです。プログラマにも両者の違いは見ることができます。
    [x]と別の数を足すことは可能ですが、それを[x]に代入することはできません。
    [y]を直接使って、[y]が指すセルに別の値を代入することが([y:=84] と書くことで)できます。
    しかし、この値は[+]のような操作の引数として直接使うことはできません。
    その代わり、現在の内容を得るために明示的に参照を手繰る
    (_dereference_、逆参照する)ことが必要です。これを[!y]と書きます。

    他のほとんどの言語、特にJavaを含むCファミリーのメンバーのすべてでは、
    すべての変数名は変更可能なセルを指します。
    そして、現在の値を得るための変数の逆参照操作は暗黙に行われます。

    形式的な学習の目的には、この2つの機構を分離しておいた方が便利です。
    この章の進行は、MLのやり方にほとんど従います。
    ここでやったことをCのような言語に適用するのは、分離していたものを一緒にすることと、
    逆参照のような操作を明示的なものから暗黙のものにするという単純な問題です。

    この章では、自然数を持つ単純型付きラムダ計算に変更可能な参照を追加すること学習します。 *)

(* ###################################################################### *)
(* ** Syntax *)
(** ** 構文 *)

Module STLCRef.

(* The basic operations on references are _allocation_,
    _dereferencing_, and _assignment_.

       - To allocate a reference, we use the [ref] operator, providing
         an initial value for the new cell.  For example, [ref 5]
         creates a new cell containing the value [5], and evaluates to
         a reference to that cell.

       - To read the current value of this cell, we use the
         dereferencing operator [!]; for example, [!(ref 5)] evaluates
         to [5].

       - To change the value stored in a cell, we use the assignment
         operator.  If [r] is a reference, [r := 7] will store the
         value [7] in the cell referenced by [r].  However, [r := 7]
         evaluates to the trivial value [unit]; it exists only to have
         the _side effect_ of modifying the contents of a cell. *)
(** 参照についての基本操作はアロケート(_allocation_)、逆参照(_dereferencing_)、
    代入(_assignment_)です。

       - 参照をアロケートするには、[ref]演算子を使います。
         これにより新しいセルに初期値が設定されます。
         例えば [ref 5] は値[5]を格納した新しいセルを生成し、
         そのセルへの参照に評価されます。

       - セルの現在の値を読むためには、逆参照演算子[!]を使います。
         例えば [!(ref 5)] は [5] に評価されます。

       - セルに格納された値を変更するには、代入演算子を使います。
         [r]が参照ならば、[r := 7] は [r] によって参照されるセルに値[7]を格納します。
         しかし [r := 7] はどうでも良い値 [unit] に評価されます。
         この演算子はセルの内容を変更するという副作用のためだけに存在します。 *)

(* ################################### *)
(* *** Types *)
(** *** 型 *)

(* We start with the simply typed lambda calculus over the
    natural numbers. To the base natural number type and arrow types
    we need to add two more types to deal with references. First, we
    need the _unit type_, which we will use as the result type of an
    assignment operation.  We then add _reference types_. *)
(** 自然数の上の単純型付きラムダ計算から始めます。
    基本の自然数型と関数型に参照を扱う2つの型を追加する必要があります。
    第一に「Unit型」です。これは代入演算子の結果の型として使います。
    それから参照型(_reference types_)を追加します。 *)
(* If [T] is a type, then [Ref T] is the type of references which
    point to a cell holding values of type [T].
<<
      T ::= Nat
          | Unit
          | T -> T
          | Ref T
>>
*)
(** [T]が型のとき、[Ref T] は型[T]の値を持つセルを指す参照の型です。
<<
      T ::= Nat
          | Unit
          | T -> T
          | Ref T
>>
*)

Inductive ty : Type :=
  | ty_Nat   : ty
  | ty_Unit  : ty
  | ty_arrow : ty -> ty -> ty
  | ty_Ref   : ty -> ty.

(* ################################### *)
(* *** Terms *)
(** *** 項 *)

(* Besides variables, abstractions, applications,
    natural-number-related terms, and [unit], we need four more sorts
    of terms in order to handle mutable references:
<<
      t ::= ...              Terms
          | ref t              allocation
          | !t                 dereference
          | t := t             assignment
          | l                  location
>>
*)
(** 変数、関数抽象、関数適用、自然数に関する項、[unit]の他に、
    変更可能な参照を扱うために4種類の項を追加する必要があります:
<<
      t ::= ...              Terms
          | ref t              allocation
          | !t                 dereference
          | t := t             assignment
          | l                  location
>>
*)

Inductive tm  : Type :=
  (* STLC with numbers: *)
  | tm_var    : id -> tm
  | tm_app    : tm -> tm -> tm
  | tm_abs    : id -> ty -> tm -> tm
  | tm_nat    : nat -> tm
  | tm_succ   : tm -> tm
  | tm_pred   : tm -> tm
  | tm_mult   : tm -> tm -> tm
  | tm_if0    : tm -> tm -> tm -> tm
  (* New terms: *)
  | tm_unit   : tm
  | tm_ref    : tm -> tm
  | tm_deref  : tm -> tm
  | tm_assign : tm -> tm -> tm
  | tm_loc    : nat -> tm.

(* Intuitively...
    - [ref t] (formally, [tm_ref t]) allocates a new reference cell
      with the value [t] and evaluates to the location of the newly
      allocated cell;

    - [!t] (formally, [tm_deref t]) evaluates to the contents of the
      cell referenced by [t];

    - [t1 := t2] (formally, [tm_assign t1 t2]) assigns [t2] to the
      cell referenced by [t1]; and

    - [l] (formally, [tm_loc l]) is a reference to the cell at
      location [l].  We'll discuss locations later. *)
(** 直観的には...
    - [ref t] (形式的には [tm_ref t])は値[t]が格納された新しい参照セルをアロケートし、
      新しくアロケートされたセルの場所(location)を評価結果とします。

    - [!t] (形式的には [tm_deref t])は[t]で参照されるセルの内容を評価結果とします。

    - [t1 := t2] (形式的には [tm_assign t1 t2])は[t1]で参照されるセルに[t2]を代入します。

    - [l] (形式的には [tm_loc l])は場所[l]のセルの参照です。場所については後で議論します。 *)

(* In informal examples, we'll also freely use the extensions
    of the STLC developed in the [MoreStlc] chapter; however, to keep
    the proofs small, we won't bother formalizing them again here.  It
    would be easy to do so, since there are no very interesting
    interactions between those features and references. *)
(** 非形式的な例では、[MoreStlc_J]章で行ったSTLCの拡張も自由に使います。
    しかし、証明を小さく保つため、ここでそれらを再度形式化することに煩わされることはしません。
    やろうと思えばそうすることは簡単です。なぜなら、
    それらの拡張と参照とには興味深い相互作用はないからです。*)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app"
  | Case_aux c "tm_abs" | Case_aux c "tm_zero"
  | Case_aux c "tm_succ" | Case_aux c "tm_pred"
  | Case_aux c "tm_mult" | Case_aux c "tm_if0"
  | Case_aux c "tm_unit" | Case_aux c "tm_ref"
  | Case_aux c "tm_deref" | Case_aux c "tm_assign"
  | Case_aux c "tm_loc" ].

Module ExampleVariables.

Definition x := Id 0.
Definition y := Id 1.
Definition r := Id 2.
Definition s := Id 3.

End ExampleVariables.

(* ################################### *)
(* *** Typing (Preview) *)
(** *** 型付け (プレビュー) *)

(* Informally, the typing rules for allocation, dereferencing, and
    assignment will look like this:
[[[
                           Gamma |- t1 : T1
                       ------------------------                         (T_Ref)
                       Gamma |- ref t1 : Ref T1

                        Gamma |- t1 : Ref T11
                        ---------------------                         (T_Deref)
                          Gamma |- !t1 : T11

                        Gamma |- t1 : Ref T11
                          Gamma |- t2 : T11
                       ------------------------                      (T_Assign)
                       Gamma |- t1 := t2 : Unit
]]]
    The rule for locations will require a bit more machinery, and this
    will motivate some changes to the other rules; we'll come back to
    this later. *)
(** 非形式的には、アロケーション、逆参照、代入の型付け規則は以下のようになります:
[[
                           Gamma |- t1 : T1
                       ------------------------                         (T_Ref)
                       Gamma |- ref t1 : Ref T1

                        Gamma |- t1 : Ref T11
                        ---------------------                         (T_Deref)
                          Gamma |- !t1 : T11

                        Gamma |- t1 : Ref T11
                          Gamma |- t2 : T11
                       ------------------------                      (T_Assign)
                       Gamma |- t1 := t2 : Unit
]]
    場所についての規則はもう少し仕掛けが必要になり、
    それが他の規則にいくらかの変更を求めることになります。
    これについては後にまた戻ってきます。*)

(* ################################### *)
(* *** Values and Substitution *)
(** *** 値と置換 *)

(* Besides abstractions and numbers, we have two new types of values:
    the unit value, and locations.  *)
(** 関数抽象と数値に加えて、新たに2種類の値を持ちます: unit値と場所です。 *)

Inductive value : tm -> Prop :=
  | v_abs  : forall x T t,
      value (tm_abs x T t)
  | v_nat : forall n,
      value (tm_nat n)
  | v_unit :
      value tm_unit
  | v_loc : forall l,
      value (tm_loc l).

Hint Constructors value.

(* Extending substitution to handle the new syntax of terms is
    straightforward.  *)
(** 新しい項の構文を扱うための置換の拡張は直接的です。 *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var x'       =>
      if beq_id x x' then s else t
  | tm_app t1 t2    =>
      tm_app (subst x s t1) (subst x s t2)
  | tm_abs x' T t1  =>
      if beq_id x x' then t else tm_abs x' T (subst x s t1)
  | tm_nat n        =>
      t
  | tm_succ t1      =>
      tm_succ (subst x s t1)
  | tm_pred t1      =>
      tm_pred (subst x s t1)
  | tm_mult t1 t2   =>
      tm_mult (subst x s t1) (subst x s t2)
  | tm_if0 t1 t2 t3 =>
      tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)
  | tm_unit         =>
      t
  | tm_ref t1       =>
      tm_ref (subst x s t1)
  | tm_deref t1     =>
      tm_deref (subst x s t1)
  | tm_assign t1 t2 =>
      tm_assign (subst x s t1) (subst x s t2)
  | tm_loc _        =>
      t
  end.

(* ###################################################################### *)
(* * Pragmatics *)
(** * プラグマティクス(語用論) *)

(* ################################### *)
(* ** Side Effects and Sequencing *)
(** ** 副作用と順次処理 *)

(* The fact that the result of an assignment expression is the
    trivial value [unit] allows us to use a nice abbreviation for
    _sequencing_.  For example, we can write
<<
       r:=succ(!r); !r
>>
    as an abbreviation for
<<
       (\x:Unit. !r) (r := succ(!r)).
>>
    This has the effect of evaluating two expressions in order and
    returning the value of the second.  Restricting the type of the first
    expression to [Unit] helps the typechecker to catch some silly
    errors by permitting us to throw away the first value only if it
    is really guaranteed to be trivial.

    Notice that, if the second expression is also an assignment, then
    the type of the whole sequence will be [Unit], so we can validly
    place it to the left of another [;] to build longer sequences of
    assignments:
<<
       r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r
>>
*)
(** 代入式の結果がつまらない値[unit]であるという事実によって、
    順次処理(_sequencing_)のうまい略記が可能になります。
    例えば、
<<
       (\x:Unit. !r) (r := succ(!r)).
>>
    の略記として
<<
       r:=succ(!r); !r
>>
    と書くことができます。
    これは2つの式を順番に評価するという作用を持ち、2つ目の式の値を返します。
    1つ目の式の型を[Unit]に限定することで、
    1つ目の値を捨てることができるのは本当にそれがつまらない値であることが保証されているときだけになり、
    型チェッカで馬鹿なエラーをチェックするのに役立ちます。

    なお、もし2つ目の式もまた代入ならば、2つの式の列全体の型が[Unit]になります。
    これから、より長い代入の列を作るために別の[;]の左側に置いても問題ありません:
<<
       r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r
>>
*)

(* Formally, we introduce sequencing as a "derived form"
    [tm_seq] that expands into an abstraction and an application. *)
(** 形式的には、順次処理を"derived form"として導入します。
    この"derived form"は、関数抽象と関数適用に展開されます。 *)

Definition tm_seq t1 t2 :=
  tm_app (tm_abs (Id 0) ty_Unit t2) t1.

(* ################################### *)
(* ** References and Aliasing *)
(** ** 参照と別名付け *)

(* It is important to bear in mind the difference between the
    _reference_ that is bound to [r] and the _cell_ in the store that
    is pointed to by this reference.

    If we make a copy of [r], for example by binding its value to
    another variable [s], what gets copied is only the _reference_,
    not the contents of the cell itself.

    For example, after evaluating
<<
      let r = ref 5 in
      let s = r in
      s := 82;
      (!r)+1
>>
    the cell referenced by [r] will contain the value [82], while the
    result of the whole expression will be [83].  The references [r]
    and [s] are said to be _aliases_ for the same cell.

    The possibility of aliasing can make programs with references
    quite tricky to reason about.  For example, the expression
<<
      r := 5; r := !s
>>
    assigns [5] to [r] and then immediately overwrites it with [s]'s
    current value; this has exactly the same effect as the single
    assignment
<<
      r := !s
>>
    _unless_ we happen to do it in a context where [r] and [s] are
    aliases for the same cell! *)
(** [r]に束縛される参照(_reference_)と、
    この参照によって指されているセル(_cell_)の違いを心に留めておく必要があります。

    例えば[r]を別の変数[s]に束縛することで[r]のコピーを作るとすると、
    コピーされるのは参照だけで、セルの中身自身ではありません。

    例えば、次の式を評価します:
<<
      let r = ref 5 in
      let s = r in
      s := 82;
      (!r)+1
>>
    するとその後で[r]によって参照されたセルは値[82]を格納している状態になります。
    一方、式全体の結果は[83]になります。参照[r]と[s]は同じセルの別名(_aliases_)と言われます。

    別名を付けられる能力があることによって、参照を持つプログラムに関する推論は、
    きわめてトリッキーになります。例えば、式
<<
      r := 5; r := !s
>>
    は[r]に[5]を代入し、直ぐにそれを[s]の現在の値で上書きします。
    これは、単一の代入
<<
      r := !s
>>
    と完全に同じ作用をします。
    ただし、「[r]と[s]がたまたま同じセルの別名であるという状況でない限り」、です! *)

(* ################################### *)
(* ** Shared State *)
(** ** 共有状態 *)

(* Of course, aliasing is also a large part of what makes references
    useful.  In particular, it allows us to set up "implicit
    communication channels" -- shared state -- between different parts
    of a program.  For example, suppose we define a reference cell and
    two functions that manipulate its contents:
<<
    let c = ref 0 in
    let incc = \_:Unit. (c := succ (!c); !c) in
    let decc = \_:Unit. (c := pred (!c); !c) in
    ...
>>
*)
(** もちろん、別名も、参照を便利なものにする大きな部分です。
    特に参照は、プログラムの異なる部分の間の暗黙の通信チャンネル
    ("implicit communication channels")、
    つまり共有状態(shared state)としてはたらきます。
    例えば、参照セルと、その内容を扱う2つの関数を定義するとします:
<<
    let c = ref 0 in
    let incc = \_:Unit. (c := succ (!c); !c) in
    let decc = \_:Unit. (c := pred (!c); !c) in
    ...
>>
*)

(* Note that, since their argument types are [Unit], the
    abstractions in the definitions of [incc] and [decc] are not
    providing any useful information to the bodies of the
    functions (using the wildcard [_] as the name of the bound
    variable is a reminder of this).  Instead, their purpose is to
    "slow down" the execution of the function bodies: since function
    abstractions are values, the two [let]s are executed simply by
    binding these functions to the names [incc] and [decc], rather
    than by actually incrementing or decrementing [c].  Later, each
    call to one of these functions results in its body being executed
    once and performing the appropriate mutation on [c].  Such
    functions are often called _thunks_.

    In the context of these declarations, calling [incc] results in
    changes to [c] that can be observed by calling [decc].  For
    example, if we replace the [...] with [(incc unit; incc unit; decc
    unit)], the result of the whole program will be [1]. *)
(** ここで、それぞれ引数の型は[Unit]なので、
    [incc]と[decc]の定義において関数抽象は関数本体に特に有用な情報を提供しないことに注意します
    (束縛変数名にワイルドカード[_]を使っているのは、このことを合図したものです)。
    そうではなく、関数抽象の目的は関数本体の実行を「遅く」するためです。
    関数抽象は値であることから、2つの[let]は単に2つの関数を名前[incc]と[decc]に束縛するだけで、
    実際に[c]を増やしたり減らしたりはしません。後に、これらの関数の1つを呼び出すたびに、
    その本体が1度実行され[c]について対応する変更が行われます。
    こういった関数はしばしば _thunk_ と呼ばれます。

    これらの宣言のコンテキストで、[incc]を呼ぶと[c]が変更されますが、
    これは[decc]を呼ぶことで確認できます。
    例えば [...] を [(incc unit; incc unit; decc unit)] に換えると、
    プログラム全体の結果は[1]になります。 *)
(* ** Objects *)
(** ** オブジェクト *)

(* We can go a step further and write a _function_ that creates [c],
    [incc], and [decc], packages [incc] and [decc] together into a
    record, and returns this record:
<<
    newcounter =
        \_:Unit.
           let c = ref 0 in
           let incc = \_:Unit. (c := succ (!c); !c) in
           let decc = \_:Unit. (c := pred (!c); !c) in
           {i=incc, d=decc}
>>
*)
(** もう一歩進んで、[c]、[incc]、[decc]を生成し、[incc]と[decc]をレコードにパッケージ化し、
    このレコードを返す「関数」を記述することもできます:
<<
    newcounter =
        \_:Unit.
           let c = ref 0 in
           let incc = \_:Unit. (c := succ (!c); !c) in
           let decc = \_:Unit. (c := pred (!c); !c) in
           {i=incc, d=decc}
>>
*)
(* Now, each time we call [newcounter], we get a new record of
    functions that share access to the same storage cell [c].  The
    caller of [newcounter] can't get at this storage cell directly,
    but can affect it indirectly by calling the two functions.  In
    other words, we've created a simple form of _object_.
<<
    let c1 = newcounter unit in
    let c2 = newcounter unit in
    // Note that we've allocated two separate storage cells now!
    let r1 = c1.i unit in
    let r2 = c2.i unit in
    r2  // yields 1, not 2!
>>
*)
(** このとき、[newcounter]を呼ぶたびに、
    同じ記憶セル[c]のアクセスを共有する2つの関数の新たなレコードが得られます。
    [newcounter]を呼び出す側はこの記憶セルには直接手が届きませんが、
    2つの関数を呼ぶことで間接的に影響を及ぼすことができます。
    言い換えると、簡単な形のオブジェクト(_object_)を作ったのです。
<<
    let c1 = newcounter unit in
    let c2 = newcounter unit in
    // ここで2つの別個の記憶セルをアロケートしたことに注意!
    let r1 = c1.i unit in
    let r2 = c2.i unit in
    r2  // 1 を返します。2ではありません!
>>
*)
(* **** Exercise: 1 star *)
(** **** 練習問題: ★ *)
(* Draw (on paper) the contents of the store at the point in
    execution where the first two [let]s have finished and the third
    one is about to begin. *)
(** 最初の2つの[let]が完了し3つ目が始まろうとする時点の記憶の中身を(紙の上に)描きなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* ################################### *)
(* ** References to Compound Types *)
(** ** 参照と合成型 *)

(* A reference cell need not contain just a number: the primitives
    we've defined above allow us to create references to values of any
    type, including functions.  For example, we can use references to
    functions to give a (not very efficient) implementation of arrays
    of numbers, as follows.  Write [NatArray] for the type
    [Ref (Nat->Nat)].

    Recall the [equal] function from the [MoreStlc] chapter:
<<
    equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
>>
    Now, to build a new array, we allocate a reference cell and fill
    it with a function that, when given an index, always returns [0].
<<
    newarray = \_:Unit. ref (\n:Nat.0)
>>
    To look up an element of an array, we simply apply
    the function to the desired index.
<<
    lookup = \a:NatArray. \n:Nat. (!a) n
>>
    The interesting part of the encoding is the [update] function.  It
    takes an array, an index, and a new value to be stored at that index, and
    does its job by creating (and storing in the reference) a new function
    that, when it is asked for the value at this very index, returns the new
    value that was given to [update], and on all other indices passes the
    lookup to the function that was previously stored in the reference.
<<
    update = \a:NatArray. \m:Nat. \v:Nat.
                 let oldf = !a in
                 a := (\n:Nat. if equal m n then v else oldf n);
>>
    References to values containing other references can also be very
    useful, allowing us to define data structures such as mutable
    lists and trees. *)
(** 参照セルの中身は数値でなければならないわけではありません。
    上で定義したプリミティブによって、任意の型の値への参照を作ることができます。
    その任意の型の中には関数型も含まれます。
    例えば、関数への参照を使って、数値の配列の(あまり効率的でない)実装をすることができます。
    以下の通りです。型 [Ref (Nat->Nat)] を [NatArray] と書きます。

    [MoreStlc_J]章での[equal]関数を思い出してください:
<<
    equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
>>
    このとき、新しい配列を作るために、参照セルをアロケートし、そのセルに関数を入れます。
    その関数はインデックスを与えられると常に[0]を返します。
<<
    newarray = \_:Unit. ref (\n:Nat.0)
>>
    配列の要素をとりだすためには、その関数を求められたインデックスに適用するだけです。
<<
    lookup = \a:NatArray. \n:Nat. (!a) n
>>
    このエンコードの興味深いところは[update]関数です。
    [update]関数は、配列、インデックス、そのインデックスの場所に格納する新しい値をとり、
    新しい関数を生成し(そしてそれを参照に格納し)ます。
    その関数は、この特定のインデックスの値を尋かれたときには[update]に与えられた新しい値を返します。
    他のインデックスについては、以前にその参照に格納されていた関数にまかせます。
<<
    update = \a:NatArray. \m:Nat. \v:Nat.
                 let oldf = !a in
                 a := (\n:Nat. if equal m n then v else oldf n);
>>
    別の参照を含む値への参照もまたとても有用です。
    これにより、変更可能なリストや木などのデータ構造が定義できるようになります。 *)

(* **** Exercise: 2 stars *)
(** **** 練習問題: ★★ *)
(* If we defined [update] more compactly like this
<<
    update = \a:NatArray. \m:Nat. \v:Nat.
                a := (\n:Nat. if equal m n then v else (!a) n)
>>
would it behave the same? *)
(** もし[update]を次のようによりコンパクトに定義したとします。
<<
    update = \a:NatArray. \m:Nat. \v:Nat.
                a := (\n:Nat. if equal m n then v else (!a) n)
>>
これは前の定義と同じように振る舞うでしょうか？ *)

(* FILL IN HERE *)
(** [] *)

(* ################################### *)
(* ** Null References *)
(** ** null参照 *)

(* There is one more difference between our references and C-style
    mutable variables: in C-like languages, variables holding pointers
    into the heap may sometimes have the value [NULL].  Dereferencing
    such a "null pointer" is an error, and results in an
    exception (Java) or in termination of the program (C).

    Null pointers cause significant trouble in C-like languages: the
    fact that any pointer might be null means that any dereference
    operation in the program can potentially fail.  However, even in
    ML-like languages, there are occasionally situations where we may
    or may not have a valid pointer in our hands.  Fortunately, there
    is no need to extend the basic mechanisms of references to achieve
    this: the sum types introduced in the [MoreStlc] chapter already
    give us what we need.

    First, we can use sums to build an analog of the [option] types
    introduced in the [Lists] chapter.  Define [Option T] to be an
    abbreviation for [Unit + T].

    Then a "nullable reference to a [T]" is simply an element of the
    type [Ref (Option T)]. *)
(** ここで定義した参照と、C言語スタイルの変更可能な変数にはもう一つの違いがあります。
    Cのような言語では、ヒープへのポインタを持つ変数は値[NULL]を持つことがあります。
    そのような「nullポインタ」の逆参照はエラーで、
    例外になったり(Java)、プログラムが停止したり(C)します。

    Cのような言語ではnullポインタは重大な問題を起こします。
    任意のポインタがnullになる可能性があるという事実は、
    任意の逆参照操作が潜在的に失敗の可能性を持つということです。
    しかしMLのような言語でも、
    時には正しいポインタを持つことを許すことも許さないこともできるようにしたい場合があります。
    幸い、参照の基本メカニズムを拡張しなくてもこれは実現できます。
    [MoreStlc_J]章で導入された直和型によってそれが可能になります。

    最初に、直和を使って、[Lists_J]章で導入した[option]型に対応するものを構築します。
    [Option T] を [Unit + T] の略記法として定義します。

    すると、「nullになり得る[T]への参照」は単に型 [Ref (Option T)] の要素となります。 *)

(* ################################### *)
(* ** Garbage Collection *)
(** ** ガベージコレクション *)

(* A last issue that we should mention before we move on with
    formalizing references is storage _de_-allocation.  We have not
    provided any primitives for freeing reference cells when they are
    no longer needed.  Instead, like many modern languages (including
    ML and Java) we rely on the run-time system to perform _garbage
    collection_, collecting and reusing cells that can no longer be
    reached by the program.

    This is _not_ just a question of taste in language design: it is
    extremely difficult to achieve type safety in the presence of an
    explicit deallocation operation.  The reason for this is the
    familiar _dangling reference_ problem: we allocate a cell holding
    a number, save a reference to it in some data structure, use it
    for a while, then deallocate it and allocate a new cell holding a
    boolean, possibly reusing the same storage.  Now we can have two
    names for the same storage cell -- one with type [Ref Nat] and the
    other with type [Ref Bool]. *)
(** 参照の形式化に移る前に述べておくべき最後の問題が、
    記憶のデアロケーション(_de_-allocation)です。
    参照セルが必要なくなったときにそれを解放する何らかのプリミティブを提供していません。
    その代わり、多くの近代的な言語(MLとJavaを含む)のように、
    実行時システムがガベージコレクション(_garbage collection_)を行うことに頼っています。
    ガベージコレクションはプログラムから到達しなくなったセルを集め再利用するものです。        

    これは言語デザインの上で単なる趣味の問題ではありません。
    明示的なデアロケーション操作が存在した場合、型安全性を保つのが極度に困難になるのです。
    その理由はよく知られたダングリング参照(_dangling reference_)問題です。
    数値を持つセルをアロケートし、何かのデータ構造にそれへの参照を持たせ、それをしばらく利用し、
    そしてそれをデアロケートし、ブール値を持つ新しいセルをアロケートします。
    このとき同じ記憶領域が再利用されるかもしれません。
    すると、同じ記憶セルに2つの名前があることになります。1つは [Ref Nat] 型で、
    もう1つは [Ref Bool] 型です。 *)

(* **** Exercise: 1 star *)
(** **** 練習問題: ★ *)
(* Show how this can lead to a violation of type safety. *)
(** このことがどのように型安全性の破壊につながるのか示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(* * Operational Semantics *)
(** * 操作的意味 *)

(* ################################### *)
(* ** Locations *)
(** ** 場所(Locations) *)

(* The most subtle aspect of the treatment of references
    appears when we consider how to formalize their operational
    behavior.  One way to see why is to ask, "What should be the
    _values_ of type [Ref T]?"  The crucial observation that we need
    to take into account is that evaluating a [ref] operator should
    _do_ something -- namely, allocate some storage -- and the result
    of the operation should be a reference to this storage.

    What, then, is a reference?

    The run-time store in most programming language implementations is
    essentially just a big array of bytes.  The run-time system keeps track
    of which parts of this array are currently in use; when we need to
    allocate a new reference cell, we allocate a large enough segment from
    the free region of the store (4 bytes for integer cells, 8 bytes for
    cells storing [Float]s, etc.), mark it as being used, and return the
    index (typically, a 32- or 64-bit integer) of the start of the newly
    allocated region.  These indices are references.

    For present purposes, there is no need to be quite so concrete.
    We can think of the store as an array of _values_, rather than an
    array of bytes, abstracting away from the different sizes of the
    run-time representations of different values.  A reference, then,
    is simply an index into the store.  (If we like, we can even
    abstract away from the fact that these indices are numbers, but
    for purposes of formalization in Coq it is a bit more convenient
    to use numbers.)  We'll use the word _location_ instead of
    _reference_ or _pointer_ from now on to emphasize this abstract
    quality.

    Treating locations abstractly in this way will prevent us from
    modeling the _pointer arithmetic_ found in low-level languages
    such as C.  This limitation is intentional.  While pointer
    arithmetic is occasionally very useful, especially for
    implementing low-level services such as garbage collectors, it
    cannot be tracked by most type systems: knowing that location [n]
    in the store contains a [float] doesn't tell us anything useful
    about the type of location [n+4].  In C, pointer arithmetic is a
    notorious source of type safety violations. *)
(** 参照の扱いについての一番些細な面は、
    操作的振る舞いをどのように形式化するかを考えるときに現れます。
    それが何故かを見る1つの方法は、「何が型 [Ref T] の値であるべきか？」と問うことです。
    考慮すべき重要な点は、[ref]演算子の評価は何かを(つまり記憶領域のアロケートを)
    「行わ」なければならず、    
    操作の結果はこの記憶領域への参照とならなければならないということです。

    それでは、参照とは何でしょうか？

    ほとんどのプログラミング言語の実装では、実行時の記憶領域は本質的にはバイト(byte)
    の(大きな)配列です。
    実行時システムは、この配列のどの部分が現在使用されているかを常に監視しています。
    新しい参照セルをアロケートしなければならないとき、
    記憶領域の自由範囲から十分な大きさのセグメント
    (整数セルには4バイト、[Float]のセルには8バイト、等)をアロケートします。
    このセグメントに「使用中」のマークをして、新しくアロケートされた領域のインデックス
    (典型的には32ビットまたは64ビットの整数)を返却します。
    参照とはこのインデックスのことです。

    現在の目的のためには、これほど具体的である必要はありません。
    記憶領域を、バイトではなく「値」の配列と考え、異なる値の実行時表現のサイズの違いは捨象します。
    すると参照は、単に記憶へのインデックスになります。
    (望むならば、これらのインデックスが数値であるという事実さえも捨象することができます。
    しかし、Coqで形式化する目的のためには、数値を使った方が若干便利です。)
    この抽象度であることを強調するため、これ以降、用語として、「参照」や「ポインタ」の代わりに
    「場所」(_location_)を使います。

    この方法で場所を抽象的に扱うことで、Cのような低レベルの言語で見られる「ポインタ算術」
    (_pointer arithmetic_)をモデル化することができなくなります。
    この制約は意図的なものです。ポインタ算術は時には非常に便利です。
    特にガベージコレクタのような低レベルのサービスを実装するときなどです。
    しかし、ほとんどの型システムではポインタ算術を追跡することができません。
    記憶領域の場所[n]に[float]が格納されていることを知っても、
    場所[n+4]の型について何も意味のあることはわかりません。
    Cにおいては、ポインタ算術は型安全性破壊の悪名高き源泉です。 *)

(* ################################### *)
(** ** Stores *)

(** Recall that, in the small-step operational semantics for
    IMP, the step relation needed to carry along an auxiliary state in
    addition to the program being executed.  In the same way, once we
    have added reference cells to the STLC, our step relation must
    carry along a store to keep track of the contents of reference
    cells.

    We could re-use the same functional representation we used for
    states in IMP, but for carrying out the proofs in this chapter it
    is actually more convenient to represent a store simply as a
    _list_ of values.  (The reason we couldn't use this representation
    before is that, in IMP, a program could modify any location at any
    time, so states had to be ready to map _any_ variable to a value.
    However, in the STLC with references, the only way to create a
    reference cell is with [tm_ref t1], which puts the value of [t1]
    in a new reference cell and evaluates to the location of the newly
    created reference cell. When evaluating such an expression, we can
    just add a new reference cell to the end of the list representing
    the store.) *)

Definition store := list tm.

(** We use [store_lookup n st] to retrieve the value of the reference
    cell at location [n] in the store [st].  Note that we must give a
    default value to [nth] in case we try looking up an index which is
    too large. (In fact, we will never actually do this, but proving
    it will of course require some work!) *)

Definition store_lookup (n:nat) (st:store) :=
  nth n st tm_unit.

(** To add a new reference cell to the store, we use [snoc]. *)

Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
  match l with
  | nil    => x :: nil
  | h :: t => h :: snoc t x
  end.

(** We will need some boring lemmas about [snoc].  The proofs are
    routine inductions. *)

Lemma length_snoc : forall A (l:list A) x,
  length (snoc l x) = S (length l).
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ]. Qed.

(* The "solve by inversion" tactic is explained in Stlc.v. *)
Lemma nth_lt_snoc : forall A (l:list A) x d n,
  n < length l ->
  nth n l d = nth n (snoc l x) d.
Proof.
  induction l as [|a l']; intros; try solve by inversion.
  Case "l = a :: l'".
    destruct n; auto.
    simpl. apply IHl'.
    simpl in H. apply lt_S_n in H. assumption.
Qed.

Lemma nth_eq_snoc : forall A (l:list A) x d,
  nth (length l) (snoc l x) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.

(** To update the store, we use the [replace] function, which replaces
    the contents of a cell at a particular index. *)

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil    => nil
  | h :: t =>
    match n with
    | O    => x :: t
    | S n' => h :: replace n' x t
    end
  end.

(** Of course, we also need some boring lemmas about [replace], which
    are also fairly straightforward to prove. *)

Lemma replace_nil : forall A n (x:A),
  replace n x [] = [].
Proof.
  destruct n; auto.
Qed.

Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.

Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  Case "st = []".
   inversion Hlen.
  Case "st = t' :: st'".
    destruct l; simpl...
    apply IHst'. simpl in Hlen. omega.
Qed.

Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  Case "l1 = 0".
    destruct st.
    SCase "st = []". rewrite replace_nil...
    SCase "st = _ :: _". destruct l2... contradict Hneq...
  Case "l1 = S l1'".
    destruct st as [|t2 st2].
    SCase "st = []". destruct l2...
    SCase "st = t2 :: st2".
      destruct l2...
      simpl; apply IHl1'...
Qed.

(* ################################### *)
(** ** Reduction *)

(** Next, we need to extend our operational semantics to take stores
    into account.  Since the result of evaluating an expression will
    in general depend on the contents of the store in which it is
    evaluated, the evaluation rules should take not just a term but
    also a store as argument.  Furthermore, since the evaluation of a
    term may cause side effects on the store that may affect the
    evaluation of other terms in the future, the evaluation rules need
    to return a new store.  Thus, the shape of the single-step
    evaluation relation changes from [t ==> t'] to [t / st ==> t' /
    st'], where [st] and [st'] are the starting and ending states of
    the store.

    To carry through this change, we first need to augment all of our
    existing evaluation rules with stores:
[[[
                               value v2
                -------------------------------------               (ST_AppAbs)
                (\a:T.t12) v2 / st ==> [v2/a]t12 / st

                        t1 / st ==> t1' / st'
                     ---------------------------                      (ST_App1)
                     t1 t2 / st ==> t1' t2 / st'

                  value v1     t2 / st ==> t2' / st'
                  ----------------------------------                  (ST_App2)
                     v1 t2 / st ==> v1 t2' / st'
]]]
    Note that the first rule here returns the store unchanged:
    function application, in itself, has no side effects.  The other two
    rules simply propagate side effects from premise to conclusion.

    Now, the result of evaluating a [ref] expression will be a fresh
    location; this is why we included locations in the syntax of terms
    and in the set of values.

    It is crucial to note that making this extension to the syntax of
    terms does not mean that we intend _programmers_ to write terms
    involving explicit, concrete locations: such terms will arise only
    as intermediate results of evaluation.  This may initially seem
    odd, but really it follows naturally from our design decision to
    represent the result of every evaluation step by a modified
    term. If we had chosen a more "machine-like" model for evaluation,
    e.g. with an explicit stack to contain values of bound
    identifiers, then the idea of adding locations to the set of
    allowed values would probably seem more obvious.

    In terms of this expanded syntax, we can state evaluation rules for
    the new constructs that manipulate locations and the store.  First, to
    evaluate a dereferencing expression [!t1], we must first reduce [t1]
    until it becomes a value:
[[[
                        t1 / st ==> t1' / st'
                       -----------------------                       (ST_Deref)
                       !t1 / st ==> !t1' / st'
]]]
    Once [t1] has finished reducing, we should have an expression of
    the form [!l], where [l] is some location.  (A term that attempts
    to dereference any other sort of value, such as a function or
    [unit], is erroneous, as is a term that tries to derefence a
    location that is larger than the size [|st|] of the currently
    allocated store; the evaluation rules simply get stuck in this
    case.  The type safety properties that we'll establish below
    assure us that well-typed terms will never misbehave in this way.)
[[[
                               l < |st|
                     ----------------------------------           (ST_DerefLoc)
                     !(loc l) / st ==> lookup l st / st
]]]

    Next, to evaluate an assignment expression [t1:=t2], we must first
    evaluate [t1] until it becomes a value (a location), and then
    evaluate [t2] until it becomes a value (of any sort):
[[[
                        t1 / st ==> t1' / st'
                 -----------------------------------               (ST_Assign1)
                 t1 := t2 / st ==> t1' := t2 / st'

                        t2 / st ==> t2' / st'
                  ---------------------------------                (ST_Assign2)
                  v1 := t2 / st ==> v1 := t2' / st'
]]]
    Once we have finished with [t1] and [t2], we have an expression of
    the form [l:=v2], which we execute by updating the store to make
    location [l] contain [v2]:
[[[
                               l < |st|
                -------------------------------------               (ST_Assign)
                loc l := v2 / st ==> unit / [v2/l]st
]]]
    The notation [[v2/l]st] means "the store that maps [l] to [v2]
    and maps all other locations to the same thing as [st.]"  Note
    that the term resulting from this evaluation step is just [unit];
    the interesting result is the updated store.)

    Finally, to evaluate an expression of the form [ref t1], we first
    evaluate [t1] until it becomes a value:
[[[
                        t1 / st ==> t1' / st'
                    -----------------------------                      (ST_Ref)
                    ref t1 / st ==> ref t1' / st'
]]]
    Then, to evaluate the [ref] itself, we choose a fresh location at
    the end of the current store -- i.e., location [|st|] -- and yield
    a new store that extends [st] with the new value [v1].
[[[
                   --------------------------------               (ST_RefValue)
                   ref v1 / st ==> loc |st| / st,v1
]]]
    The value resulting from this step is the newly allocated location
    itself.  (Formally, [st,v1] means [snoc st v1].)

    Note that these evaluation rules do not perform any kind of
    garbage collection: we simply allow the store to keep growing
    without bound as evaluation proceeds.  This does not affect the
    correctness of the results of evaluation (after all, the
    definition of "garbage" is precisely parts of the store that are
    no longer reachable and so cannot play any further role in
    evaluation), but it means that a naive implementation of our
    evaluator might sometimes run out of memory where a more
    sophisticated evaluator would be able to continue by reusing
    locations whose contents have become garbage.

    Formally... *)

Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x T t12 v2 st,
         value v2 ->
         tm_app (tm_abs x T t12) v2 / st ==> subst x v2 t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st ==> t1' / st' ->
         tm_app t1 t2 / st ==> tm_app t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tm_app v1 t2 / st ==> tm_app v1 t2'/ st'
  | ST_SuccNat : forall n st,
         tm_succ (tm_nat n) / st ==> tm_nat (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tm_succ t1 / st ==> tm_succ t1' / st'
  | ST_PredNat : forall n st,
         tm_pred (tm_nat n) / st ==> tm_nat (pred n) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tm_pred t1 / st ==> tm_pred t1' / st'
  | ST_MultNats : forall n1 n2 st,
         tm_mult (tm_nat n1) (tm_nat n2) / st ==> tm_nat (mult n1 n2) / st
  | ST_Mult1 : forall t1 t2 t1' st st',
         t1 / st ==> t1' / st' ->
         tm_mult t1 t2 / st ==> tm_mult t1' t2 / st'
  | ST_Mult2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tm_mult v1 t2 / st ==> tm_mult v1 t2' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st ==> t1' / st' ->
         tm_if0 t1 t2 t3 / st ==> tm_if0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
         tm_if0 (tm_nat 0) t2 t3 / st ==> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         tm_if0 (tm_nat (S n)) t2 t3 / st ==> t3 / st
  | ST_RefValue : forall v1 st,
         value v1 ->
         tm_ref v1 / st ==> tm_loc (length st) / snoc st v1
  | ST_Ref : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tm_ref t1 /  st ==> tm_ref t1' /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         tm_deref (tm_loc l) / st ==> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st ==> t1' / st' ->
         tm_deref t1 / st ==> tm_deref t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < length st ->
         tm_assign (tm_loc l) v2 / st ==> tm_unit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st ==> t1' / st' ->
         tm_assign t1 t2 / st ==> tm_assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st ==> t2' / st' ->
         tm_assign v1 t2 / st ==> tm_assign v1 t2' / st'

where "t1 '/' st1 '==>' t2 '/' st2" := (step (t1,st1) (t2,st2)).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2" | Case_aux c "ST_SuccNat"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredNat"
  | Case_aux c "ST_Pred" | Case_aux c "ST_MultNats"
  | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
  | Case_aux c "ST_If0" | Case_aux c "ST_If0_Zero"
  | Case_aux c "ST_If0_Nonzero" | Case_aux c "ST_RefValue"
  | Case_aux c "ST_Ref" | Case_aux c "ST_DerefLoc"
  | Case_aux c "ST_Deref" | Case_aux c "ST_Assign"
  | Case_aux c "ST_Assign1" | Case_aux c "ST_Assign2" ].

Hint Constructors step.

Definition stepmany := (refl_step_closure step).
Notation "t1 '/' st '==>*' t2 '/' st'" := (stepmany (t1,st) (t2,st'))
  (at level 40, st at level 39, t2 at level 39).

(* ################################### *)
(** * Typing *)

(** Our contexts for free variables will be exactly the same as for
    the STLC, partial maps from identifiers to types. *)

Definition context := partial_map ty.

(* ################################### *)

(** ** Store typings *)

(** Having extended our syntax and evaluation rules to accommodate
    references, our last job is to write down typing rules for the new
    constructs -- and, of course, to check that they are sound.
    Naturally, the key question is, "What is the type of a location?"

    First of all, notice that we do _not_ need to answer this question
    for purposes of typechecking the terms that programmers actually
    write.  Concrete location constants arise only in terms that are
    the intermediate results of evaluation; they are not in the
    language that programmers write.  So we only need to determine the
    type of a location when we're in the middle of an evaluation
    sequence, e.g. trying to apply the progress or preservation
    lemmas.  Thus, even though we normally think of typing as a
    _static_ program property, it makes sense for the typing of
    locations to depend on the _dynamic_ progress of the program too.

    As a first try, note that when we evaluate a term containing
    concrete locations, the type of the result depends on the contents
    of the store that we start with.  For example, if we evaluate the
    term [!(loc 1)] in the store [[unit, unit]], the result is [unit];
    if we evaluate the same term in the store [[unit, \x:Unit.x]], the
    result is [\x:Unit.x].  With respect to the former store, the
    location [1] has type [Unit], and with respect to the latter it
    has type [Unit->Unit]. This observation leads us immediately to a
    first attempt at a typing rule for locations:
[[[
                             Gamma |- lookup  l st : T1
                            ----------------------------
                             Gamma |- loc l : Ref T1
]]]
    That is, to find the type of a location [l], we look up the
    current contents of [l] in the store and calculate the type [T1]
    of the contents.  The type of the location is then [Ref T1].

    Having begun in this way, we need to go a little further to reach a
    consistent state.  In effect, by making the type of a term depend on
    the store, we have changed the typing relation from a three-place
    relation (between contexts, terms, and types) to a four-place relation
    (between contexts, _stores_, terms, and types).  Since the store is,
    intuitively, part of the context in which we calculate the type of a
    term, let's write this four-place relation with the store to the left
    of the turnstile: [Gamma; st |- t : T].  Our rule for typing
    references now has the form
[[[
                     Gamma; st |- lookup l st : T1
                   --------------------------------
                     Gamma; st |- loc l : Ref T1
]]]
    and all the rest of the typing rules in the system are extended
    similarly with stores.  The other rules do not need to do anything
    interesting with their stores -- just pass them from premise to
    conclusion.

    However, there are two problems with this rule.  First, typechecking
    is rather inefficient, since calculating the type of a location [l]
    involves calculating the type of the current contents [v] of [l].  If
    [l] appears many times in a term [t], we will re-calculate the type of
    [v] many times in the course of constructing a typing derivation for
    [t].  Worse, if [v] itself contains locations, then we will have to
    recalculate _their_ types each time they appear.

    Second, the proposed typing rule for locations may not allow us to
    derive anything at all, if the store contains a _cycle_.  For example,
    there is no finite typing derivation for the location [0] with respect
    to this store:
<<
   [\x:Nat. (!(loc 1)) x, \x:Nat. (!(loc 0)) x]
>>
*)
(** **** Exercise: 2 stars *)
(** Can you find a term whose evaluation will create this particular
    cyclic store? *)

(** [] *)

(** Both of these problems arise from the fact that our proposed
    typing rule for locations requires us to recalculate the type of a
    location every time we mention it in a term.  But this,
    intuitively, should not be necessary.  After all, when a location
    is first created, we know the type of the initial value that we
    are storing into it.  Suppose we are willing to enforce the
    invariant that the type of the value contained in a given location
    _never changes_; that is, although we may later store other values
    into this location, those other values will always have the same
    type as the initial one.  In other words, we always have in mind a
    single, definite type for every location in the store, which is
    fixed when the location is allocated.  Then these intended types
    can be collected together as a _store typing_ ---a finite function
    mapping locations to types.

    As usual, this _conservative_ typing restriction on allowed
    updates means that we will rule out as ill-typed some programs
    that could evaluate perfectly well without getting stuck.
*)

(** Just like we did for stores, we will represent a store type simply
    as a list of types: the type at index [i] records the type of the
    value stored in cell [i]. *)

Definition store_ty := list ty.

(** The [store_ty_lookup] function retrieves the type at a particular
    index. *)

Definition store_ty_lookup (n:nat) (ST:store_ty) :=
  nth n ST ty_Unit.

(** Suppose we are _given_ a store typing [ST] describing the store
    [st] in which some term [t] will be evaluated.  Then we can use
    [ST] to calculate the type of the result of [t] without ever
    looking directly at [st].  For example, if [ST] is [[Unit,
    Unit->Unit]], then we may immediately infer that [!(loc 1)] has
    type [Unit->Unit].  More generally, the typing rule for locations
    can be reformulated in terms of store typings like this:
[[[
                                 l < |ST|
                   -------------------------------------
                   Gamma; ST |- loc l : Ref (lookup l ST)
]]]

    That is, as long as [l] is a valid location (it is less than the
    length of [ST]), we can compute the type of [l] just by looking it
    up in [ST].  Typing is again a four-place relation, but it is
    parameterized on a store _typing_ rather than a concrete store.
    The rest of the typing rules are analogously augmented with store
    typings.  *)

(* ################################### *)
(** ** The Typing Relation *)

(** We can now give the typing relation for the STLC with
    references.  Here, again, are the rules we're adding to the base
    STLC (with numbers and [Unit]): *)

(**
[[[
                               l < |ST|
                  --------------------------------------              (T_Loc)
                  Gamma; ST |- loc l : Ref (lookup l ST)

                         Gamma; ST |- t1 : T1
                     ----------------------------                     (T_Ref)
                     Gamma; ST |- ref t1 : Ref T1

                      Gamma; ST |- t1 : Ref T11
                      -------------------------                       (T_Deref)
                        Gamma; ST |- !t1 : T11

                      Gamma; ST |- t1 : Ref T11
                        Gamma; ST |- t2 : T11
                    -----------------------------                    (T_Assign)
                    Gamma; ST |- t1 := t2 : Unit
]]]
*)

Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall Gamma ST x T,
      Gamma x = Some T ->
      has_type Gamma ST (tm_var x) T
  | T_Abs : forall Gamma ST x T11 T12 t12,
      has_type (extend Gamma x T11) ST t12 T12 ->
      has_type Gamma ST (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T1 T2 Gamma ST t1 t2,
      has_type Gamma ST t1 (ty_arrow T1 T2) ->
      has_type Gamma ST t2 T1 ->
      has_type Gamma ST (tm_app t1 t2) T2
  | T_Nat : forall Gamma ST n,
      has_type Gamma ST (tm_nat n) ty_Nat
  | T_Succ : forall Gamma ST t1,
      has_type Gamma ST t1 ty_Nat ->
      has_type Gamma ST (tm_succ t1) ty_Nat
  | T_Pred : forall Gamma ST t1,
      has_type Gamma ST t1 ty_Nat ->
      has_type Gamma ST (tm_pred t1) ty_Nat
  | T_Mult : forall Gamma ST t1 t2,
      has_type Gamma ST t1 ty_Nat ->
      has_type Gamma ST t2 ty_Nat ->
      has_type Gamma ST (tm_mult t1 t2) ty_Nat
  | T_If0 : forall Gamma ST t1 t2 t3 T,
      has_type Gamma ST t1 ty_Nat ->
      has_type Gamma ST t2 T ->
      has_type Gamma ST t3 T ->
      has_type Gamma ST (tm_if0 t1 t2 t3) T
  | T_Unit : forall Gamma ST,
      has_type Gamma ST tm_unit ty_Unit
  | T_Loc : forall Gamma ST l,
      l < length ST ->
      has_type Gamma ST (tm_loc l) (ty_Ref (store_ty_lookup l ST))
  | T_Ref : forall Gamma ST t1 T1,
      has_type Gamma ST t1 T1 ->
      has_type Gamma ST (tm_ref t1) (ty_Ref T1)
  | T_Deref : forall Gamma ST t1 T11,
      has_type Gamma ST t1 (ty_Ref T11) ->
      has_type Gamma ST (tm_deref t1) T11
  | T_Assign : forall Gamma ST t1 t2 T11,
      has_type Gamma ST t1 (ty_Ref T11) ->
      has_type Gamma ST t2 T11 ->
      has_type Gamma ST (tm_assign t1 t2) ty_Unit.

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Mult" | Case_aux c "T_If0"
  | Case_aux c "T_Unit" | Case_aux c "T_Loc"
  | Case_aux c "T_Ref" | Case_aux c "T_Deref"
  | Case_aux c "T_Assign" ].

(** Of course, these typing rules will accurately predict the results
    of evaluation only if the concrete store used during evaluation
    actually conforms to the store typing that we assume for purposes
    of typechecking.  This proviso exactly parallels the situation
    with free variables in the STLC: the substitution lemma promises
    us that, if [Gamma |- t : T], then we can replace the free
    variables in [t] with values of the types listed in [Gamma] to
    obtain a closed term of type [T], which, by the type preservation
    theorem will evaluate to a final result of type [T] if it yields
    any result at all.  (We will see later how to formalize an
    analogous intuition for stores and store typings.)

    However, for purposes of typechecking the terms that programmers
    actually write, we do not need to do anything tricky to guess what
    store typing we should use.  Recall that concrete location
    constants arise only in terms that are the intermediate results of
    evaluation; they are not in the language that programmers write.
    Thus, we can simply typecheck the programmer's terms with respect
    to the _empty_ store typing.  As evaluation proceeds and new
    locations are created, we will always be able to see how to extend
    the store typing by looking at the type of the initial values
    being placed in newly allocated cells; this intuition is
    formalized in the statement of the type preservation theorem
    below.  *)

(* ################################### *)
(** * Properties *)

(** Our final task is to check that standard type safety properties
    continue to hold for the STLC with references.  The progress
    theorem ("well-typed terms are not stuck") can be stated and
    proved almost as for the STLC; we just need to add a few
    straightforward cases to the proof, dealing with the new
    constructs.  The preservation theorem is a bit more interesting,
    so let's look at it first.  *)

(* ################################### *)
(** ** Well-Typed Stores *)

(** Since we have extended both the evaluation relation (with initial
    and final stores) and the typing relation (with a store typing),
    we need to change the statement of preservation to include these
    parameters.  Clearly, though, we cannot just add stores and store
    typings without saying anything about how they are related: *)

Theorem preservation_wrong1 : forall ST T t st t' st',
  has_type empty ST t T ->
  t / st ==> t' / st' ->
  has_type empty ST t' T.
Admitted.

(** If we typecheck with respect to some set of assumptions about the
    types of the values in the store and then evaluate with respect to
    a store that violates these assumptions, the result will be
    disaster.  We say that a store [st] is _well typed_ with respect a
    store typing [ST] if the term at each location [l] in [st] has the
    type at location [l] in [ST].  Since only closed terms ever get
    stored in locations (why?), it suffices to type them in the empty
    context. The following definition of [store_well_typed] formalizes
    this.  *)

Definition store_well_typed (ST:store_ty) (st:store) :=
  length ST = length st /\
  (forall l, l < length st ->
     has_type empty ST (store_lookup l st) (store_ty_lookup l ST)).

(** Informally, we will write [ST |- st] for [store_well_typed ST st]. *)

(** Intuitively, a store [st] is consistent with a store typing
    [ST] if every value in the store has the type predicted by the
    store typing.  (The only subtle point is the fact that, when
    typing the values in the store, we supply the very same store
    typing to the typing relation!  This allows us to type circular
    stores.) *)

(** **** Exercise: 2 stars *)
(** Can you find a store [st], and two
    different store typings [ST1] and [ST2] such that both
    [ST1 |- st] and [ST2 |- st]? *)

(* FILL IN HERE *)
(** [] *)

(** We can now state something closer to the desired preservation
    property: *)

Theorem preservation_wrong2 : forall ST T t st t' st',
  has_type empty ST t T ->
  t / st ==> t' / st' ->
  store_well_typed ST st ->
  has_type empty ST t' T.
Admitted.

(** This statement is fine for all of the evaluation rules except the
    allocation rule [ST_RefValue].  The problem is that this rule
    yields a store with a larger domain than the initial store, which
    falsifies the conclusion of the above statement: if [st']
    includes a binding for a fresh location [l], then [l] cannot be in
    the domain of [ST], and it will not be the case that [t']
    (which definitely mentions [l]) is typable under [ST]. *)

(* ############################################ *)
(** ** Extending Store Typings *)

(** Evidently, since the store can increase in size during evaluation,
    we need to allow the store typing to grow as well.  This motivates
    the following definition.  We say that the store type [ST']
    _extends_ [ST] if [ST'] is just [ST] with some new types added to
    the end. *)

Inductive extends : store_ty -> store_ty -> Prop :=
  | extends_nil  : forall ST',
      extends ST' nil
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).

Hint Constructors extends.

(** We'll need a few technical lemmas about extended contexts.

    First, looking up a type in an extended store typing yields the
    same result as in the original: *)

Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_ty_lookup l ST' = store_ty_lookup l ST.
Proof with auto.
  intros l ST ST' Hlen H.
  generalize dependent ST'. generalize dependent l.
  induction ST as [|a ST2]; intros l Hlen ST' HST'.
  Case "nil". inversion Hlen.
  Case "cons". unfold store_ty_lookup in *.
    destruct ST' as [|a' ST'2].
    SCase "ST' = nil". inversion HST'.
    SCase "ST' = a' :: ST'2".
      inversion HST'; subst.
      destruct l as [|l'].
      SSCase "l = 0"...
      SSCase "l = S l'". simpl. apply IHST2...
        simpl in Hlen; omega.
Qed.

(** Next, if [ST'] extends [ST], the length of [ST'] is at least that
    of [ST]. *)

Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    inversion Hlen.
    simpl in *.
    destruct l; try omega.
      apply lt_n_S. apply IHextends. omega.
Qed.

(** Finally, [snoc ST T] extends [ST], and [extends] is reflexive. *)

Lemma extends_snoc : forall ST T,
  extends (snoc ST T) ST.
Proof with auto.
  induction ST; intros T...
  simpl...
Qed.

Lemma extends_refl : forall ST,
  extends ST ST.
Proof.
  induction ST; auto.
Qed.

(* ################################### *)
(** ** Preservation, Finally *)

(** We can now give the final, correct statement of the type
    preservation property: *)

Definition preservation_theorem := forall ST t t' T st st',
  has_type empty ST t T ->
  store_well_typed ST st ->
  t / st ==> t' / st' ->
  exists ST',
    (extends ST' ST /\
     has_type empty ST' t' T /\
     store_well_typed ST' st').

(** Note that the preservation theorem merely asserts that there is
    _some_ store typing [ST'] extending [ST] (i.e., agreeing with [ST]
    on the values of all the old locations) such that the new term
    [t'] is well typed with respect to [ST']; it does not tell us
    exactly what [ST'] is.  It is intuitively clear, of course, that
    [ST'] is either [ST] or else it is exactly [snoc ST T1], where
    [T1] is the type of the value [v1] in the extended store [snoc st
    v1], but stating this explicitly would complicate the statement of
    the theorem without actually making it any more useful: the weaker
    version above is already in the right form (because its conclusion
    implies its hypothesis) to "turn the crank" repeatedly and
    conclude that every _sequence_ of evaluation steps preserves
    well-typedness.  Combining this with the progress property, we
    obtain the usual guarantee that "well-typed programs never go
    wrong."

    In order to prove this, we'll need a few lemmas, as usual. *)

(* ################################### *)
(** ** Substitution lemma *)

(** First, we need an easy extension of the standard substitution
    lemma, along with the same machinery about context invariance that
    we used in the proof of the substitution lemma for the STLC. *)

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
  | afi_succ : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tm_succ t1)
  | afi_pred : forall x t1,
      appears_free_in x t1 ->
      appears_free_in x (tm_pred t1)
  | afi_mult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_mult t1 t2)
  | afi_mult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_mult t1 t2)
  | afi_if0_1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tm_if0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tm_if0 t1 t2 t3)
  | afi_if0_3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tm_if0 t1 t2 t3)
  | afi_ref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (tm_ref t1)
  | afi_deref : forall x t1,
      appears_free_in x t1 -> appears_free_in x (tm_deref t1)
  | afi_assign1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_assign t1 t2)
  | afi_assign2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_assign t1 t2).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" | Case_aux c "afi_abs"
  | Case_aux c "afi_succ" | Case_aux c "afi_pred"
  | Case_aux c "afi_mult1" | Case_aux c "afi_mult2"
  | Case_aux c "afi_if0_1" | Case_aux c "afi_if0_2" | Case_aux c "afi_if0_3"
  | Case_aux c "afi_ref" | Case_aux c "afi_deref"
  | Case_aux c "afi_assign1" | Case_aux c "afi_assign2" ].

Hint Constructors appears_free_in.

Lemma free_in_context : forall x t T Gamma ST,
   appears_free_in x t ->
   has_type Gamma ST t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros. generalize dependent Gamma. generalize dependent T.
  afi_cases (induction H) Case;
        intros; (try solve [ inversion H0; subst; eauto ]).
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H8.
    apply not_eq_beq_id_false in H.
    rewrite extend_neq in H8; assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' ST t T,
  has_type Gamma ST t T ->
  (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
  has_type Gamma' ST t T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros...
  Case "T_Var".
    apply T_Var. symmetry. rewrite <- H...
  Case "T_Abs".
    apply T_Abs. apply IHhas_type; intros.
    unfold extend.
    remember (beq_id x x0) as e; destruct e...
    apply H0. apply afi_abs. apply beq_id_false_not_eq... auto.
  Case "T_App".
    eapply T_App.
      apply IHhas_type1...
      apply IHhas_type2...
  Case "T_Mult".
    eapply T_Mult.
      apply IHhas_type1...
      apply IHhas_type2...
  Case "T_If0".
    eapply T_If0.
      apply IHhas_type1...
      apply IHhas_type2...
      apply IHhas_type3...
  Case "T_Assign".
    eapply T_Assign.
      apply IHhas_type1...
      apply IHhas_type2...
Qed.

Lemma substitution_preserves_typing : forall Gamma ST x s S t T,
  has_type empty ST s S ->
  has_type (extend Gamma x S) ST t T ->
  has_type Gamma ST (subst x s t) T.
Proof with eauto.
  intros Gamma ST x s S t T Hs Ht.
  generalize dependent Gamma. generalize dependent T.
  tm_cases (induction t) Case; intros T Gamma H;
    inversion H; subst; simpl...
  Case "tm_var".
    rename i into y.
    remember (beq_id x y) as eq; destruct eq; subst.
    SCase "x = y".
      apply beq_id_eq in Heqeq; subst.
      rewrite extend_eq in H3.
      inversion H3; subst.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ _ _ _ Hcontra Hs) as [T' HT'].
      inversion HT'.
    SCase "x <> y".
      apply T_Var.
      rewrite extend_neq in H3...
  Case "tm_abs". subst.
    rename i into y.
    remember (beq_id x y) as eq; destruct eq.
    SCase "x = y".
      apply beq_id_eq in Heqeq; subst.
      apply T_Abs. eapply context_invariance...
      intros. apply extend_shadow.
    SCase "x <> x0".
      apply T_Abs. apply IHt.
      eapply context_invariance...
      intros. unfold extend.
      remember (beq_id y x0) as e. destruct e...
      apply beq_id_eq in Heqe; subst.
      rewrite <- Heqeq...
Qed.

(* ################################### *)
(** ** Assignment Preserves Store Typing *)

(** Next, we must show that replacing the contents of a cell in the
    store with a new value of appropriate type does not change the
    overall type of the store.  (This is needed for the [ST_Assign]
    rule.) *)

Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  store_well_typed ST st ->
  has_type empty ST t (store_ty_lookup l ST) ->
  store_well_typed ST (replace l t st).
Proof with auto.
  intros ST st l t Hlen HST Ht.
  inversion HST; subst.
  split. rewrite length_replace...
  intros l' Hl'.
  remember (beq_nat l' l) as ll'; destruct ll'.
  Case "l' = l".
    apply beq_nat_eq in Heqll'; subst.
    rewrite lookup_replace_eq...
  Case "l' <> l".
    symmetry in Heqll'; apply beq_nat_false in Heqll'.
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H0...
Qed.

(* ######################################## *)
(** ** Weakening for Stores *)

(** Finally, we need a lemma on store typings, stating that, if a
    store typing is extended with a new location, the extended one
    still allows us to assign the same types to the same terms as the
    original.

    (The lemma is called [store_weakening] because it resembles the
    "weakening" lemmas found in proof theory, which show that adding a
    new assumption to some logical theory does not decrease the set of
    provable theorems.) *)

Lemma store_weakening : forall Gamma ST ST' t T,
  extends ST' ST ->
  has_type Gamma ST t T ->
  has_type Gamma ST' t T.
Proof with eauto.
  intros. has_type_cases (induction H0) Case; eauto.
  Case "T_Loc".
    erewrite <- extends_lookup...
    apply T_Loc.
    eapply length_extends...
Qed.

(** We can use the [store_weakening] lemma to prove that if a store is
    well-typed with respect to a store typing, then the store extended
    with a new term [t] will still be well-typed with respect to the
    store typing extended with [t]'s type. *)

Lemma store_well_typed_snoc : forall ST st t1 T1,
  store_well_typed ST st ->
  has_type empty ST t1 T1 ->
  store_well_typed (snoc ST T1) (snoc st t1).
Proof with auto.
  intros.
  unfold store_well_typed in *.
  inversion H as [Hlen Hmatch]; clear H.
  rewrite !length_snoc.
  split...
  Case "types match.".
    intros l Hl.
    unfold store_lookup, store_ty_lookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    SCase "l < length st".
      apply lt_S_n in Hlt.
      rewrite <- !nth_lt_snoc...
      apply store_weakening with ST. apply extends_snoc.
      apply Hmatch...
      rewrite Hlen...
    SCase "l = length st".
      inversion Heq.
      rewrite nth_eq_snoc.
      rewrite <- Hlen. rewrite nth_eq_snoc...
      apply store_weakening with ST... apply extends_snoc.
Qed.

(* ################################### *)
(** ** Preservation! *)

(** Now that we've got everything set up right, the proof of
    preservation is actually quite straightforward. *)

Theorem preservation : forall ST t t' T st st',
  has_type empty ST t T ->
  store_well_typed ST st ->
  t / st ==> t' / st' ->
  exists ST',
    (extends ST' ST /\
     has_type empty ST' t' T /\
     store_well_typed ST' st').
Proof with eauto using store_weakening, extends_refl.
    remember (@empty ty) as Gamma.
  intros ST t t' T st st' Ht.
  generalize dependent t'.
  has_type_cases (induction Ht) Case; intros t' HST Hstep;
    subst; try (solve by inversion); inversion Hstep; subst;
    try (eauto using store_weakening, extends_refl).
  Case "T_App".
    SCase "ST_AppAbs". exists ST.
      inversion Ht1; subst.
      split; try split... eapply substitution_preserves_typing...
    SCase "ST_App1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_App2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Succ".
    SCase "ST_Succ".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Pred".
    SCase "ST_Pred".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Mult".
    SCase "ST_Mult1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_Mult2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_If0".
    SCase "ST_If0_1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'... split...
  Case "T_Ref".
    SCase "ST_RefValue".
      exists (snoc ST T1).
      inversion HST; subst.
      split.
        apply extends_snoc.
      split.
        replace (ty_Ref T1)
          with (ty_Ref (store_ty_lookup (length st) (snoc ST T1))).
        apply T_Loc.
        rewrite <- H. rewrite length_snoc. omega.
        unfold store_ty_lookup. rewrite <- H. rewrite nth_eq_snoc...
        apply store_well_typed_snoc; assumption.
    SCase "ST_Ref".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Deref".
    SCase "ST_DerefLoc".
      exists ST. split; try split...
      destruct HST as [_ Hsty].
      replace T11 with (store_ty_lookup l ST).
      apply Hsty...
      inversion Ht; subst...
    SCase "ST_Deref".
      eapply IHHt in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
  Case "T_Assign".
    SCase "ST_Assign".
      exists ST. split; try split...
      eapply assign_pres_store_typing...
      inversion Ht1; subst...
    SCase "ST_Assign1".
      eapply IHHt1 in H0...
      inversion H0 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
    SCase "ST_Assign2".
      eapply IHHt2 in H5...
      inversion H5 as [ST' [Hext [Hty Hsty]]].
      exists ST'...
Qed.

(** **** Exercise: 3 stars (preservation_informal) *)
(** Write a careful informal proof of the preservation theorem,
    concentrating on the [T_App], [T_Deref], [T_Assign], and [T_Ref]
    cases.

(* FILL IN HERE *)
[] *)


(* ################################### *)
(** ** Progress *)

(** Fortunately, progress for this system is pretty easy to prove; the
    proof is very similar to the proof of progress for the STLC, with
    a few new cases for the new syntactic constructs. *)

Theorem progress : forall ST t T st,
  has_type empty ST t T ->
  store_well_typed ST st ->
  (value t \/ exists t', exists st', t / st ==> t' / st').
Proof with eauto.
    intros ST t T st Ht HST. remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst; try solve by inversion...
  Case "T_App".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve by inversion.
      destruct IHHt2 as [Ht2p | Ht2p]...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tm_app (tm_abs x T t) t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_app t1' t2). exists st'...
  Case "T_Succ".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [ inversion Ht ].
      SSCase "t1 is a tm_nat".
        exists (tm_nat (S n)). exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_succ t1'). exists st'...
  Case "T_Pred".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht ].
      SSCase "t1 is a tm_nat".
        exists (tm_nat (pred n)). exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_pred t1'). exists st'...
  Case "T_Mult".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct IHHt2 as [Ht2p | Ht2p]...
      SSCase "t2 is a value".
        inversion Ht2p; subst; try solve [inversion Ht2].
        exists (tm_nat (mult n n0)). exists st...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tm_mult (tm_nat n) t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_mult t1' t2). exists st'...
  Case "T_If0".
    right. destruct IHHt1 as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve [inversion Ht1].
      destruct n.
      SSCase "n = 0". exists t2. exists st...
      SSCase "n = S n'". exists t3. exists st...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_if0 t1' t2 t3). exists st'...
  Case "T_Ref".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_ref t1'). exists st'...
  Case "T_Deref".
    right. destruct IHHt as [Ht1p | Ht1p]...
    SCase "t1 is a value".
      inversion Ht1p; subst; try solve by inversion.
      eexists. eexists. apply ST_DerefLoc...
      inversion Ht; subst. inversion HST; subst.
      rewrite <- H...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_deref t1'). exists st'...
  Case "T_Assign".
    right. destruct IHHt1 as [Ht1p|Ht1p]...
    SCase "t1 is a value".
      destruct IHHt2 as [Ht2p|Ht2p]...
      SSCase "t2 is a value".
        inversion Ht1p; subst; try solve by inversion.
        eexists. eexists. apply ST_Assign...
        inversion HST; subst. inversion Ht1; subst.
        rewrite H in H5...
      SSCase "t2 steps".
        inversion Ht2p as [t2' [st' Hstep]].
        exists (tm_assign t1 t2'). exists st'...
    SCase "t1 steps".
      inversion Ht1p as [t1' [st' Hstep]].
      exists (tm_assign t1' t2). exists st'...
Qed.

(* ################################### *)
(** * References and Nontermination *)

Section RefsAndNontermination.
Import ExampleVariables.

(** We know that the simply typed lambda calculus is _normalizing_,
    that is, every well-typed term can be reduced to a value in a
    finite number of steps.  What about STLC + references?
    Surprisingly, adding references causes us to lose the
    normalization property: there exist well-typed terms in the STLC +
    references which can continue to reduce forever, without ever
    reaching a normal form!

    How can we construct such a term?  The main idea is to make a
    function which calls itself.  We first make a function which calls
    another function stored in a reference cell; the trick is that we
    then smuggle in a reference to itself!
<<
   (\r:Ref (Unit -> Unit).
        r := (\x:Unit.(!r) unit); (!r) unit)
   (ref (\x:Unit.unit))
>>

   First, [ref (\x:Unit.unit)] creates a reference to a cell of type
   [Unit -> Unit].  We then pass this reference as the argument to a
   function which binds it to the name [r], and assigns to it the
   function (\x:Unit.(!r) unit) -- that is, the function which
   ignores its argument and calls the function stored in [r] on the
   argument [unit]; but of course, that function is itself!  To get
   the ball rolling we finally execute this function with [(!r)
   unit].
*)

Definition loop_fun :=
  tm_abs x ty_Unit (tm_app (tm_deref (tm_var r)) tm_unit).

Definition loop :=
  tm_app
  (tm_abs r (ty_Ref (ty_arrow ty_Unit ty_Unit))
    (tm_seq (tm_assign (tm_var r) loop_fun)
            (tm_app (tm_deref (tm_var r)) tm_unit)))
  (tm_ref (tm_abs x ty_Unit tm_unit)).

(** This term is well-typed: *)

Lemma loop_typeable : exists T, has_type empty [] loop T.
Proof with eauto.
  eexists. unfold loop. unfold loop_fun.
  eapply T_App...
  eapply T_Abs...
  eapply T_App...
    eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
    unfold extend. simpl. reflexivity. auto.
  eapply T_Assign.
    eapply T_Var. unfold extend. simpl. reflexivity.
  eapply T_Abs.
    eapply T_App...
      eapply T_Deref. eapply T_Var. reflexivity.
Qed.

(** To show formally that the term diverges, we first define the
    [step_closure] of the single-step reduction relation, written
    [==>+].  This is just like the reflexive step closure of
    single-step reduction (which we're been writing [==>*]), except
    that it is not reflexive: [t ==>+ t'] means that [t] can reach
    [t'] by _one or more_ steps of reduction. *)

Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
  | sc_one  : forall (x y : X),
                R x y -> step_closure R x y
  | sc_step : forall (x y z : X),
                R x y ->
                step_closure R y z ->
                step_closure R x z.

Definition stepmany1 := (step_closure step).
Notation "t1 '/' st '==>+' t2 '/' st'" := (stepmany1 (t1,st) (t2,st'))
  (at level 40, st at level 39, t2 at level 39).

(** Now, we can show that the expression [loop] reduces to the
    expression [!(loc 0) unit] and the size-one store [ [(loc 0) / r]
    loop_fun]. *)

(** As a convenience, we introduce a slight variant of the [normalize]
    tactic, called [reduce], which tries solving the goal with
    [rsc_refl] at each step, instead of waiting until the goal can't
    be reduced any more. Of course, the whole point is that [loop]
    doesn't normalize, so the old [normalize] tactic would just go
    into an infinite loop reducing it forever! *)

Ltac print_goal := match goal with |- ?x => idtac x end.
Ltac reduce :=
    repeat (print_goal; eapply rsc_step ;
            [ (eauto 10; fail) | (instantiate; compute)];
            try solve [apply rsc_refl]).

Lemma loop_steps_to_loop_fun :
  loop / [] ==>*
  tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun].
Proof with eauto.
  unfold loop.
  reduce.
Qed.

(** Finally, the latter expression reduces in two steps to itself! *)

Lemma loop_fun_step_self :
  tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun] ==>+
  tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun].
Proof with eauto.
  unfold loop_fun; simpl.
  eapply sc_step. apply ST_App1...
  eapply sc_one. compute. apply ST_AppAbs...
Qed.

(** **** Exercise: 4 stars *)
(** Use the above ideas to implement a factorial function in STLC with
    references.  (There is no need to prove formally that it really
    behaves like the factorial.  Just use the example below to make
    sure it gives the correct result when applied to the argument
    [4].) *)

Definition factorial : tm :=
  (* FILL IN HERE *) admit.

Lemma factorial_type : has_type empty [] factorial (ty_arrow ty_Nat ty_Nat).
Proof with eauto.
  (* FILL IN HERE *) Admitted.

(** If your definition is correct, you should be able to just
    uncomment the example below; the proof should be fully
    automatic using the [reduce] tactic. *)

(*
Lemma factorial_4 : exists st,
  tm_app factorial (tm_nat 4) / [] ==>* tm_nat 24 / st.
Proof.
  eexists. unfold factorial. reduce.
Qed.
*)
(** [] *)

(* ################################### *)
(** * Additional Exercises *)

(** **** Exercise: 5 stars, optional *)
(** Challenge problem: modify our formalization to include an account
    of garbage collection, and prove that it satisfies whatever nice
    properties you can think to prove about it. *)

(** [] *)

End RefsAndNontermination.
End STLCRef.
