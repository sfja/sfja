(** * Basics_J: 関数プログラミングとプログラムの証明 *)


(** * 列挙型 *)

(** プログラミング言語Coqには、ほとんど何も（ブール型や数値型すら）ビルトインされていません。その代わりCoqには、新しい型やそれを処理するための強力なツールが用意されています。 *)


(** ** 曜日の表し方 *)

(** まず最初はとても簡単なサンプルから始めましょう。次の定義は、Coqに対して、新しいデータ型のセット（集合）である'型'を定義しています。その型は[day]で、要素は[monday]、[tuesday]...などです。その定義の1行は以下のようにも読めます。"[monday]は[day]。[tuesday]は[day]"といった具合です。
 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** "[day]"が何かを定義できれば、それを利用して関数を書くこともできるでしょう。 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(** 一つ注意しておかなければならないことがあります。この関数の定義では、引数の型と戻り値の型が明示されていることです。他の多くの関数型プログラミング言語と同様、Coqはこのように型を明示的に書かずともちゃんと動くようになっています。それはいわゆる「型推論」という機構によって実現されていますが、型を明示した方がプログラムを読みやすくできると判断するなら、いつでもそうしてかまいません。 *)

(** 関数の定義ができたら、いくつかの例を挙げてそれが正しいものであることをチェックしなければなりません。それを実現するために、Coqには三つの方法が用意されています。一つ目は「[Eval Simpl]」コマンドを使って、関数[next_weekday]を含んだ式を評価させることです。次のコマンドをよく見て、何をしているかを考えてみてください。 *)

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

(** もし今手元にコンピュータがあるなら、CoqのIDEのうち好きなもの（CoqIDEやProofGeneralなどから）を選んで起動し、実際に上のコマンドを入力し動かしてみるといいでしょう。付録の「[Basic.v]」ファイルから上のサンプルを探してCoqに読み込ませ、結果を観察してください。 *)

(** 「[simpl]（simplify）」というキーワードは、Coqに対して「我々が与えた式を正確に評価せよ」という命令です。しばらくの間、「[simpl]」コマンドは我々にとって必要な唯一のコマンドになるでしょう。この後でもう少し使い出のある別のコマンドを覚えるまでの間ですが。 *)

(** 二番目の方法は、評価の結果として我々が期待しているものをCoqに対してあらかじめ以下のような形で例示しておくというものです。 *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** この宣言は二つのことを行っています。ひとつは、[saturday]の次の次にあたる平日が、[tuesday]であるということを確認する必要があるということを示すこと。もう一つは、後で参照しやすいように、その確認事項に[test_next_weekday]という名前を与えていることです。
    この確認事項を定義すれば、次のようなコマンドを流すだけで、Coqによって正しさを検証できます。 *)

Proof. simpl. reflexivity.  Qed.

(** この文について細かいことは今は置いておきますが（じきに戻ってきます）、本質的には以下のような意味になります「我々が作成した確認事項は簡約後の同値チェックによって証明されました。」 *)

(** 三番目の方法は、Coqで[定義]したものから、他のより一般的な言語（OcamlやScheme、Haskellといった）のプログラムを抽出してしまうことです。この機能は今主流の言語で完全に確認されたプログラムを実現できる道を開いたという意味でとても興味深いものです。ここではこの件について深入りすることはしませんが、もしより深く知りたいという場合はCoq'Art book（Bertot and Casteran著）か、Coqリファレンスマニュアルを参照してください。 *)


(** ** ブール型 *)

(** 同様にして、[true]と[false]を値としてとる「[bool型]」を定義することができます。 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(**
このようにして、我々は独自のbool型を一から作りあげることもできるのですが、もちろんCoqには標準ライブラリとしてbool型が多くの有用な関数、補助定理と一緒に用意されています。（もし興味があるなら、CoqライブラリドキュメントのCoq.Init.Datatypesを参照してください。）ここでは可能な限り標準ライブラリと正確に同じ機能を、我々独自の名前で定義していくことにしましょう。 *)

(**ブール型を使用する関数は、Day型と同じように定義することができます。 *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** 後半の二つは、引数を複数持つ関数を定義する方法を示しています。 *)

(** 次の四つの単体テストは、関数[orb]が取り得るすべての引数についての完全な仕様（真理値表）となっています。 *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true) = true.
Proof. simpl. reflexivity.  Qed.

(** 記述方法について: .v ファイルのコメントの中に Coqのコード片を含める場合には、角括弧を使用してコメントと区切ります。この慣習は[coqdoc]というドキュメント作成ツールでも利用されているのですが、コード片を周囲のコメントから視覚的に分離することができます。CoqソースのHTML版では、ソースはコメントとは[別のフォント]で表示されます。 *)

(** 次にCoqでのちょっとトリッキーな定義（[admit]）を紹介しましょう。この[admit]は、定義や証明にある不完全な部分を「とりあえず今は無いこと」にしてくれるものです。これを次の[nandb]での練習問題に使ってみることにしましょう。ここからしばらく、練習問題を解くということは[admit]や[Admitted]と書かれた部分をちゃんとした定義や証明に書き直す作業になります。 *)

Definition admit {T: Type} : T.  Admitted.

(** **** 練習問題: ★ (nandb) *)
(** 次の定義を完成させ、[Example]で記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。  *)

(** この関数はどちらか、もしくは両方が[false]になったときに[true]を返すものである。 *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  (* FILL IN HERE *) admit.

(** 下の定義から[Admitted.]を取り去り、代わりに"[Proof. simpl. reflexivity. Qed.]"で検証できるようなコードを記述しなさい。 *)

Example test_nandb1:               (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (andb3) *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* ここを埋めなさい *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
(** [] *)


(** ** 関数の型 *)

(** [Check]コマンドを使うと、Coqに、指定した式の型を表示させることができます。例えば、（[negb true]）という式の全体の型は[bool]である、という具合です。 *)

Check (negb true).
(* ===> negb true : bool *)

(** [negb]のような関数は、それ自身が[true]や[false]と同じように値であると考えることもできます。そのようにとらえた場合の値の型を「関数型」と呼び、以下のように矢印を使った型として表します。 *)

Check negb.
(* ===> negb : bool -> bool *)

(** [negb]の型は[bool->bool]と書き、「[bool]から[bool]」と読み、[bool]型の引数をとって[bool]型の戻り値を返す関数と理解することができます。同様に、[andb]の型は[bool -> bool -> bool]と書き、「二つの[bool]型の値を引数として[bool]型の値を作成して戻す」と解釈します。 *)


(** ** 数値 *)

(** ちょっと技術的な話：Coqは大規模な開発を支援するためにちょっと大げさにも見えるモジュールシステムを提供しています。このコースではこれらはほとんど必要のないものですが、一つだけ有用なものがあります。プログラムの中のいくつかの要素を[Module X]と[End X]で囲んでおくと、[End X]以降の部分から、囲まれた中の定義を[X.foo]という風に呼び出すことができます。このことは、新しく[foo]という名前で関数を定義しても問題ないということです。逆に、同じスコープの中では、同じ名前での定義はエラーとなります。という訳で、今回我々はこの機能を使って[nat]という型を内部モジュールとして定義します。そうすることで、標準ライブラリの同じ名前の定義を覆い隠してしまわずに済みます。 *)

Module Playground1.

(** 我々がここまでで定義してきた型は「列挙型」の型定義でした。このような型は、有限の要素をすべて列挙することによって定義されます。型を定義するもう一つの方法は、「帰納的な記述」を並べることで要素を記述する方法です。例えば、自然数は（全て並べるわけにはいきませんが）以下のような方法で定義できます。 *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** この定義の各句は、以下のように解釈できます。
      - [O]は自然数である（[0]（ゼロ）ではなく"[O]"（オー）であることに注意）
      - [S]は自然数を引数にとり、別の自然数を生成する「コンストラクタ」である。このことは、[n]が自然数なら[S n]も自然数であることを示している。

    この定義にして、もう少し詳しく見ていきましょう。

    これまでに定義してきた帰納的な型（[weekday]、[nat]、[bool]など）は、実際には式の集合とでも言うべきものです。[nat]の定義は、[nat]の要素となる式がどのように構築されるかを表しています。

    - 式[O]（オー）は、[nat]に属する。
    - もし[n]が[nat]に属するならば、[S n]もまた[nat]に属する。
    - これら二つの方法で表された式のみが[nat]に属するものの全てである。*)

(** これら三つの条件によって、[nat]が帰納的([Inductive])な方法で厳格に定義されています。この定義によって、式 [O]、式 [S O]、式  [S (S O)]、式 [S (S (S O))]...が全て[nat]に属する式であることが表されています。また同時に、[true]や[andb true false]、[S (S false)]が[nat]に属さないことも明確にされています。

こうして定義された自然数[nat]をマターンマッチにかけることで、簡単な関数を書いてみましょう。例えば、一つ前の[nat]を返す関数は以下のよう書けます。
 *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** この２番目の句は「もし[n]が何らかの[n']を用いて[S n']と表せるなら、[n']を返す」と読めます。 *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** 自然数というのは非常に一般的な型なので、Coqは自然数を扱ったり表したりするときに若干特別な扱いをします。[S]や[O]を使った式の代わりに一般的に使われるアラビア数字を使うことができます。実際、Coqは数値を表示する際、デフォルトではアラビア数字を用います。 *)

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

(** [nat]のコンストラクタ[S]は、[nat -> nat]型の関数で[minustwo]や[pred]も同様です。 *)

Check S.
Check pred.
Check minustwo.

(** これらが表しているのは、いずれの関数も数を引数にとって数を生成できる、ということです。しかしながらこれらの関数には根本的な違いがあります。[pred]や[minustwo]といった関数には「計算ルール」というものが定義されています。[pred]の定義は、[pred n]が[match n with | O => O | S m' => m' end]のように簡約されることを記述したものですが、一方[S]にはそのような定義がありません。しかし両方とも関数には違いなく、引数を元に評価されるということについては同じで、それ以上のものではないのです。 *)

(** 数値を扱う多くの関数は、単なるパターンマッチだけでは記述できず、再帰的な定義が必要になってきます。例えば、[n]が偶数かどうかを調べて返す関数[evenb]は、[n-2]が偶数であるかどうかを調べる、という再帰的な定義を必要とします。そういう関数を定義する場合、[Fixpoint]というキーワードを使用します。 *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Coqがこの定義をチェックする際、[evenb]が再帰的に呼ばれるとき、最初の引数が減少しているかに注目します。これは、ここでいう再帰が[n]について構造的再帰（もしくは原始的再帰）であること、つまり[n]について常により少ない値で再帰呼び出しを行っているか、ということです。これは[evenb]が最終的に停止するということを意味しています。Coqは[Fixpoint]キーワードで定義される関数が常にこの「減少性」を持つことを要求します。 *)

(** 同じように[Fixpoint]を使って関数[oddb]を定義することもできますが、ここでは次のようにもっとシンプルな用法で簡単に作ってみましょう。 *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity.  Qed.

(** 当然ながら、引数を複数持つ関数も再帰的に定義することができます。 *)

(** ネームスペースを汚さないようにするため、別のモジュールに定義することにしましょう。*)
Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** 3に2を加えた結果は、5になるべきですね。 *)

Eval simpl in (plus (S (S (S O))) (S (S O))).

(** Coqがこの計算をどう進めて（簡約して）結論を導くかは以下のように表現できます。 *)

(**     [plus (S (S (S O))) (S (S O))]    *)
(**    ==> [S (plus (S (S O)) (S (S O)))]    by the second clause of the [match]*)
(**    ==> [S (S (plus (S O) (S (S O))))]    by the second clause of the [match]*)
(**    ==> [S (S (S (plus O (S (S O)))))]    by the second clause of the [match]*)
(**    ==> [S (S (S (S (S O))))]             by the first clause of the [match]  *)

(** 表記を簡便にするため、複数の引数が同じ型を持つときは、型の記述をまとめることができます。 [(n m : nat)]は[(n : nat) (m : nat)]と書いたのとまったく同じ意味になります。 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

(** matchに引数を与える際、複数の引数を次のようにカンマで区切って一度に渡すことができます。 *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** [minus]の[match]の行に現れる( _ )は、ワイルドカードパターンと呼ばれるものです。パターンの中に _ を書くと、それはその部分が何であってもマッチし、その値が使用されないことを意味します。この _ は、このような場合に無意味な名前をつける必要をなくしてくれます。 *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1:             (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** **** 演習問題: ★ (factorial) *)
(** 再帰を使用した、一般的なfactorical（階乗）の定義を思い出してください :
<<
    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    これをCoqでの定義に書き直しなさい。 *)

Fixpoint factorial (n:nat) : nat :=
  (* FILL IN HERE *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
(** [] *)

(** ここで紹介する"notation"（表記法）という機能を使うことで、加算、減算、乗算のような数値を扱う式をずっと読みやすく、書きやすくすることができます。 *)

Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)  (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)  (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

(** これらは、これまで我々が定義してきたものを何ら変えるわけではありません。NotationはCoqのパーサに対して[x + y]を[plus x y]と解釈させたり、逆に[plus x y]を[x + y]と表記させたりするためのものです。

各表記法のシンボルは、表記法のスコープ内でのみ有効です。Coqはどのスコープであるかを推測しようとします。[S(O*O)]と書かれていた場合は、それを[nat_scope]であると推測しますし、ソースにデカルト積（タプル）型[bool*bool]と書かれていたら、[type_scope]であると推測します。時には[(x*y)%nat]といった風に、%表記を使ってスコープを明示する必要があるでしょうし、どの表記スコープで解釈したかが[%nat]というような形でCoqからフィードバックされてくることもあります。

表記のスコープは、多くの場合数値に適用されます。ですので[0%nat]という表記を[O]（オー）や[0%Z]（数値のゼロ）という意味で見ることがあります。 *)

(** 最初の方で、Coqにはほとんど何も用意されていない、という話をしましたが、本当のところ、数値を比較する関数すら自分で作らなければならないのです！! *)
(** [beq_nat]関数は自然数を比較してbool値を返すものです。入れ子になった[match]に気をつけて、以下のソースを読んでください。（二つの変数を一度に[match]させる場合の書き方は、[minus]のところですでに登場しています） *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** 同様に、[ble_nat]関数は自然数を比較して小さいか等しい、ということを調べてbool値を生成し返します。 *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** 練習問題: ★★ (blt_nat) *)
(** [blt_nat]関数は、自然数を比較して小さい、ということを調べてbool値を生成します（ [nat]ural numbers for [l]ess-[t]han）。[Fixpoint]を使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。

注：[simpl]タクティックを使ってうまくいかない場合は、代わりに[compute]を試してください。それはよりうまく作られた[simpl]と言えるものですが、そもそもシンプルでエレガントな解が書けていれば、[simpl]で十分に評価できるはずです。 *)

Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.
(** [] *)


(** * 簡約を用いた証明 *)

(** ここまでに、いくつかの型や関数を定義してきました。が、ここからは少し目先を変えて、こういった型や関数の特性や振る舞いをどうやって知り、証明していくかを考えてみることにしましょう。実際には、すでにこれまでやってきたことでも、その一部に触れています。。例えば、前のセクションの[Example]は、ある関数にある特定の値を入力した時の振る舞いについて、あらかじめ想定していたものと正確に一致していると主張してくれます。それらの主張が証明しているものは、以下のものと同じです。

[=]の両側の式を定義に基づいて簡約した結果は、一致している。

このような「簡約を用いた証明」は、関数のさらに興味深い性質をうまく証明することができます。例えば、[0]が自然数の加算における左単位元（[0]が、左から加えても値が変わらない値であること）であることの証明は、[n]が何であっても[0 + n]を注意深く縮小(簡約)したものが[n]になることを、[+]という関数が「最初の引数を引き継いで再帰的に定義されている」ということを考慮した上で示せればいいということです。 *)

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof.
  simpl. reflexivity.  Qed.

(** [reflexivity]コマンドは暗黙的に＝の両辺を簡約してから等しいかどうかを調べてくれます。そのため、上の証明はもう少し短くすることができます。*)
(** 実際、[reflexivity]は[simpl]よりいくぶん多くのことをやってくれるので、覚えておくと後々便利でしょう。例えば、[reflexivity] は定義された句を展開したり、右辺と置き換えるといったことを試みます。この違いから、[reflexivity] が向いているのは、「[reflexivity] によって全てのゴールが自動的に証明され、[reflexivity] が見つけて展開した式をあえて見なくてもよい」という場合で、逆に[simpl]は、我々自身が新しいゴールを読んで理解すべき時（勝手に定義を展開し解釈して欲しくない時）に向いているということになります。 *)

Theorem plus_O_n' : forall n:nat, 0 + n = n.
Proof.
  reflexivity.  Qed.

(** この定理と証明の様式は、以前示した例とほとんど同じですが、唯一の違いは、量化子が加えられている（[forall n:nat]）ことと、[Example]の代わりに[Theorem]キーワードが使用されていることです。後者の違いは単なるスタイルの違いで、[Example]と[Theorem]（他にも[Lemma]、[Fact]、[Remark]など）はCoqから見るとすべて同じ意味を持ちます。

[simpl]や[reflexivity]はタクティックの例です。タクティックは、[Proof]と[Qed]の間に記述され、Coqに対して、我々がしようとしている主張の正当性をどのようにチェックすべきかを指示するためのコマンドです。この講義の残りでは、まだ出てきていないタクティックのうちのいくつかを紹介していきましょう。さらにその後の講義ではもっと色々出てくるのですが。 *)

(** **** 練習問題: ★, optional (simpl_plus) *)
(** この問い合わせの結果、Coqが返す応答はなにか？ *)

Eval simpl in (forall n:nat, n + 0 = n).

(** また次のものの場合はどうか？ *)

Eval simpl in (forall n:nat, 0 + n = n).

(** この二つの違いを示せ。  [] *)


(** * [intros]タクティック *)

(** 単体テストの際には対象の関数に対して特定の引数を渡すわけですが、プログラムの証明を行う上で注意を払うべきポイントは、それが量化子（任意の[n]について、など）や仮定（[m=n]と仮定すると）で始まるか、ということです。そのような状況で求められるのは「仮定をたてて証明できる」ことです。例えば「よし、[n]を任意の数値としよう」「よし、仮に[m=n]と仮定してみよう」といった具合です。

[intros]タクティックは、このようなことを量化子や仮定をゴールから前提条件にき上げることで実現してくれます。

例えば、以下は同じ定理を少し異なるやり方で証明したものです。 *)

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.

(** 次の証明をCoq上で逐次実行し、どのように状況が変化してゴールが導かれるのかをよく観察してください。 *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** 定理の名前についている[_l]という接尾辞は、「左の」と読みます。 *)


(** * 書き換え（[Rewriting]）による証明*)

(** 少しばかり興味深い定理を見てみましょう。 *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** この定理は、あらゆる[n]や[m]について完全に成り立つと言っているわけではなく、[n = m]が成り立つときに限って成立する、というもので、この矢印は"ならば"と一般的に読みます。

[n]と[m]が両方とも任意の数なのですから、これをこれまでの証明でやってきたように簡約することはできません。その代わりに、[n = m]ならば、イコールの両側の[n]や[m]を互いに書き換えても等しさは変わらない、というところに注目します。このような書き換えをしてくれるのが[rewrite]タクティックです。 *)

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite -> H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

(** 証明の1行目は、∀（forall）がついた、つまり「あらゆる[n],[m]について」の部分をコンテキストに移しています。2行目は、[n = m]ならば、という仮定をコンテキストに写し、[H]という名前をこれに与えています。3行目は、ゴールになっている式([n + n = m + m])に仮定[H]の左側を右側にするような書き換えを施しています。

（[rewrite]の矢印は特に論理に関与していません。単に左側を右側に置き換えているだけです。逆に右側を左側に置き換えたい場合は、[rewrite <-]と書くこともできます。この逆の置き換えも上の証明で試して、Coqの振る舞いがどのように変わるかを観察してください。） *)

(** **** 練習問題: ★ (plus_id_exercise) *)
(** [Admitted.]を削除し、証明を完成させなさい。*)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Admittedコマンドは、Coqに対して「この証明はあきらめたので、この定理はこれでいいことにしてください」と指示するものです。この機能は、より長い証明をする際に便利です。何か大きな論証をしようとする時、今のところ信用している補足的な命題を示したい時があります。そんな時、[Admitted]を使用すると、その命題を一時的に信用できることにして、それを踏み台にしてより大きな論証を進めることができるのです。そしてそれが完成したのち、あらためて保留していた命題の証明を埋めればいいのです。ただし注意して下さい。[admit]や[Admitted]を使用することは、一時的にドアを開けて、「全て形式的なチェックを受け証明済みの、信用するに足るCoqの世界」から、信用に値しない下界へ足を踏み出していることに他なりません。いつかは戻ってドアを閉めることがお約束です。*)

(** 仮定の代わりに、前もって証明された定理を使っても[rewrite]タクティックは同じように利用することができます。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** 練習問題: ★★, recommended (mult_1_plus) *)
Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** * Case分析 *)

(** もちろん、どんな命題でも簡単な計算だけで証明できるという訳ではありません。一般に、未知だったり仮定の（任意のbool、自然数、リストなど）値は、我々が検証しようとしている関数の先頭に記述され、それが簡約の邪魔をしてくれます。例えば、下のような命題をsimplタクティックだけで証明しようとすると、すぐに行き詰まってしまうでしょう。 *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. simpl.  (* does nothing! *)
Admitted.

(** その原因は、beq_natと+の定義で、共に最初の引数が[match]に渡されていることです。つまり、[+]に渡す最初の引数は[n]という未知数な上に、[beq_nat]の引数は[n + 1]という複合式になっているため、そのまま簡約できないのです。

今求められていることは、[n]を何らかの条件に分割し、先に進めそうな形にすることができないかを検討することです。もし[n]が[O]なら、[beq_nat (n + 1) 0]の結果を得ることはできます。もちろん結果は[false]です。しかしもし[n]が何かの[n']を使って[n = S n']と表せると考えても、我々は[n + 1]の値を得ることはできません。ただ、その式が一つの[S]で始まる（始まらないものは[O]にマッチする）ことに着目すると、[beq_nat]の結果を計算して値を求めることができます。その結果結果[beq_nat (n + 1) 0]は、やはり[false]になるでしょう。

このことから、求められるタクティックはCoqに[n = O]の場合と[n = S n']の場合に分けて考えるように求めるようなもので、これを実現するのが[destruct]タクティックです。 *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

(** [destruct]タクティックは二つのサブゴールを作ります。その両方を別々に、Coqを使って定理として証明していくことになります。一つのサブゴールからもう一つへ移動するための特別なコマンドは必要ありません。一つ目のサブゴールが証明されれば、それは消えて自動的にもう一つのサブゴールにフォーカスが移ります。この証明では、二つに分かれたサブゴールのいずれも[reflexivity]を1回使うだけで簡単に証明できます。

destructについている注釈"[as [| n']]"は、"イントロパターン"と呼ばれるものです。これはCoqに対して、両方のサブゴールに元[n]だった変数をどのような変数名を使って取り入れるかを指示するものです。一般的に[[]]の間にあるものは"名前のリスト"で、"[|]"によって区切られます。このリストの最初の要素は空ですが、これは[nat]の最初のコンストラクタである[O]が引数をとらないからです。二つ目のコンストラクタ[S]は引数を一つ取りますので、リストの二つ目の要素である[n']を名前に使用します。

[destruct]タクティックは帰納的に定義された型に対して使用できます。例えば、bool値の否定が反射的であること・・・つまり否定の否定が元と同じになることを証明してみましょう。 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** ここで使われている[destruct]には[as]句がありませんが、ここで展開している[b]の型[bool]の二つのコンストラクタが両方とも引数をとらないため、名前を指定する必要がないのです。このような場合、"[as [|]]"や"[as []]"のように書くこともできます。実際のところほとんどの場合[destruct]の[as]句は省略可能です。その際はCoqの側で自動的に変数名をつけてくれます。これは確かに便利なのですが、よくない書き方とも言えます。Coqはしばしば名前付けに混乱して望ましくない結果を出す場合があります。 *)

(** **** 練習問題: ★ (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** * Caseへのネーミング *)

(** caseのサブゴールからサブゴールへ明示的に移動するためのコマンドがないことは、証明の過程と結果を表すスクリプトを読みにくくしていることも事実です。さらに大掛かりな証明では、caseの分析も階層化し、Coqを使って証明を進めていくことが苦痛に感じられるかもしれません（あるCaseが五つのサブゴールを持ち、残りの七つのCaseも他のCaseの内部にあるような状況を想像してみてください･･･）。インデントやコメントを上手に使うと多少は改善しますが、最もよい解決方法は"[Case]"タクティックを定義して使用することです。

[Case]タクティックはCoqにビルトインされていませんので、自分で定義する必要があります。それがどのような仕組みで動いているかを理解する必要はありませんので、ここでは定義は跳ばして使用例から見ていくことにします。このサンプルは、Coqの機能のうちまだ解説していないstringライブラリとLtacコマンドを使用します。これらはカスタムタクティックを定義するときに使うもので、Aaron Bohannon の業績によるものです。 *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(** 以下は[Case]をどのように使うかのサンプルです。証明を順次実行して、コンテキストがどのように変わっていくかを観察しなさい。 *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

(** [Case]が行っていることは実はとても簡単です。Caseは、続けて指定されたタグ名を、今証明しようとしているゴールへのコンテキストに文字列として追加しているだけなのです。証明がサブゴールに到達し、証明されると、次のトップレベル（今しがた解決したゴールと兄弟関係にある）ゴールがアクティブになります。するとさっきCaseで指定した文字列がすでに証明を終えたcaseとしてコンテキストに現れます。これは健全性のチェックにもなります。もし今の証明が完了しておらず、コンテキストに残ったまま次の[Case]タックティクを実行すると、エラーメッセージが表示されます。

ネストしたcaseの分析（今[destruct]で解決しようとしているゴール自体が、他の[destruct]の産物であるような場合）のために、[SCase]("subcase")が用意されています。 *)

(** **** 練習問題: ★★ (andb_true_elim2) *)
(** [destruct]を使い、case（もしくはsubcase）を作成して、以下の証明[andb_true_elim2]を完成させなさい。 *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Coq上に証明の経過を記述する際、それをどのようにフォーマットするべきか、ということについてちゃんとしたルールというものはありません。行が分割され、証明の各段階が階層を持ち、それをインデントで表現するような場合は特にそうです。しかしながら、複数のサブゴールが作成された部分が明示的に[Case]タクティックでマークされた場合は、それを行頭から記述することにします。そうしておけば、証明は読みやすくなり、それ以外でどんな方針のレイアウトが選ばれても、あまり問題になりません。

ここで、１行の長さをどれくらいにしておくべきか、ということにも触れておきましょう。始めたばかりのCoqユーザーは、証明全体を１行に収めようと、複数のタクティックを同じ行に書き、非常に長い行を書いてしまいがちです。よいスタイルというものは「ほどほど」のところにあります。特にあげるなら、一連の流れを１行に書くにしても1行80字程度にとどめておくべきでしょう。これ以上長くなると読むのも大変になりますし、印刷や画面表示もうまくいかない場合が多くなります。多くのエディタがこのような制限をかける機能を持っていますのでそれを使ってもいいでしょう。 *)



(** * 帰納法 *)

(** 我々は以前、[0]が加法[+]の左単位元（左から加えても値が値が変わらない値）であることを引数を分解し評価することで証明しました。右から加える場合でも同じように証明できるのでしょうか？ *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ･･･同じぐらい簡単、というわけにはいかないようです。[reflexivity]を使ってみても同じです。[n + 0]の[n] は任意の未知数であり、[+]の定義にある[match]のせいで簡約できません。[destruct n]を使い、caseごとに推論するのも難しそうです。caseごとに考えると[n = 0]のときはうまくいきますが、[n = S n']のほうでは[n']で同じように詰まってしまいます。[destruct n']でさらに一歩踏み込んでみたところで、[n]は任意の大きい数のまま動きません。どうやらまだ来たことがないところに迷い込んでしまったようです。 *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Admitted.

(** Caseによる解析は少しだけうまくいきそうに思えますが、やはり行き詰まります。 *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Admitted.

(** このような命題を証明する場合 － 実際、数値やリストや、その他の帰納的な定義を持つ型にまつわる証明の多くはそうなのですが － もっとずっと強力な推論規則が必要になります。それが「帰納法」です。

高校で習った帰納法の仕組みを思い出して、自然数を考えてみましょう。もし[P(n)]が自然数[n]に対する命題であるとすると、Pがどんな[n]に対しても成り立つことは、以下のような方法で証明できます。

         - [P(O)]が成り立つことを示す;
         - どんな[n']に対しても、もし[P(n')]が成り立つなら[P(S n')]も成り立つことを示す;
         - これによって、[P(n)]がどんな[n]でも成り立つと結論される

Coqでは、それぞれのステップは同じですが順序は逆向きに考えます。まず、ゴールの証明である「任意の[n]について[P(n)]が成り立つ」からはじめ、それを二つの独立したサブゴールに分割します（ここで[induction]タクティックを使います）。その結果、一つ目のサブゴールは[P(O)]、二つ目は[P(n') -> P(S n')]となるはずです。以下は、実際に[induction]タクティックが先ほど証明しようとしていた定理にどう作用するかを示したものです。 *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** [destruct]のように、[induction]タクティックも[as...]句を取り、サブゴールに導入する際の変数の名前を指定することができます。最初のブランチでは[n]は[0]に置き換えられ、ゴールは[0 + 0 = 0]となり、簡約できる状態になります。二つ目のブランチでは、[n]は[S n']に置き換えられ、[n' + 0 = n']が前提としてコンテキストに付け加えられます。（この際、仮定に[IHn']という名前がつけられます。これは「Induction Hypothesys for [n']（n'についての帰納法の仮定）」というような意味です。二番目のゴールは[(S n') + 0 = S n']となり、[S (n' + 0) = S n']に簡約されます。ここから、帰納法の仮定[n' + 0 = n']を使って証明の残りを完成させます。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** 練習問題: ★★, recommended (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** **** 練習問題: ★★ (double_plus) *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (destruct_induction) *)
(** [destruct]と[induction]の違いを短く説明しなさい。

(* FILL IN HERE *)

*)
(** [] *)


(** * 形式的証明と非形式的証明 *)

(** "非形式的な証明はアルゴリズムであり、形式的な証明はコードである" *)

(** 数学的に厳格な証明を構成するとはどういうことなのか、という問題は、千年もの間哲学者を悩ませてきました。しかし少々雑な定義でよければ次のように書くこともができます。数学的な命題[P]の証明とは、それを読む（あるいは聞く）人をして、[P]がtrueであることを納得せしめる文章を書く（語る）ことである、と。このことから、証明はコミュニケーション行為であると言えるでしょう。

さて、このコミュニケーションの相手は、二種類に分けることができます。一方は、Coqのプログラムのように振る舞うような場合で、このケースでの「信用に値する」というのは、[P]が形式的論理のルールに基づく確実な論理から導かれたもので、その証明が、このチェックを行うプログラムをガイドする秘訣になっているようなものです。そんな秘訣が「形式的証明」です。

一方、読者が人間的な存在で、証明が英語などの自然言語で書かれているようなケースは「非形式的証明」であると言えます。こんなケースでの成功の条件は「あまりきちんと明示しないこと」です。とにかく、読んでいる人に納得させてしまえる証明こそが「よい証明」なのです。しかしひとつの証明を複数の読者が見るような場合、ある論点について、ある人は特定の言い回しによって核心に至るかもしれませんが、人によってはそうではないかもしれません。もっと極端な人は、ただ知ったかぶりをする割りに経験は浅い、単なる「頭でっかち」であるかもしれません。そういった人たちを押しなべて納得させる唯一の方法は、ただ骨身を惜しまず細かいところまで論じることなのです。逆にある読者はこういったことに精通しているあまり、細かいことにこだわりすぎて全体的な流れを見失う、ということもあります。多くの人が望んでいることは総論としてどうなのか、ということを知ることで、細かいことを考えていくことは面倒なものです。結局のところ、非形式的な証明でみんなを納得させる標準的な方法はなさそうです。なぜなら、非形式的な書き方で想定される読者全員を納得させる方法はないからです。しかし実際のところ、数学者は複雑な数学的事柄についてたくさんの表記規則のおかげで、証明が正しいか否かを判断するための標準的かつ公正な方法がもたらされたのです。

我々はこのコースでCoqを使用しているのですから、それだけできちんと形式化された証明に乗っていると言えます。しかしこのことは、非形式的な表現を無視していい、ということではありません。形式的証明は多くの場合有効ですが、人と人との間で考えを伝えあう際には必ずしも効率的とは言えないものです。 *)

(** 例えば、下の例は加法が結合的であることを示すものです。 *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coqはこのような証明を完璧にこなしてくれますが、上の証明は人間にとってはいささかのみこみにくいと言わざるを得ません。もしあなたがCoqに十分慣れていて、タクティックを次々と適用しながら証明を進めていき、コンテキストやゴールがどう変化していくかを頭の中だけでイメージしていくことができるようなレベルの人でも、上の証明はかなり複雑で、ほとんど理解不能に思えるかもしれません。それを横目に、数学者はサラサラとこんな風に書くでしょう。 *)
(** - 定理：任意の[n],[m],[p]について、以下が成り立つ
[[
      n + (m + p) = (n + m) + p.
]]
    証明：[n]について帰納法を適用する。

    - まず[n = 0]と置くと、以下のようになる
[[
        0 + (m + p) = (0 + m) + p.
]]
      これは、[+]の定義から直接導くことができる。

    - 次に[n = S n']と置き、帰納法の仮定を
[[
        n' + (m + p) = (n' + m) + p.
]]
      とすると、以下のような式が立つ。
[[
        (S n') + (m + p) = ((S n') + m) + p.
]]
      ここで、[+]の定義より、以下のように変形できる。
[[
        S (n' + (m + p)) = S ((n' + m) + p),
]]
      これは、直後の値について帰納法の仮定が成り立つことを示している。 [] *)

(** どちらの表現も、やっていることは基本的に同じことです。これはもちろん偶然ではなく、Coqの[induction]タクティックが、数学者が考えるのと同じ目標を、同じサブゴールとして、同じ順番で作成するように作られているだけです。しかしこの二つをよく見ると、重要な違いがあります。形式的証明は、ある部分（[reflexivity]を使っている部分など）ではより明示的ですが、それ以外のところはあまり明示的ではありません。特にあるポイントにおける証明の状態が、Coqの証明では明示されていません。一方、非形式的証明は、途中で何度も「今どのあたりで、どのようになっているか」を思い出させてくれるような書き方になっています。 *)

(** 形式的証明も、以下のように書けば構造が分かりすくなります。 *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** 練習問題: ★★ (plus_comm_informal) *)
(** [plus_comm]の証明を、非形式的な証明に書き換えなさい。 *)

(** 定理：加法は可換である。

    Proof: (* FILL IN HERE *)
[]
*)

(** **** 練習問題: ★★, optional (beq_nat_refl_informal) *)
(** 次の証明を、[plus_assoc] の非形式的な証明を参考に書き換えなさい。Coqのタクティックを単に言い換えただけにならないように！

   定理：true=beq_nat n n forany n.（任意のnについて、nはnと等しいという命題がtrueとなる）

    Proof: (* FILL IN HERE *)
[]
 *)

(** **** 練習問題: ★, optional (beq_nat_refl) *)
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(** * 証明の中で行う証明 *)

(** Coqでは（非形式的な数学と同様に）大きな証明は高い頻度で、後に出てきた証明が前に出ている証明を参照するような定理の列に分割されます。しかし時折、証明がいくつかの自明で雑他な事実を必要とし、それがまたトップレベルの名前をつけるほどでもなかったりします。こういう場合、状態を単純化し、すでに使われている定理の右に出現するサブ定理を証明することができれば便利です。[assert]タクティックはこれを可能にしてくれます。例えば、最初の方でやった証明[mult_0_plus]は、[plus_O_n]と名付けられた定理の証明から参照されています。[assert]を使うと[plus_O_n]の証明をこんな風に行うことができます。 *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

(** [assert]タクティックは、二つのサブゴールを取り込みます。最初のものは[H:]という接頭辞をつけているように、それ自身を主張するもので、Assertion [H]と呼びます。
（まず注意が必要なのは、上で使用した[destruct]や[induction]に[as]句をつけることで、[assert (0 + n = n) as H]というようにassertionに名前をつけられることです。
もう一つ、証明に出てくるassertionに、[Case]を使ってマーキングしている事も注目です。その理由は、読みやすさのため、というだけでなく、例えばCoqをインタラクティブに使っているとき、証明を進めている間にコンテキストから["Proof of assertion"]という文字列が消える瞬間を観察することで、証明の完了を知ることができます。）二つ目のゴールは、[assert]を呼び出した場合と、コンテキストに[0 + n = n] : [H]という仮定が得られることを除けば同じです。このことから、[assert]は、我々が証明しなければならない事実そのものとなるサブゴールと、その最初のサブゴールの証明がどのような値でも成り立つことを使って証明される事実となる二つ目のサブゴールを作成することが分かります。 *)

(** 実際[assert]は多くのシチュエーションで便利に使えるでしょう。例えば、[(n + m)
    + (p + q) = (m + n) + (p + q)]であることを証明するとしましょう。[=]の両側で異なるのは最初のカッコの中の[+]の両側の[n]と[m]が入れ替わっているだけで、このことは加法の交換法則([plus_comm]）があるものを別のものに書き換えることに使用できることを示しています。しかしながら、[rewrite]タクティックは「どこに適用するか」を考える必要がある場合には少々おばかさんです。ここでは[+]が3箇所で使われていますが[rewrite -> plus_comm]は一番外側（つまり中央）の[+]にしか適用されません。 *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* ここで[(n + m)]を[(m + n)]に入れ替えたいのですが、[plus_comm]でこれができるかと試してみると... *)
  rewrite -> plus_comm.
  (* うまくいきません。Coqは別のところを[rewrite]してしまいます *)
Admitted.

(** [plus_comm]を、適用したいポイントに対して使用するには、まず[n + m = m + n]で始まるような補助定理（ここでは何とかしようとしている[m]と[n]を特定するため）を導き、それを望むrewriteに使用します。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** 練習問題: ★★★★ (mult_comm) *)
(** [assert]を使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.


(** では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明した[plus_swap]が便利に使えるでしょう。 *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (evenb_n__oddb_Sn) *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** * さらなる練習問題 *)

(** **** 練習問題: ★★★, optional (more_exercises) *)
(** 紙を何枚か用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)[destruct]を使ったcase分割が必要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべからず」といった理由です。 *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (plus_swap') *)
(** [replace]タクティックは、特定のサブタームを置き換えたいものと置き換えることができます。もう少し正確に言うと、[replace (t) with (u)]は、ゴールにある[t]という式を全て[u]にかきかえ、[t = u]というサブゴールを追加します。この機能は、通常の[rewrite]がゴールの思い通りの場所に作用してくれない場合に有効です。

[replace]タクティックを使用して[plus_swap']の証明をしなさい。ただし[plus_swap]のように[assert (n + m = m + n)]を使用しないで証明を完成させなさい。
*)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** 練習問題: ★★★★, recommended (binary) *)
(** これまでとは異なる、通常表記の自然数ではなく2進のシステムで、自然数のより効率的な表現を考えなさい。それは自然数をゼロとゼロに1を加える加算器からなるものを定義する代わりに、以下のような2進の形で表すものです。2進数とは、
      - ゼロであるか,
      - 2進数を2倍したものか,
      - 2進数を2倍したものに1を加えたもの.

    (a) まず、以下のnatの定義に対応するような2進型[bin]の帰納的な定義を完成させなさい。
    (ヒント: [nat]型の定義を思い出してください。
[[
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
]]
    nat型の定義[O]や[S]の意味が何かを語るものではなく、（[O]が実際に何であろうが）[O]がnatであって、[n]がnatなら[S]が何であろうと[S n]はnatである、ということを示しているだけです。「[O]がゼロで、[S]は1を加える」という実装がそれを自然数としてみて実際に関数を書き、実行したり証明したりしてみてはじめて実際に意識されます。ここで定義するbinも同様で、次に書く関数が書かれてはじめて型binに実際の数学的な意味が与えられます。)

    (b) 先に定義したbin型の値をインクリメントする関数を作成しなさい。また、bin型をnat型に変換する関数も作成しなさい。

    (c) 最後にbで作成したインクリメント関数と、2進→自然数関数が可換であることを証明しなさい。これを証明するには、bin値をまずインクリメントしたものを自然数に変換したものが、先に自然数変換した後にインクリメントしたものの値と等しいことを証明すればよい。
*)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★★★ (binary_inverse) *)
(** この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用いてもよい。


    (a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。


    (b) あなたはきっと、逆方向についての証明をしたほうがいいのでは、と考えているでしょう。それは、任意の2進数から始まり、それを自然数にコンバートしてから、また2進数にコンバートし直したものが、元の自然数と一致する、という証明です。しかしながら、この結果はtrueにはなりません。！！その原因を説明しなさい。


    (c) 2進数を引数として取り、それを一度自然数に変換した後、また2進数に変換したものを返すnormalize関数を作成し、証明しなさい。
*)

(* FILL IN HERE *)


(** **** 練習問題: ★★, optional (decreasing) *)
(** 各関数の引数のいくつかが"減少的"でなければならない、という要求仕様は、Coqのデザインにおいて基礎となっているものです。特に、そのことによって、Coq上で作成された関数が、どんな入力を与えられても必ずいつか終了する、ということが保障されています。しかし、Coqの"減少的な解析"が「とても洗練されているとまではいえない」ため、時には不自然な書き方で関数を定義しなければならない、ということもあります。

これを具体的に感じるため、[Fixpoint]で定義された、より「微妙な」関数の書き方を考えてみましょう（自然数に関する簡単な関数でかまいません）。それが全ての入力で停止することと、Coqがそれを、この制限のため受け入れてくれないことを確認しなさい。 *)

(* FILL IN HERE *)
(** [] *)

