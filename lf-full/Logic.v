(** * Logic: Coq中的逻辑系统 *)

Require Export Tactics.

(**
    在之前的章节中我们已经看到了很多有关事实性的声明（命题）和表达证实这些
    声明的正确性的证据（即证明）的方法的许多例子。比如说，至今为止我们已经
    做了许多[e1 = e2]这样的 _'相等性命题'_ ，形如[P -> Q]这样的主体为蕴含式
    的命题，以及形如[forall x, P x]的量化命题的证明。
    在接触更多相关的细节之前，让我们先探讨一下在Coq中数学表达式的地位。回忆
    一下，Coq是一门 _'有类型的'_ 语言；在Coq的世界中，一切有意义的表达式都有其
    类型。这类逻辑性的断言也是如此。所有我们试着去证明的命题在Coq中都有着[Prop]
    这一 _'专门为命题设立的'_ 类型。我们可以用Check去查看这类命题的类型：  *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** 注意： _'所有语法上合法的命题的类型都为[Prop]'_ 。它们的类型与它们
    是否为真命题无关： _'本身成为'_ 一个命题与 _'能得到这个命题的证明'_ 
    是不同的两回事。 *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(**
    除了类型之外，命题也是所谓的 _'一等对象'_ ，即在Coq的世界中，我们可以像对
    其他值进行操作一样对命题进行操作。到现在为止，我们已经知道命题可以在
    [Theorem]（还有[Lemma]和[Example]）的定义中出现： *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(**
    但是它们同时也可以用于其他地方。比如说，就像我们用[Definition]给某些
    函数或者其他类型的值取一个名字一样，我们可以用同样的方法为某些命题取
    一个名字： *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(**
    在这之后我们可以在任何需要填入一个命题的地方使用这个名字，例如在一个
    Theorem声明中： *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** 我们也可以写出所谓 _'参数化'_ 的命题；它们实际上是一类函数：它们取某些
    类型的值作为参数，并最终得到一个命题。 *)

(**
    例如下面的这个函数；它取一个数字，并返回一个断言了这个数字等于3的命题。 *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** 在Coq中，我们说那些返回一个命题的函数 _'定义了它们所取的参数的性质'_ 。
    以下面这个多态函数为例子；它描述了 _'单射函数'_ 这个十分常见的概念。 *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** 相等性操作符 [=] 也是一个返回命题的函数：[n = m]是使用了Coq
    的[Notation]机制定义的[eq n m]的语法糖。因为[eq]可以用在任意类型的
    值上，所以它也是多态的：*)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(**
    （注意在上面我们写的是[@eq]而不是[eq]；[eq]的类型参数[A]被定义成了
    隐式参数，所以为了看到[eq]的完整的类型，我们需要通过[@]暂时取消对隐
    式参数的处理。 *)

(* ################################################################# *)
(** * 逻辑连接符 *)

(* ================================================================= *)
(** ** 合取（逻辑"与"） *)

(** 命题[A]与[B]的 _'合取'_ 或 _'逻辑与'_ 写作[A /\ B]，表示一个宣称[A]和[B]都
    为真的命题。 *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** 证明合取命题一般用[split]这一证明策略；它会分别为组成合取的两个部分生成
    子目标。 *)

Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** 对于任意的命题[A]和[B]，如果我们假设[A]为真而且我们也假设[B]为真，那么我
    们能够得出[A /\ B]也为真的结论。*)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** 因为定理的应用会产生与假设的个数相等的子目标，我们能够通过应用[and_intro]
    来得到与使用[split]一样的结果。*)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 以上就是与证明合取有关的内容。在进行相反方向的操作，即在证明过程中需要 _'使用'_ 
    某个合取假设的时候，一般使用[destruct]。
    如果当前证明上下文中存在形如[A /\ B]的假设[H]，[destruct H as [HA HB]]将会从上
    下文中去掉[H]并增加[HA]和[HB]这两个新的假设，其中前者宣称[A]为真，而后者宣称[B]
    为真。 *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 我们也能够在将[H]引入当前上下文的同时对其进行解构： *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 也许你会想，我们完全可以将[n = 0]和[m = 0]写成分开的两个假设，为什么
    我们仍然要不厌其烦地将这两个假设包在一个单独的合取之中呢？*)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** 单纯地就这个定理而言两种都可以，但是我们需要理解如何对合取假设进行操作，
    因为这样的假设经常在证明的中途出现，特别是在进行较为大型的开发的时候。
    这里就有这样的一个比较简单的例子： *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** 另外一个经常碰见的场合，就是我们已经知道了[A /\ B]，但是我们只需要[A]或
    者[B]的时候。以下的引理对于应付这样的状况而言会很有用： *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 最后，我们有时也需要改变由多个命题组成的合取中某些部分所在的位置。以下的
    引理对于应付这样的状况而言会很有用： *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.
  
(** **** Exercise: 2 stars (and_assoc)  *)
(** （留意一下[intros]后面所使用的 _'嵌套'_ 的模式是如何将假设[H : P /\ (Q /\ R)]
    分解为[HP : P]，[HQ : Q]和[HR : R]这三个互相独立的假设的。从那个地方开始完
    成这个证明。） *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 顺带一提，[/\]这一中缀记号只是[and A B]的语法糖而已；[and]才是Coq里将两个命题
    合并得到合取命题的操作符。 *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** 析取 *)

(** 另外一个重要的连接符是所谓的 _'析取'_ ，或者 _'逻辑与'_ 连接符。对于任意两个命题[A]
    和[B]，其析取[A \/ B]在[A]与[B]之中的任意一个命题为真时为真。（或者，我们可以写
    [or A B]，其中[or : Prop -> Prop -> Prop]。）
    使用某个析取假设的时候，我们使用分类讨论；就像对[nat]以及其他的数据类型进行分类
    讨论一样，对析取假设进行分类讨论时我们也可以使用像[destruct]或者[intros]这样的
    证明策略。以下是一个对析取假设进行分类讨论的例子： *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* 这个模式会自动对[n = 0 \/ m = 0]作出分类讨论。 *)
  intros n m [Hn | Hm].
  - (* 在这里存在[n = 0] *)
    rewrite Hn. reflexivity.
  - (* 在这里存在[m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** 相对应地，要证明某个析取命题为真，我们需要证明它任意一边的命题为真。我们用[left]
    和[right]这两种证明策略来作出这种选择。就像它们的名字所说的那样，[left]将会选择
    待证的析取命题的左边，而[right]将会选择右边。
    下面是一个很简单的例子：*)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** 这个更为有趣的例子则需要在同一个证明中使用[left]和[right]： *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 假命题与否定 *)

(** 到现在为止我们主要都在证明某些东西 _'是真的'_ ，比如说加法真的符合交换律，
    列表之间的连接真的符合结合律等等；我们当然也有可能对一些 _'否定'_ 的，证明
    了某些命题 _'并非为真'_ 的事物产生兴趣。在Coq中，我们使用否定操作符[~]否定
    某个命题。
    为了理解否定背后的原理，回想一下在[Tactics]一章中有关 _'爆炸原理'_ 的
    相关讨论；爆炸原理断言，当我们假设了矛盾的存在时，我们可以证明任意命题。
    遵循着这一直觉，我们可以将[~ P]（即“非[P]”）定义为[forall Q, P -> Q]；
    但Coq选择了另外一种稍微有些不同的做法：它将[~ P]定义为[P -> False]，而
    [False]是在标准库中 _'被特别地定义了的'_ 矛盾性的命题。 *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** 因为[False]是矛盾性的命题，我们也可以对其应用爆炸原理：如果我们在证明上下文
    中得到了一个[False]，我们可以[destruct]它，并证明任何当前待证明的目标。 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(**
    _Ex falso quodlibet_ 是拉丁文，意思是“从谬误出发你能够证明任何你想要的”；
    这是爆炸原理的另一个为人熟知的名字。 *)

(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** 证明对于任意命题[P]，从Coq对于[~ P]的定义能够推出上面提到的对于否定的定义。 *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 以下是我们用[not]宣称并证明“[0]和[1]是不同的[nat]”这一命题的做法： *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** 这样的有关不相等的命题出现得十分频繁，足以让我们为其定义一个独立的表示法：
    [x <> y]。 *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** 在能够熟练地在Coq中对否定命题进行操作之前确实需要一点练习：即使有时你已经很
    清楚为什么某个否定命题为真，刚开始试图通过适当的设置让Coq接受这一点可能也会
    稍微有些困难。以下是一些作为热身的有关一些常见的事实的证明：*)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced, recommendedM (double_neg_inf)  *)
(** 写出[double_neg]，即下述命题的一个非形式化的证明：
    命题：对任意命题[P]而言，[P]蕴含[~~P]。 *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, advancedM (informal_not_PNP)  *)
(** 写出[forall P : Prop, ~ (P /\ ~P)]这一命题的非形式化的证明。你可以使用
    任何你想用的自然语言。 *)

(* FILL IN HERE *)
(** [] *)

(** 类似地，因为不等式包含了一个否定，在能够熟练地使用它之前也需要一定的练习。
    这里是一个比较有用的小技巧：如果你需要证明某个不可能的目标（例如当前的子目
    标是[false = true]）时，用[ex_falso_quodlibet]将这个目标转换成[False]；
    如果当前的证明上下文中存在形如[~P]的假设（例如形如[x<>y]的假设），那么这会
    让这些假设的使用变得更容易些。*)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** 因为我们经常会用到[ex_falso_quodlibet]，所以Coq提供了一个内置的证明策略：
    [exfalso]；这个策略在被使用时相当于应用了[ex_falso_quodlibet]。*)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

(* ================================================================= *)
(** ** 真值 *)

(** 除了[False]以外，Coq的标准库中也定义了[True]这一十分容易就能证明的命题。
    我们用[I : True]这一事先定义了的常数来证明[True]： *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** 与经常被使用的[False]不同，因为证明过于简单（所以也就没什么足以引起兴趣的
    东西）而且并不携带任何有用的信息，[True]很少被使用。
    然而在使用条件从句构建更加复杂的[Prop]或者作为高阶[Prop]的一个参数的时候它
    也可以变得十分有用。以后我们将会看到[True]的这类用法。
*)

(* ================================================================= *)
(** ** 逻辑上的相等性 Logical Equivalence *)

(** “当且仅当”这一逻辑连接符用起来十分顺手；它是两个蕴含式的合取，声明两个命题
    在任何情况下都有着相同的真值。 *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** 以上面的[<->]的对称性（[iff_sym]）的证明作为参照，证明[<->]同时也
    有自反性和传递性。 *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Coq的某些证明策略会以特别的方式处理[iff]，并以此避免了某些底层的对证明
    状态的操作。比如说，[rewrite]和[reflexivity]除了可以对等式使用以外同样
    也可以对[iff]使用。你需要加载一个特别的Coq库来让Coq允许你使用等式以外的
    式子进行重写。 *)

Require Import Coq.Setoids.Setoid.

(** 以下是一个简单的例子；它展示了这些证明策略会如何使用[iff]。
    首先，先让我们证明一些比较基本的[iff]等价命题…… *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** 现在我们能够在某些与等价性相关的命题的证明中使用[rewrite]和[reflexivity]
    的时候使用这些事实。这里是上述的[mult_0]的、包含了三个变量的版本： *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** [apply]也可以与[<->]一同使用。当[apply]的参数是一个等价性命题的证明，它将
    试图猜出使用该命题所包含的哪一个方向的蕴含式。 *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** 存在量化 *)

(**
    _'存在量化'_ 也是十分重要的逻辑连接符。我们用[exists x : T, P]表示存在一些
    类型为[T]的[x]使得一些性质[P]对于[x]成立。如果Coq能够从上下文中推断出[x]的
    类型应该为[T]，那么就像[forall]中我们可以省略[x]的类型标注一样，在[exists]中
    我们也可以省略[: T]这一类型标注。 *)

(** 证明形如[exists x, P]的命题时我们需要证明[P]对于一些特定的[x]是成立的；这些
    [x]被称作证实了这一命题的 _'实例'_ 。证明分为两个步骤：首先用[exists t]指出
    我们已经知道的可以使[P]成立的实例[t]，然后我们证明所有[x]都被替换成[t]的命题
    [P]。 *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** 相反地，如果我们在上下文中有形如[exists x, P]的存在假设，我们可以将其解构得到
    某个实例[x]以及证实[P]对[x]成立的证据。 *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star (dist_not_exists)  *)
(** 证明这一命题：如果[P]对所有[x]成立，那么没有使得[P]不成立的[x]。 *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** 证明存在量化对析取符合分配律。 *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 在编程中使用命题  *)

(**
    我们所了解的逻辑连接符大幅提升了我们以简单的命题为基础构建更为复杂的命题的能力。
    作为例子，让我们来思考如何表示“某个元素[x]出现在某个列表[l]之中”这一命题。注意到
    这一性质有着很简单的递归结构：*)

(** - 如果[l]是空列表，那么[x]不可能在[l]中出现；所以“[x]在[l]中出现”应该为假命题。
    - 如果[l]为形如[x' :: l']的列表，那么“[x]在[l]中出现”的正确性取决于[x]是否与[x']
      相等或者[x]是否在[l']出现。
 
    我们能够将这一定义直接翻译成一个递归函数；这个函数将取一个元素和一个列表作为参数
    并返回一个命题：*)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** 当[In]被应用于某个具体的列表时，它将被展开为一串由具体的命题组成的
    析取式。*)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** （注意，在上面的例子中我们使用了空模式来 _'无视'_ 最后一种情况。） *)

(** 我们也可以证明关于[In]的一些更为一般的，或者更为高阶的引理。
    注意在下面[In]被应用到一个变量上；只有我们对其进行分类讨论的时候，它才会
    被展开。 *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil，矛盾 *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** 虽然递归地定义命题在某些情况下会十分方便，但是这种方法也有其劣势。比如说，
    作为一种递归函数，这类命题也会受Coq对递归函数的要求的限制：在Coq中递归函数
    必须是“明显可停机”的。在下一章我们将会了解如何 _'归纳地'_ 定义一个命题；这是
    一种与之不同的技巧，有着其独特的优势和劣势。*)

(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (All)  *)
(** 回忆一下，返回命题的函数能够被视为对其参数的某种 _'性质'_ 的定义。比如说，
    假设[P]的类型为[nat -> Prop]，那么[P n]就是声明[n]拥有性质[P]的命题。
    以[In]作为参考，完成[All]这一递归函数的定义；它以某个列表[l]以及针对其元素
    的性质[P]为参数，返回一个声明“[l]中全部元素都具有性质[P]”的命题。证明[All_In]
    这一引理以对你的定义进行测试。当然了，为了通过测试而直接将[All_In]的左半部分
    写入[All]的定义是 _'不被接受的'_ 。
  *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (combine_odd_even)  *)
(** 完成[combine_odd_even]的定义；它取两个针对数字的性质作为它的两个参数
    [Podd]和[Peven]，并返回这样的性质[P]：[P n]在[n]为奇数的时候等价于[Podd n]，
    在[n]为偶数的时候等价于[Peven n]。 *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** 证明下述的事实以测试你的定义是否正确。 *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(**
    Coq拥有一个将它从其他证明助理区分开来的特性：它将 _'证明本身'_ 也作为
    第一等的值。在这一点的背后有许多更深入的细节，但是对于使用Coq而言这
    些细节并不是必须要了解的事实。这一节只是对相关内容进行一点简单的说明；
    更多的细节可以在[ProofObjects]和[IndPrinciples]这两个可选的章节中得知。 *)

(** 我们已经知道[Check]可以显示一个表达式的类型；我们也可以用[Check]查找某个
    名字所指的定理：*)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** 在显示[plus_comm]这一定理所声明的 _'命题'_ 时，Coq使用了与显示某个值的 _'类
    型'_ 一样的方式。为什么会这样呢？
    实际上[plus_comm]所指向的是一个被称作 _'证明对象'_ 的结构，它表示了证实
    [forall n m : nat, n + m = m + n]这一命题的逻辑上的演化过程。这一对象的
    类型 _'就是'_ 它所证明的命题。 *)

(**
    就直觉上而言这是十分自然的：定理的声明部分说明了这一定理能被用于什么场合，
    就像某个计算对象的类型说明了这一对象能被如何使用一样。例如，如果某个项的类
    型为[nat -> nat -> nat]；这说明我们可以将其用在两个[nat]上，然后得到一个[nat]。
    类似地，如果我们有类型为[n = m -> n + n = m + m]的对象，当我们给出类型为[n = m]
    的“证据”时，我们就能运用这一定理并得到[n + n = m + m]。 *)

(**
    就操作本身而言，我们能够将这种类比向前更推进一步：定理能被当作函数应用在有着正确类型的
    假设上；这样我们在将其结论特殊化的时候就不需要向证明中插入断言。比如说，假设现在我们
    想要证明如下的结果：*)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** 这个定理的证明初看上去十分简单，我们只要用[plus_comm]做两次重写就行了；然而问题是，
    第二次重写的效果会与第一次重写互相抵消：*)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

(** 我们可以使用我们已经知道的工具通过这个简单的方法来解决这个问题：用[assert]在中间插入被
    实例化了的[plus_comm]；这样我们就能够按照我们想要的方式进行重写： *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(**
    另外一个更为简洁优雅的方法是将[plus_comm]直接应用在我们想要以之实例化的参数上，
    就像我们将一个多态函数应用到某个类型时所做的那样： *)

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** 对于几乎所有以定理作为其参数的证明策略，你都可以这么将一个定理作为函数应用到
    某些参数上，并将得到的实例化的定理传给这些证明策略；注意，定理应用所使用的类
    型推导机制跟函数应用的是同一种，所以就像对某个函数所做的那样，你可以将通配符
    作为定理的参数，也可以将某些作为参数的前提定义为隐式参数。这些用法在以下的证
    明中都能够看到：*)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** 在以后的章节中我们将会看到更多这方面的例子。*)

(* ################################################################# *)
(** * Coq vs. 集合论  *)

(**
    Coq的核心，即被称作 _Calculus of Inductive Constructions_ 的系统，在一些很重要的方面
    与其他被数学家们用于写下精确而严谨的证明的形式系统不一样。例如在主流数学中使用最普遍
    的策梅洛-弗兰克尔（Zermelo-Fraenkel）集合论：在这一形式系统中一个数学对象可以同时是许
    多不同的集合的成员；而在Coq的逻辑中，一个项有且仅有一个类型。这些区别的存在使得人们
    需要用稍微有些不同的方式去描述同一种非形式化的数学概念，但是这些都是十分自然且易于理
    解使用的。比如说，在Coq中我们一般不会说某个自然数[n]属于某个包含了全体偶数的集合；而
    作为替代地, 我们会有（或定义）[ev : nat -> Prop]这种描述了全体偶数的性质，然后说[ev n]
    这一命题为真。
    然而也存在着对于某些数学概念/论证而言不为核心的逻辑系统引入新的公理就难以进行
    描述甚至是无法描述的的情况。我们将以对两个世界之间的一些最显著的差别的讨论作为
    这一章节的结束。 *)

(* ================================================================= *)
(** ** 函数外延性 *)

(**
    目前为止我们所看见的有关相等性的断言基本上都只是有关归纳类型（例如[nat]和
    [bool]，诸如此类），但是由于Coq的相等操作符是多态的，这些并不是唯一能够有
    相等性命题的类型——举例而言，我们能够写出声明了 _'两个函数相等'_ 的命题：*)

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** 在一般的数学研究中，对于任意的两个函数[f]和[g]，只要它们所产生的结果相等，
    那么它们就会被认为相等：

    (forall x, f x = g x) -> f = g

    这被称作 _'函数外延性'_ 原理。
    不甚严谨地说，所谓“外延性”指的是某个对象的可观察的行为；因此函数外延性指
    的就是某个函数的身份完全由其行为，（用Coq的术语来说）也就是由我们将其应用于
    参数上之后所能得到的结果确定。
    函数外延性并不在Coq的基本公理之内；因此某些“应该为真”的命题是不能被证明的：*)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* 卡住了 *)
Abort.

(** 但是我们能用[Axiom]这一命令将函数外延性添加到Coq的核心逻辑系统之中： *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** [Axiom]的效果与定义一个定理然后用[Admitted]跳过证明部分相同，但是它会提示我们
    这是一个公理：我们不需要为其加上证明。
    现在我们能够在证明中使用函数外延性了： *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** 当然，在为Coq增添新的公理的时候我们必须十分小心，因为新增添的公理可能会与
    现有的公理导致整体的 _'不一致'_ ；而当系统不一致的时候，任何命题都能够被证明为真，
    包括[False]。但不幸的是，并没有什么简单的能够判断某条公理会不会与现有的公理
    产生不一致的方法：一般而言，确认某一组公理的一致性都需要付出艰辛的努力；然
    而我们已经知道，添加函数外延性并不会导致这种不一致。
    我们可以用[Print Assumptions]查看某个证明所依赖的所有附加公理。 *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 4 stars (tr_rev)  *)
(** 对于[rev]的定义我们有一个问题：在[rev]的每一步都会执行一次对[app]的调用，
    而一次[app]调用所需要的时间大致上与列表的长度成正比。也就是说，[rev]有着
    与列表长度成平方关系的时间复杂度。我们能够用下面的定义来对这个问题作出改进： *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

(** 这个定义被称作是 _'尾递归的'_ ，因为对函数自身的递归调用是所需进行的操作中的
    最后一个（也就是说在递归调用之后我们并不进行[++]）。一个足够好的编译器会针对
    这样的源码生成非常高效的目标代码。证明这两个定义等价。 *)

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** 命题与布尔代数  *)

(** 我们已经知道在Coq中有两种不同的描述逻辑事实的方式：布尔表达式（类型为[bool]的值）
    和命题（类型为[Prop]的值）。举例而言，我们能够通过以下两种方式声明某个数字[n]为偶数：
      - (1) [evenb n]返回[true]；
      - (2) 或者存在某些使得[n = double k]的数字[k]。
      这两个对“偶数性”的定义确实是等价的；我们能够证明一些辅助用的引理来证明这一点。
    我们一般说[evenb n]这一布尔值 _'反映'_ 了命题[exists k, n = double k]。 *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** 类似地，我们可以用类似的两种方式声明任意的两个数字[n]和[m]的相等性：(1)
    [beq_nat n m]返回[true]，以及(2)[n = m]。这两种方式也是等价的。 *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** 然而，即使就逻辑上而言这两种表达方式是等价的，在进行具体的操作时它们也是不一样的。
    相等性就是这种例子之中较为极端的一个：[beq_nat n m = true]这一假设对于有关[n]和[m]的
    命题的证明而言几乎没有帮助，但是如果我们将这一假设变换为[n = m]这一等价的形式，我们就
    能够将其用于重写。
    偶数性也是一个比较有意思的例子。回想一下，在我们证明[even_bool_prop]的反方向部分
    （即[evenb_double]，从命题到布尔表达式的方向）的时候，我们只是简单地对[k]使用了
    归纳法；而证明另一个方向（即[evenb_double_conv]这一练习）的命题则需要某种十分聪明
    的对命题进行一般化的手段，因为我们不能直接证明[(exists k, n = double k) -> evenb = true]。
    对这些例子而言，命题性的声明比起它们所对应的布尔表达式而言要更为有用；但并不是
    在任何情况下都是如此。比如说，在函数的定义里我们不能检查某个任意的命题是否为真；
    因此这段代码是不被接受的： *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(**
    Coq会拒绝接受这段代码并给出「[n = 2]的类型为[Prop]」这样的错误信息，因为它想要的
    是一个[bool]（或其他的有两个元素的归纳类型）。出现这条错误信息的原因跟Coq的核心语言
    有关：其 _'计算性'_ 的特性使得它只能表达可计算的全函数。这么做的原因之一是为了能够
    从使用Coq开发的代码中抽取可以执行的程序。因此在Coq中 _'并没有'_ 某种通用的判断任意
    [Prop]是否为真的按类分析操作：一旦存在这种操作，我们就能够用它来写出不可计算的函数。
    
    即使一般的不可计算的函数不能被表示为布尔代数中的运算，我们也应该知道即使是对于 _'可计算的'_ 
    性质而言也存在着使用[Prop]会比[bool]方便的场合，因为递归函数定义受限于Coq对于相关内容的限制。
    比如说，下一章将会讲述如何使用[Prop]定义「某个正则表达式可以匹配某个给出的字符串」这一性质；
    如果使用[bool]，那么就会需要真的写一个正则表达式的匹配器：这么做会更加复杂，更加难以理解，同时
    也更加难以对相关的内容进行推理和证明。
    相反的，使用布尔值会带来一个重要的好处：通过对Coq中的项进行计算能够实现一些证明的自动化。这一
    技巧被称作_proof by reflection_。考虑下面的例子： *)

Example even_1000 : exists k, 1000 = double k.

(** 对于这个命题而言，最为直接的证明方式是直接给出[k]的值。 *)

Proof. exists 500. reflexivity. Qed.

(** 而与它对应的使用了布尔值的声明的证明则要更加简单些： *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** 有趣的是，因为这两种定义是等价的，我们能够不显式地指出500这个值而用相对应的布尔值
    方程式去完成它的对应物的证明： *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(**
    虽然在这个例子中证明的长度并没有因此而缩减多少，但是对于更加大型的证明我们一般都
    可以用反射技巧让它们变得更小。一个比较极端的例子是，在用Coq证明著名的 _'四色定理'_ 
    时人们使用了反射技巧将对几百种不同的情况的分析工作缩减成一个对布尔值的计算。我们
    不会详细地讲解反射技巧，但是对于展示布尔值计算和一般命题的互补的优势而言，它是个
    很好的例子。 *)

(** **** Exercise: 2 stars (logical_connectives)  *)
(** 下述引理将在这一章中进行了讨论的命题性的连接符跟相对应的布尔运算操作联系了起来。*)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** 下述引理是命题[beq_nat_true_iff]的“非”版本；在某些情况下这一引理会使事情变得
    更为方便些。（在以后的章节中我们将会看到更多这方面的例子） *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (beq_list)  *)
(** 给定一个用于确定类型为[A]的值之间的相等性的布尔操作符[beq]，我们能够定义
    可以检测两个包含类型为[A]的值的列表是否相等的函数[beq_list beq]。完成下面
    [beq_list]的定义。证明[beq_list_true_iff]这一引理以确认你的定义是正确的。 *)

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** 回忆一下在[Tactics]一章中来自练习[forall_exists_challenge]的函数[forallb]： *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** 证明下述将[forallb]跟[All]这一性质联系起来的定理。*)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** 是否存在没有被这个规范描述包括的关于函数[forallb]的性质？*)

(* FILL IN HERE *)
(** [] *)

(* ================================================================= *)
(** ** 经典逻辑 vs. 构造逻辑  *)

(**
    我们已经知道，在定义一个Coq函数时我们没有办法判断某个命题[P]是否为真；你或许会
    对为此感到惊讶：对于 _'证明'_ 而言也存在类似的限制！换句话说，下面的推理原则即使
    符合直觉，但是在Coq中它是不可被证明的：*)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(**
    回想一下，在证明形如[P \/ Q]的命题时，我们使用[left]和[right]这两个策略；为了使用
    这两个策略证明这些命题，我们需要知道哪一边能够被证明为真。但是在[excluded_middle]中，
    [P]是被全程量化的，它可以指代任意命题；因此我们对[P]本身一无所知，所以我们也不能得到
    足够让我们确定用[left]还是[right]的信息，就像Coq因为缺乏信息而不能在函数内部机械地确定
    [P]是否为真一样。 *)

(** 然而，如果我们恰好知道[P]被某个布尔项[b]反射，那么我们就能很轻易地知道它究竟是否为真：
    我们只要检测[b]的值就可以了。 *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** 特别地，对于关于自然数[n]和[m]的等式[n = m]而言，排中律是成立的。*)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

(**
    通用的排中律在Coq中并不是默认可以使用的；这一点看上去或许很奇怪，毕竟任何声明
    肯定都是非真即假的。然而不假设排中律存在也有它的优势：Coq中的声明可以比在标准数学
    中同样的声明更强。比如说，如果存在[exists x, P x]的Coq证明，那么我们就能够直接
    展示出能够让我们证明[P x]的[x]的值；也就是说，任何关于存在性的证明一定都是 _'构造性'_ 的。 *)

(** 像Coq一样不假设排中律的正确性的逻辑系统被称作 _'构造逻辑'_ ；而更加常规的、排中律
    对于任意命题都成立的逻辑系统（例如ZFC集合论）则被称作 _'经典逻辑'_ 。 *)

(** 下述例子展示了为什么假设排中律成立会导致非构造性的证明：
    _'声明'_ ：存在无理数[a]和[b]使得[a ^ b]为有理数。
    _'证明'_ ：易知[sqrt 2]为无理数。如果[sqrt 2 ^ sqrt 2]为有理数，那么可以取
    [a = b = sqrt 2]；如果[sqrt 2 ^ sqrt 2]为无理数，那么可以取[a = sqrt 2 ^ sqrt 2]和
    [b = sqrt 2]，因为[a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2]。[]
    看得到在这个证明中发生了什么吗？我们在不知道[sqrt 2 ^ sqrt 2]是否为有理数的
    情况下就使用了排中律将它分为两种不同的情况；因此在最后，我们知道这样的[a]和[b]
    是存在的，但是我们并不能确定它们的值。
    即使构造逻辑很有用，它也有它的限制：有很多在经典逻辑中能够轻易被证明的声明会有
    更加复杂的构造性证明，而对于某些声明而言这样的证明甚至不存在。幸运的是，排中律
    就像函数外延性一样与Coq的逻辑系统相兼容；我们可以安全地将其作为公理添加到Coq中。
    但是在这本书中我们不需要这样做：这本书所覆盖的内容都可以使用构造逻辑得到，而且
    因此所产生的额外的耗费都微不足道。
    一般而言在意识到有哪些证明技巧不应该在进行构建性证明时使用之前都要经过一定的实践和
    练习，但是在这些证明技巧之中反证法尤为臭名昭著，因为它的使用将会导向一个非构造性的
    证明。这里是一个典型的例子：假设我们希望证明存在有着性质[P]的某个[x]，也就是说，
    我们希望证明存在某个[x]使得[P x]。我们先假设这个命题为假，即假设[~ exists x, P x]。
    从这个假设中我们不用特别费劲就能得到[forall x, ~ P x]。如果我们能够通过这个命题得到
    矛盾，我们就能够得到一个对于存在性的证明，即使我们完全没有指出能够使[P x]成立的[x]的值。
    从构造性的角度来看，在这里存在着的技术上的瑕疵，是我们试图用[~ ~ (exists x, P x)]的证明
    去证明[exists x, P x]。从下面的练习我们可以看到，允许自己从任意声明中去掉双重否定等价于
    引入排中律。因此只要不引入这一额外的公理，我们就不能在Coq中写出这行证明。 *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** 通用的排中律跟Coq之间的一致性的证明十分复杂而且并不能在Coq系统自身进行。然而，下述定理
    说明了对于 _'任意指定的某个'_ Prop [P]而言，加入一个可判定公理（也就是一个排中律的特例）
    都是安全的。之所以这样是因为我们不能证明这样的公理的否定命题；如果我们能够证明这样的命题，
    那么我们就会同时有[~ (P \/ ~P)]和[~ ~ (P \/ ~P)]，而这将产生矛盾。*)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (not_exists_dist)  *)
(** 在经典逻辑中有这么一条定理；它声明下述两条假设是等价的：

    ~ (exists x, ~ P x)
    forall x, P x

    [dist_not_exists]证明了这一等价性的其中一个方向。有趣的事是，在构造逻辑中我们
    不能证明另外一个方向。你的任务就是证明这个方向的证明能够使用排中律得到。*)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, optional (classical_axioms)  *)
(** 对于那些喜欢挑战的人，这里是摘自Bertor和Casteran所著的Coq'Art这本书（第123页）的练习。
    下述的四个句子，包括上面提到的[excluded_middle]，都被认为描述了经典逻辑。在Coq中我们不能
    证明它们，但是假如我们希望在经典逻辑下工作的话，我们可以安全地将其中任意一条作为公理添加
    到Coq中。
    证明这五个命题（以下四个以及[excluded_middle]）互相等价。 *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
(** [] *)

(** $Date: 2017-03-05 13:25:50 -0800 (Sun, 05 Mar 2017) $ *)
