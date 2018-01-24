(** * 归纳法：用归纳法证明 *)

(** 在开始之前，我们需要把上一章中所有的定义都导入进来： *)

Require Export Basics.

(** 为了让 [Require Export] 起效，首先你需要用 [coqc] 将 [Basics.v] 编译成
    [Basics.vo]，这类似于将 .java 文件编译成 .class 文件，或将 .c 文件编译成 .o
    文件。我们有两种方法：
     - 在 CoqIDE 中：
         打开 [Basics.v]。在「Compile」菜单中点击「Compile Buffer」。
     - 在命令行中：
         执行 [coqc Basics.v]
   如果你遇到了问题（例如，稍后你可能会在本文件中遇到缺少标识符的提示），
   那可能是因为没有正确设置 Coq 的「加载路径」。命令 [Print LoadPath.]
   能帮你理清这类问题。 *)

(* ################################################################# *)
(** * 归纳法证明 *)

(** 我们在上一章中用一个基于化简的简单论据证明了 [0] 是 [+] 的左幺元。
    我们也观察到，当我们打算证明 [0] 也是 [+] 的 _'右'_ 幺元时... *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

(** ...事情就没这么简单了。只应用 [reflexivity] 的话不起作用，因为 [n + 0] 中的
    [n] 是任意未知数，所以在 [+] 的定义中 [match] 无法被化简。  *)

Proof.
  intros n.
  simpl. (* 不起作用！ *)
Abort.

(** 即便用 [destruct n] 分类讨论也不会有所改善：诚然，我们能够轻易地证明 [n = 0]
    时的情况；但在证明对于某些 [n'] 而言 [n = S n'] 时，我们又会遇到与此前相同的问题。 *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* 虽然目前还没啥问题... *)
  - (* n = S n' *)
    simpl.       (* ...不过我们又卡在这儿了 *)
Abort.

(** 虽然还可以用 [destruct n'] 再推进一步，但由于 [n] 可以任意大，
    如果照这个思路继续证明的话，我们永远也证不完。 *)

(** 为了证明这种关于数字、列表等归纳定理的集合的有趣事实，
    我们通常需要一个更强大的推理原理： _'归纳'_ 。
    回忆一下_自然数的归纳原理_，你也许曾在高中的数学课上，在某门离散数学课上或
    在其它类似的课上学到过它：若 [P(n)] 为涉及自然数的命题，而我们想要证明 [P]
    对于所有自然数 [n] 都成立，那么可以这样推理：
         - 证明 [P(O)] 成立；
         - 证明对于任何 [n']，若 [P(n')] 成立，那么 [P(S n')] 也成立。
         - 最后得出 [P(n)] 对于所有 [n] 都成立的结论。
    在 Coq 中的过程也一样：我们以证明 [P(n)] 对于所有 [n] 都成立的证明目标开始，
    然后（通过应用 [induction] 策略）把它分为两个子目标：一个是我们必须证明
    [P(O)] 成立，另一个是我们必须证明 [P(n') -> P(S n')]。下面就是该定理的用法： *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(** 和 [destruct] 一样，[induction] 策略也能通过 [as...] 子句为引入到
    子目标中的变量指定名字。由于这次有两个子目标，因此 [as...] 有两部分，用 [|]
    隔开。（严格来说，我们可以忽略 [as...] 子句，Coq 会为它们选择名字。
    然而在实践中这样不好，因为让 Coq 自行选择名字的话更容易导致理解上的困难。）
    在第一个子目标中 [n] 被 [0] 取代。由于没有新的变量会被引入，因此 [as ...]
    字句的第一部分为空；而当前的目标会变成 [0 + 0 = 0]：使用化简就能得到此结论。
    在第二个子目标中，[n] 被 [S n'] 所取代，而对 [n'] 的归纳假设（Inductive
    Hypothesis），即 [n' + 0 = n'] 则以 [IHn'] 为名被添加到了上下文中。
    这两个名字在 [as...] 子句的第二部分中指定。在此上下文中，待证目标变成了
    [(S n') + 0 = S n']；它可被化简为 [S (n' + 0) = S n']，而此结论可通过
    [IHn'] 得出。 *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** （其实在这些证明中我们并不需要 [intros]：当 [induction] 策略被应用到
    包含量化变量的目标中时，它会自动将需要的变量移到上下文中。） *)

(** **** Exercise: 2 stars, recommended (basic_induction)  *)
(** 用归纳法证明以下命题。你可能需要之前的证明结果。 *)

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

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (double_plus)  *)
(** 考虑以下函数，它将其参数乘二： *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** 用归纳法证明以下关于 [double] 的简单事实： *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_S)  *)
(** 我们的 [evenb n] 定义对 [n - 2] 的递归调用不大方便。这让证明 [evenb n]
    时更难对 [n] 进行归纳，因此我们需要一个关于 [n - 2] 的归纳假设。
    以下引理给予了 [evenb (S n)] 另一个表征，使其在归纳时能够更好地工作：
    我们对 [evenb n] 的定义有一点不太方便的地方：它以 [n - 2] 为参数进行了递归调用；
    在为了证明与 [evenb n] 有关的事实而对 [n] 使用归纳法时，这会让证明过程变得更为困难，
    因为我们可能会需要一个关于 [n - 2] 的归纳假设。以下引理用一种不同的方式刻画了
    [evenb (S n)] 的性质，这将使归纳过程变得更加容易。 *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 starM (destruct_induction)  *)
(** 简要说明一下 [destruct] 策略和 [induction] 策略之间的区别。
(* FILL IN HERE *)
*)
(** [] *)

(* ################################################################# *)
(** * 证明里的证明 *)

(** 和在非形式化的数学中一样，在 Coq 中，大的证明通常会被分为一系列定理，
    后面的定理引用之前的定理。但有时一个证明会需要一些繁杂琐碎的事实，
    而这些事实缺乏普遍性，以至于我们甚至都不应该给它们单独取顶级的名字。
    此时，如果能仅在需要时简单地陈述并立即证明所需的「子定理」就会很方便。
    我们可以用 [assert] 策略来做到。例如，我们之前对 [mult_0_plus]
    定理的证明引用了前一个名为 [plus_O_n] 的定理，而我们只需内联使用 [assert]
    就能陈述并证明 [plus_O_n]： *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** [assert] 策略引入两个子目标。第一个为断言本身，通过给它加前缀 [H:]
    我们将该断言命名为 [H]。（我们也可以用 [as] 来命名该断言，就像我们前面用
    [destruct] 和 [induction] 做的那样。例如 [assert (0 + n = n) as H]。）
    注意我们用花括号 [{ ... }] 将该断言的证明括了起来。这么做不仅是为了提高可读性，
    同时也为了在交互地使用 Coq 时能更容易地看到我们已经证明了这个子目标。第二个目标
    跟执行 [assert] 之前的子目标一样，只是这次在上下文中，我们有了名为 [H] 的前提
    [0 + n = n]。也就是说，[assert] 生成的第一个子目标是我们必须证明的已断言的事实，
    而在第二个子目标中，我们可以使用已断言的事实在一开始试图证明的事情上取得进展。 *)

(** 另一个 [assert] 的例子... *)

(** 例如，假设我们想要证明 [(n + m) + (p + q) = (m + n) + (p + q)]。
    [=] 两边唯一的不同就是第一个内部的 [+] 的参数 [m] 和 [n] 交换了位置，
    所以看起来我们可以用加法交换律（[plus_comm]）来将它重写为另一个。然而，
    [rewrite] 策略对于应该在_哪里_起作用这点一并不聪明。本命题中 [+] 用了三次 ，
    结果 [rewrite -> plus_comm] 只对_外层_那个起了作用... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* 我们只需要为 (m + n) 交换 (n + m)... 看起来 plus_comm 能搞定！*)
  rewrite -> plus_comm.
  (* 不起作用... Coq 选错了要改写的加法！ *)
Abort.

(** 为了在需要的地方使用 [plus_comm]，我们可以（为此处讨论的特定的 [m] 和 [n]）
    引入一个局部引理来陈述 [n + m = m + n]，然后我们用 [plus_comm] 证明它，
    并用它来进行期望的改写。 *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** 「非形式化证明是算法，形式化证明是代码。」 *)

(** What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true --
    an unassailable argument for the truth of [P].  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** 例如，下面是加法交换律的一个证明： *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq 对此表示十分满意。然而人类却很难理解它。我们可以用注释和标号让它
    的结构看上去更清晰一点... *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** ...而且如果你习惯了 Coq，你可能会在脑袋里逐步过一遍策略，并想象出
    每一点的上下文和目标栈的状态。不过若证明再复杂一点，那就几乎不可能了。
    一个（迂腐的）数学家可能把证明写成这样： *)

(** - _'定理'_ ：对于任何 [n], [m] 和 [p],

      n + (m + p) = (n + m) + p.

    _'证明'_ ：对 [n] 使用归纳法。
    - 首先，设 [n = 0]。我们必须证明

        0 + (m + p) = (0 + m) + p.

      此结论可从 [+] 的定义直接得到。
    - 接着，设 [n = S n']，其中

        n' + (m + p) = (n' + m) + p.

      我们必须证明

        (S n') + (m + p) = ((S n') + m) + p.

      根据 [+] 的定义，由此式可得

        S (n' + (m + p)) = S ((n' + m) + p),

      它由归纳假设直接得出。 _'证毕'_ 。 *)

(** 证明的总体形式大体类似，当然这并非偶然：Coq 的设计使其 [induction]
    策略会像数学家写出的标号那样，按相同的顺序生成相同的子目标。但咱细节上则有
    明显的不同：形式化证明在某些方面更为明确（例如对 [reflexivity] 的使用），
    但在其它方面则不够明确（特别是 Coq 证明中任何给定点的「证明状态」都是完全
    隐含的，而非形式化证明则常会反复告诉读者目前证明进行的状态）。 *)

(** **** Exercise: 2 stars, advanced, recommendedM (plus_comm_informal)  *)
(** 将你对 [plus_comm] 的解答翻译成非形式化证明：
    定理：加法满足交换律。
    证明： (* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, optionalM (beq_nat_refl_informal)  *)
(** 以 [plus_assoc] 的非形式化证明为范本，写出以下定理的非形式化证明。
    不要只是用中文来解释 Coq 策略！
    定理： 对于任何 [n]，均有 [true = beq_nat n n]。
    证明 (* FILL IN HERE *)
[] *)

(* ################################################################# *)
(** * 更多练习 *)

(** **** Exercise: 3 stars, recommended (mult_comm)  *)
(** 用 [assert] 来帮助证明此定理。你应该不需要对 [plus_swap] 进行归纳。 *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** 现在证明乘法交换律。（你在证明过程中可能需要定义并证明一个独立的辅助定理。
    你可能会用上 [plus_swap]。） *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** 找一张纸。对于以下定理，首先请_思考_ (a) 它能否能只用化简和改写来证明，
    (b) 它还需要分类讨论（[destruct]），以及 (c) 它还需要归纳证明。先写下你的
    预判，然后填写下面的证明（你的纸不用交上来，这只是鼓励你先思考再行动！） *)

Theorem leb_refl : forall n:nat,
  true = leb n n.
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
  leb n m = true -> leb (p + n) (p + m) = true.
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

(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** 证明以下定理。（把 [true] 放在等式左边可能看起来有点奇怪，不过 Coq 标准库中
    就是这样表示的，我们照做就是。无论按哪个方向改写都一样好用，所以无论我们如何
    表示定理，用起来都没问题。） *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap')  *)
(** [replace] 策略允许你指定一个具体的要改写的子项和你想要将它改写成的项：
    [replace (t) with (u)] 会将目标中表达式 [t]（的所有副本）替换为表达式 [u]，
    并生成 [t = u] 作为附加的子目标。在简单的 [rewrite] 作用在目标错误的部分上时
    这种做法通常很有用。
   用 [replace] 策略来证明 [plus_swap']，除了无需 [assert (n + m = m + n)]
   外和 [plus_swap] 一样。 *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, recommendedM (binary_commute)  *)
(** 回忆一下你在 [Basics] 中为练习 [binary] 编写的 [incr] 和 [bin_to_nat]
    函数。证明下图可交换。

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    也就是说，一个二进制数先自增然后将它转换为（一进制）自然数，和先将它转换为
    自然数后再自增会产生相同的结果。将你的定理命名为 [bin_to_nat_pres_incr]
    （「pres」即「preserves」的简写，意为「保持原状」）。
    在你开始做这个练习前，将你在 [binary] 练习的解中的定义复制到这里，
    让这个文件可以被单独评分。若你想要更改你的原始定义以便让此属性更易证明，
    请自便！ *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advancedM (binary_inverse)  *)
(** 本练习是前一个关于二进制数的练习的延续。你需要你在其中的定义和定理来完成这个；
    请将它们复制到本文件中让它自包含以便评分。
    (a) 首先，写一个将自然数转换为二进制数的的函数。然后证明对于所有自然数，
        用此函数将其转换为二进制数后，再转换回自然数会得到和原来一样的自然数。
    (b) 你也许会自然而然地想到，将一个二进制数转换为自然数再转换为二进制数之后
        应该得到与原二进制数相同的结果。然而，这并不是真的！解释问题出在哪。
    (c) 定义一个「直接的」规范化函数——即，一个从二进制数到二进制数的函数
        [normalize]，使得对于任何二进制数 b，将其转换为自然数后再转换二进制数
        会产生 [(normalize b)]。证明它。（警告：这部分有点棘手！）
    再次说明，如果对此有帮助的话，请随意更改你之前的定义。 *)

(* FILL IN HERE *)
(** [] *)

(** $Date: 2017-03-05 13:25:50 -0800 (Sun, 05 Mar 2017) $ *)
