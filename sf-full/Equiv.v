(** * Equiv: 程序等价性 *)

(* IMPORTS *)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.
(* /IMPORTS *)

(** *** 一些关于练习的一般性建议:
    - 这里要进行的大多数Coq证明都与先前我们所提供的相似. 在做作业之前, 花一些时间
      （非形式化的在纸上和Coq中）思考我们的证明确保你理解他们的的每一个细节. 这会节省你
      大量的时间.
    - 我们现在进行的Coq证明已经足够复杂，以至于近乎不可能单靠“灵感”或者以随机的尝试误打误撞的完成证明。你需要一个关于为何
      某个属性为真以及如何进行证明的概念并从这个概念开始。完成这一项任务的最好的方
      法是在开始进行形式化证明之前至少在纸上写出一个非形式化证明的梗概
      --直观的说服自己相信定理成立--然后再进行形式化证明。另外，
      你也可以拉来一个好友，尝试说服他相信这条定理成立; 然后试着形式化你刚才的解释。
    - 使用自动化工具来减少工作量！本章的一些证明练习，如果全部一个个分类去分析的话
      会非常长. *)

(* ################################################################# *)
(** * 行为的等价性 *)

(** 在上一章中我们讨论了一个非常简单的程序变换的正确性; [optimize_0plus] 函数。
    这是我们考虑的算数表达式语言的第一个版本--它没有变量--所以很容易定义 _'什么是'_ 
    正确的程序变换： 即输出一个求值结果与原程序相同的程序。
    
    为了更进一步的讨论整个Imp语言变换的正确性，我们需要考虑状态和变量的作用。 *)

(* ================================================================= *)
(** ** 定义 *)

(** 对于包含变量的 [aexp] 和 [bexp], 我们需要的定义简单明了。在 _'所有状态'_
    下两个 [aexp] 或者 [bexp] 的求值结果相同，我们就说他们 _'行为等价'_ 。*)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** 对于命令，情况有些微妙。我们不能简单的说：“如果两个指令在相同的初始状态下求值到相同
    的终止状态，那么说这两个指令等价。”，因为有些命令（在某些初始状态下）根本不会在任何
    状态终止！我们实际上需要的是：“若两个指令在给出任何初始状态时都发散或者终止在相同
    的状态上，则这两个指令行为等价。”。简单的说就是：“如果其中一个终止在某
    状态上那么另一个也终止在这个状态上，反之亦然。” *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [SKIP]: *)

Theorem skip_left: forall c,
  cequiv
     (SKIP;; c)
     c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** Exercise: 2 stars (skip_right)  *)
(** 试证在任一命令后加上SKIP所变换出的新程序与原程序等价。 *)

Theorem skip_right: forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 类似的，这里是一些简化 [IFB] 的简单变换: *)

Theorem IFB_true_simple: forall c1 c2,
  cequiv
    (IFB BTrue THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. inversion H5.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** 当然，一些程序员会尝试以IF的判断条件字面上是否等于 [BTrue] 作为优化前提。但一个
    更有趣的方式是看IF的判断条件是否等价于真: *)
(** _Theorem_: 如果 [b] 等价于 [BTrue], 那么 [IFB b THEN c1
   ELSE c2 FI] 等价于 [c1].
*)
(**
   _Proof_:
     - ([->]) 我们必须证明, 对于所有 [st] 和 [st'], 如果 [IFB b
       THEN c1 ELSE c2 FI / st || st'] 则 [c1 / st || st'].
       能够应用于 [IFB b THEN c1 ELSE c2 FI / st || st'] 的证明规则只有两条：
       [E_IfTrue] 和 [E_IfFalse].
       - 假设 [IFB b THEN c1 ELSE c2 FI / st || st'] 证明自 [E_IfTrue]
         这条证明规则.  若使用证明规则 [E_IfTrue] 其必备的前提条件 [c1 / st || st'] 必为真， 而这正好是
         我们的证明所需要的条件。
       - 另一方面, 假设 [IFB b THEN c1 ELSE c2 FI / st || st'] 证明自
         [E_IfFalse]. 我们能得知 [beval st b = false] 和 [c2 / st || st'].
         之前提到 [b] 等价于 [BTrue], 也就是说对于所有 [st], 有[beval st b = beval st BTrue].
         具体的说就是 [beval st b = true] 成立, 导致 [beval st BTrue = true] 成立。 
         但是与此同时，之前假设 [E_IfFalse] 必备的前提条件 [beval st b = false] 也成立，
         这就构成了一组矛盾。从而说明不可能使用了 [E_IfFalse] 这条证明规则。
     - ([<-]) 我们必须证明，对于所有 [st] 和 [st'], 如果 [c1 / st || st']  
       则 [IFB b THEN c1 ELSE c2 FI / st || st'].
       已知 [b] 等价于 [BTrue], 我们知道 [beval st b] = [beval st BTrue] = [true].
       结合 [c1 / st || st'] 这条假设, 我们能应用 [E_IfTrue] 来证明出 [IFB b THEN
       c1 ELSE c2 FI / st || st'].  []
   下面是这个证明的形式化版本: *)

Theorem IFB_true: forall b c1 c2,
     bequiv b BTrue  ->
     cequiv
       (IFB b THEN c1 ELSE c2 FI)
       c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b 求值得出 true *)
      assumption.
    + (* b 求值得出 false (矛盾) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

(** **** Exercise: 2 stars, recommended (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** 证明我们可以通过对条件取反来交换 IF 的两个分支 *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 对于 [WHILE] 循环我们能够给出一组相似的定理：当一个循环的条件等价于 [BFalse] 的
    时候它等价于 [SKIP], 当一个循环的条件等价于 [BTrue] 的时候它等价于
    [WHILE BTrue DO SKIP END] （或者任意不终止的程序）。
    前者比较简单. *)

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(** **** Exercise: 2 stars, advanced, optional (WHILE_false_informal)  *)
(** 写出 [WHILE_false] 的非形式化证明.
(* FILL IN HERE *)
[]
*)

(** 为了证明第2个定理, 我们需要一个辅助定理: [WHILE] 循环在条件等价于
     [BTrue] 的时候循环不会终止: *)

(** _Lemma_: 如果 [b] 等价于 [BTrue], 则不可能像
     [(WHILE b DO c END) / st || st'] 这样会终止。
    _Proof_: 假设循环会终止，即 [(WHILE b DO c END) / st || st'].  我们将证明在通过
    对 [(WHILE b DO c END) / st || st'] 使用归纳法可以引出矛盾。
      - 假设 [(WHILE b DO c END) / st || st'] 使用了 [E_WhileEnd] 这条证明规则。
        那么根据假设得出 [beval st b = false] 。但是这和 [b] 等价于 [BTrue] 矛盾。
      - 假设 [(WHILE b DO c END) / st || st'] 使用了 [E_WhileLoop] 这条证明规则.
        结果就是给出了一个和 [(WHILE b DO c END) / st || st'] 矛盾的假设, 正巧是
        我们正要证明的那个!
      - 由于只有以上的几条规则可以证明出 [(WHILE b DO c END) / st || st'] 所以归纳时
        的其他的情况会立即导致矛盾。 [] *)

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* 大多数证明规则不可能应用，我们可以用 反演（inversion）来去除他们 *)
    inversion Heqcw; subst; clear Heqcw.
  (* 我们只关心这两个关于 WHILE 循环的证明规则: *)
  - (* E_WhileEnd *) (* 矛盾 -- b 总是 true! *)
    unfold bequiv in Hb.
    (* [rewrite] 能实例化Hb中的变量 [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* 直接使用IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, optional (WHILE_true_nonterm_informal)  *)
(** 试解释 [WHILE_true_nonterm] 的意义。
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, recommended (WHILE_true)  *)
(** 证明下面的定理. _'提示'_ : 你可能需要使用 [WHILE_true_nonterm]. *)

Theorem WHILE_true: forall b c,
  bequiv b BTrue  ->
  cequiv
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A more interesting fact about [WHILE] commands is that any finite
    number of copies of the body can be "unrolled" without changing
    meaning.  Unrolling is a common transformation in real compilers. *)

Theorem loop_unrolling: forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* 不执行循环 *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* 执行循环 *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* 执行循环 *)
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
      assumption. assumption. assumption.
    + (* 不执行循环 *)
      inversion H5; subst. apply E_WhileEnd. assumption.  Qed.

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Proving program properties involving assignments is one place
    where the Functional Extensionality axiom often comes in handy. *)

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
     - (* -> *)
       inversion H; subst. simpl.
       replace (t_update st X (st X)) with st.
       + constructor.
       + apply functional_extensionality. intro.
         rewrite t_update_same; reflexivity.
     - (* <- *)
       replace st' with (t_update st' X (aeval st' (AId X))).
       + inversion H. subst. apply E_Ass. reflexivity.
       + apply functional_extensionality. intro.
         rewrite t_update_same. reflexivity.
Qed.

(** **** Exercise: 2 stars, recommended (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (equiv_classes)  *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  WHILE BNot (BLe (AId X) (ANum 0)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_b : com :=
  IFB BEq (AId X) (ANum 0) THEN
    X ::= APlus (AId X) (ANum 1);;
    Y ::= ANum 1
  ELSE
    Y ::= ANum 0
  FI;;
  X ::= AMinus (AId X) (AId Y);;
  Y ::= ANum 0.

Definition prog_c : com :=
  SKIP.

Definition prog_d : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= APlus (AMult (AId X) (AId Y)) (ANum 1)
  END.

Definition prog_e : com :=
  Y ::= ANum 0.

Definition prog_f : com :=
  Y ::= APlus (AId X) (ANum 1);;
  WHILE BNot (BEq (AId X) (AId Y)) DO
    Y ::= APlus (AId X) (ANum 1)
  END.

Definition prog_g : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition prog_h : com :=
  WHILE BNot (BEq (AId X) (AId X)) DO
    X ::= APlus (AId X) (ANum 1)
  END.

Definition prog_i : com :=
  WHILE BNot (BEq (AId X) (AId Y)) DO
    X ::= APlus (AId Y) (ANum 1)
  END.

Definition equiv_classes : list (list com)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(* ################################################################# *)
(** * 行为等价的性质 *)

(** 现在我们开始开发之前定义的程序等价中的一些性质. *)

(* ================================================================= *)
(** ** 行为等价是一种等价性 *)

(** 首先, 我们验证 [aexps], [bexps], 和 [com] 的确满足 _'等价性'_ （ _equivalences_ ）
    -- 也就是说, 它们都满足 自反性（reflexive），对称性（symmetric）和 传递性（transitive）。
    这些证明全都不难。 *)

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
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* 断言的证明 *) apply H. }
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
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23.  Qed.

(* ================================================================= *)
(** ** 行为等价是一种一致性 *)

(** 不太明显地, 行为等价也满足 _'一致性'_ （ _congruence_ ). 也就是说
    两个子程序等价那么只有子程序有差异的两个大程序也等价:

              aequiv a1 a1'
      -----------------------------
      cequiv (i ::= a1) (i ::= a1')
 
              cequiv c1 c1'    
              cequiv c2 c2'
         ------------------------
         cequiv (c1;;c2) (c1';;c2')

    ...等等.  *)

(** (注意我们这里用的推理规则记号并不是定义的一部分, 只是将一些合法的蕴含式用易读的方式写下而已.
    接下来我们将证明这些蕴含式.) *)

(** 我们会在接下来的章节（在 [fold_constants_com_sound] 的证明中）看到
    一些例子能够说明为何这些一致性十分重要。但是它的主要意义在于这些一致性允许我们在用一小部
    分程序替换一个大程序中等价的一部分并证明替换前和替换后程序的等价
    性时 _'无需'_ 进行与不变的部分相关的证明；也即是说，程序的改变所产生
    的证明的工作量与改变的大小而不是与整个程序的大小成比例。 *)

Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

(** 循环的一致性更有趣, 因为他需要使用归纳法（induction）.
    _Theorem_: 对于 [WHILE] ，等价性是一种一致性 -- 也就是说, 如果 [b1] 等价于 [b1']
    同时 [c1] 等价于 [c1'] ，那么 [WHILE b1 DO c1 END] 等价于
     [WHILE b1' DO c1' END] 。
    _Proof_: 假设 [b1] 等价于 [b1'] 同时 [c1] 等价于 [c1'] 。
    我们要证明，对于所有 [st] 和 [st'] ， [WHILE b1 DO c1 END / st || st']
    当且仅当 [WHILE b1' DO c1' END / st || st'] 。我们把两个方向分开考虑。
      - ([->]) 我们证明 [WHILE b1 DO c1 END / st || st'] 蕴涵
        [WHILE b1' DO c1' END / st || st'] ，对 [WHILE b1 DO c1 END / st || st']
        使用归纳法。只有推导最后所使用的规则是 [E_WhileEnd] 和 [E_WhileLoop] 情况才需要
	   特别进行讨论。
          - [E_WhileEnd]: 在这种情况时, 我们拥有假设的必备条件 [beval st b1 = false]
            和 [st = st'] 。但是，因为 [b1] 和 [b1'] 是等价的，
            我们有 [beval st b1' = false], 然后应用 [E-WhileEnd] ，
            得出我们需要的 [WHILE b1' DO c1' END / st || st'] 。
          - [E_WhileLoop]: 在这种情况时, 我们拥有假设的必备条件 [beval st b1 = true] ， 
            [c1 / st || st'0] 和 以及对某个状态 [st'0] 而言，有假设 [WHILE b1 DO c1 END / st'0 || st']
            ，另外还有归纳假设 [WHILE b1' DO c1' END / st'0 || st'] 。
            因为 [c1] 和 [c1'] 等价，推导出 [c1' / st || st'0] 。
            然后因为 [b1] 和 [b1'] 等价，推导出 [beval st b1' = true] ，
            最后应用 [E-WhileLoop] ，得出我们
            需要的 [WHILE b1' DO c1' END / st || st'] 。
      - ([<-]) 反之亦然. [] *)

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  (* WORKED IN CLASS *)
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - (* -> *)
    remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite <- Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite <- Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.
  - (* <- *)
    remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + (* E_WhileEnd *)
      apply E_WhileEnd. rewrite -> Hb1e. apply H.
    + (* E_WhileLoop *)
      apply E_WhileLoop with (st' := st').
      * (* show loop runs *) rewrite -> Hb1e. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity.  Qed.

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 比如, 这里有两个等价的程序, 和他们的等价性证明... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (* Program 2: *)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X)   (* <--- 这里有改动 *)
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

(** **** Exercise: 3 stars, advanced, optional (not_congr)  *)
(** We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(** * 程序变换 *)

(** _'程序变换'_ （ _program transformation_ ）是一种以任意程序
    作为输入并且输出这个程序的某种变体的函数。比如编译中的常量折叠优化就是
    一个典型的例子，但是程序变换不限于此。 *)

(** 如果一个程序变换的输出持有与其输入程序相同的行为，那么这个程序变换
    是 _'健全'_ （ _sound_ ）的. 
 
    我们可以定义出 [aexp], [bexp], 和 [com] 的健全性的概念。 *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** 常量折叠变换 *)

(** 如果一个表达式不引用变量, 那么他就是 _'常量'_ （ _constant_ ）.
 
    常量折叠是这样一种优化方式：找到常量表达式然后用它们的值替换它们. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId i        => AId i
  | APlus a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp
      (AMult (APlus (ANum 1) (ANum 2)) (AId X))
  = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

(** 注意这个版本的常量折叠不包括优化显而易见的加法等. -- 为了简单起见我们先
    把注意力集中在一个优化上.  把其他简化表达式的优化合并进来也不难; 只是
    定义和证明会更长. *)

Example fold_aexp_ex2 :
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6))
                             (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

(** 我们不仅可以把 [fold_constants_aexp] 优化到 [bexp] (比如在某些 [BEq]
    和 [BLe] 的时候), 我们也能找到一些 _'布尔'_ （ _boolean_ ）表达式的常量
    在原地化简他们. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
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
                 (AMinus (ANum 2) (APlus (ANum 1)
                                         (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

(** 为了化简程序中的常量, 我们需要在所有子表达式上使用适当的函数. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | i ::= a  =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
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
    (* 原程序: *)
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y))
             (APlus (ANum 2) (ANum 4)) THEN
       SKIP
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0)
             (AMinus (ANum 4) (APlus (ANum 2) (ANum 1)))
     THEN
       Y ::= ANum 0
     ELSE
       SKIP
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END)
  = (* 常量折叠后: *)
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP
     ELSE
       (Y ::= ANum 0)
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO
       X ::= APlus (AId X) (ANum 1)
     END).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 常量折叠的健全性 *)

(** 现在我们证明之前所做的事情的正确性. *)

(** 这是对算数表达式的证明: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum 和 AId 很显然 *)
    try reflexivity;
    (* 从IH和下面的观察出发很容易完成 APlus , Aminus 和 AMult 的情况的证明：
              aeval st (APlus a1 a2) 
            = ANum ((aeval st a1) + (aeval st a2)) 
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
(之后的s AMinus/minus 和 AMult/mult 同理) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, optional (fold_bexp_Eq_informal)  *)
(** 这里有一个 “布尔表达式常量折叠中 [BEq] 的健全性” 的非形式化证明。认真读完
    再和下面的形式化证明做比较。然后补充完整下面 [BLe] 的情况的形式化证明 （尽量
    不看之前的 [BEq] 的情况的证明 ）。
   _Theorem_: 布尔表达式的常量折叠函数 [fold_constants_bexp] ，有健全性。
   _Proof_: 我们必须证明 对于所有 [b] ， [fold_constants_bexp] 有健全性。
   我们在 [b] 上使用归纳法. 这里只给出 [b] 有 [BEq a1 a2] 的形式的证明。
   在本例中, 我们需要证明 

       beval st (BEq a1 a2) 
     = beval st (fold_constants_bexp (BEq a1 a2)).

   有两种情况需要讨论：
     - 首先，假设对于某些 [n1] 和 [n2] 而言有 [fold_constants_aexp a1 = ANum n1] 和
       [fold_constants_aexp a2 = ANum n2] 成立。
       在这种���况下，我们有

           fold_constants_bexp (BEq a1 a2) 
         = if beq_nat n1 n2 then BTrue else BFalse

       和

           beval st (BEq a1 a2) 
         = beq_nat (aeval st a1) (aeval st a2).

       由于算数表达式的健全性(定理 [fold_constants_aexp_sound])，可得

           aeval st a1 
         = aeval st (fold_constants_aexp a1) 
         = aeval st (ANum n1) 
         = n1

       和

           aeval st a2 
         = aeval st (fold_constants_aexp a2) 
         = aeval st (ANum n2) 
         = n2,

       所以

           beval st (BEq a1 a2) 
         = beq_nat (aeval a1) (aeval a2)
         = beq_nat n1 n2.

       同时, 容易看出 （在分别考虑 [n1 = n2] 和 [n1 <> n2] 的情况之后）

           beval st (if beq_nat n1 n2 then BTrue else BFalse)
         = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
         = if beq_nat n1 n2 then true else false
         = beq_nat n1 n2.

       所以

           beval st (BEq a1 a2) 
         = beq_nat n1 n2.
         = beval st (if beq_nat n1 n2 then BTrue else BFalse),
]]         
       正是所需的假设。
     - 另一方面，假设 [fold_constants_aexp a1] 和 [fold_constants_aexp a2]
       之中有一个不是常量。这种情况我们需要证明

           beval st (BEq a1 a2) 
         = beval st (BEq (fold_constants_aexp a1)
                         (fold_constants_aexp a2)),

       根据 [beval] 的定义，它等同于证明

           beq_nat (aeval st a1) (aeval st a2) 
         = beq_nat (aeval st (fold_constants_aexp a1))
                   (aeval st (fold_constants_aexp a2)).

       但是，由于算数表达式的健全性（定理 [fold_constants_aexp_sound]），可得出

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       本例证毕。 []
*)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue 和 BFalse 是显然的 *)
    try reflexivity.
  - (* BEq *)
    rename a into a1. rename a0 into a2. simpl.

(* 当存在许多构造子时使用归纳法会使得认为指定变量名成为
       一件琐事，然而Coq并不总是能够选择足够漂亮的变量名。
       我们可以使用 重命名（[rename]）策略: [rename a into a1] 
会把当前目标和上下文中的 [a] 替换成 [a1]. *)

    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.

    (* 唯一有趣的情况是 a1 和 a2 在折叠后同时变为常量 *)
      simpl. destruct (beq_nat n n0); reflexivity.
  - (* BLe *)
    (* FILL IN HERE *) admit.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** 补充以下证明的有关 [WHILE] 的部分. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* 如果if没有被优化掉, 那么我们很容易使用 IH 和 fold_constants_bexp_sound 来得出证明*)
    + (* b 总为真 *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b 总为假 *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** (0 + n) 优化的健全性, 最终版 *)

(** **** Exercise: 4 stars, advanced, optional (optimize_0plus)  *)
(** 回顾 [Imp] 中 [optimize_0plus] 的定义:

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

   注意这个函数是针对没有状态的旧 [aexp] 写的.
   给 [aexp] [bexp] 和 [com] 都写一个带状态的新版本:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   明这三个函数都具有健全性，就像之前证明 [fold_constants_*] 那样。
   （在 [optimize_0plus_com] 的证明中你需要一致性引理 -- 否则证明过程会 _'很长'_ ！）
   然后再在命令上定义一个新优化器，它首先使用常量折叠 （ [fold_constants_com] ）
   然后使用 [0 + n] 优化（ [optimize_0plus_com] ）。
   - 给这个优化器给出一个有意义的测试用例。
   - 证明这个优化程序有健全性。（这部分应该会 _'很简单'_ 。） *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(** * 证明程序不等价 *)

(** Suppose that [c1] is a command of the form [X ::= a1;; Y ::= a2]
    and [c2] is the command [X ::= a1;; Y ::= a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X ::= 42 + 53;;
               Y ::= Y + X)
       c2  =  (X ::= 42 + 53;;
               Y ::= Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** 我们马上就能看到这是不行的, 但是且慢, 现在, 看你自己能否找一个反例出来. *)

(** 下面形式化的定义描述了在算数表达式里如何把某个变量的所有引用替换为另一个表达式: *)

Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId i'       =>
      if beq_id i i' then u else AId i'
  | APlus a1 a2  =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (APlus (ANum 42) (ANum 53))
             (APlus (AId Y) (AId X))
= (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
Proof. reflexivity.  Qed.

(** 而这里是一个我们感兴趣的性质：它说明了类似上述形式的 [c1] 和 [c2] 总是等价.  *)

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

(** 遗憾的是, 这个性质 _'不'_ 总是成立. 
    _Theorem_: 对于所有 [i1], [i2], [a1], 和 [a2] 以下命题并不总是成立,

         cequiv (i1 ::= a1;; i2 ::= a2)
                (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).
]] 
    _Proof_: 我们使用反证法，假设对于所有 [i1], [i2], [a1], 和 [a2], 下面的假设成立

      cequiv (i1 ::= a1;; i2 ::= a2) 
             (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

    那么考虑下面的程序:

         X ::= APlus (AId X) (ANum 1);; Y ::= AId X

    注意下面的假设

         (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
         / empty_state || st1,

    在 [st1 = { X |-> 1, Y |-> 1 }] 时成立.
    根据假设

        cequiv (X ::= APlus (AId X) (ANum 1);; Y ::= AId X)
               (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))

    同时根据 [cequiv] 的定义, 我们有

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state || st1.

    同时我们也能证明出

        (X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1))
        / empty_state || st2,

    在 [st2 = { X |-> 1, Y |-> 2 }] 时成立。这里注意, 因为 [ceval] 是确定性的
    但是已知 [st1 <> st2] 这就造成矛盾!  [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* 这里有个反例: 假设 [subst_equiv_property] 让我们证明以下两个程序等价... *)
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= AId X)
      as c1.
  remember (X ::= APlus (AId X) (ANum 1);;
            Y ::= APlus (AId X) (ANum 1))
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  (* ... 让我们证明 [c2] 能终止于两个不同的状态: 
        st1 = {X |-> 1, Y |-> 1} 
        st2 = {X |-> 1, Y |-> 2}. *)
  remember (t_update (t_update empty_state X 1) Y 1) as st1.
  remember (t_update (t_update empty_state X 1) Y 2) as st2.
  assert (H1: c1 / empty_state \\ st1);
  assert (H2: c2 / empty_state \\ st2);
  try (subst;
       apply E_Seq with (st' := (t_update empty_state X 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  (* 最后, 因为程序求值的确定性而产生矛盾. *)
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 empty_state); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

(** **** Exercise: 4 stars, optional (better_subst_equiv)  *)
(** 之前我们想的等价性也不是完全胡说八道 -- 差一点就正确了. 只要增加一个
    条件就是正确的, 只要保证 [X] 不在第一个等式的右边出现. *)

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
  aeval (t_update st i ni) a = aeval st a.
Proof.
  (* FILL IN HERE *) Admitted.

(** 使用 [var_not_used_in_aexp] 形式化证明这个正确版的 [subst_equiv_property]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (inequiv_exercise)  *)
(** 证明死循环不等价于 [SKIP] *)

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * 扩展练习: 非确定性 Imp *)

(** 就像之前看到的 (在 Imp那章里的 [ceval_deterministic]), Imp 的关联的求值
    是确定性的.  但是, _'不确定性'_ 是很多程序语言定义中重要的一部分. 比如, 在很多
    命令式语言中 (比如C和类C的语言), 函数参数的求值顺序是未定义的. 程序片段

      x = 0;;
      f(++x, x)

    调用 [f] 的参数也许是 [(1, 0)] 又也许是 [(1, 1)], 取决于编译器的选择. 
    这可能让程序员有些困惑, 但是给了编译器作者选择实现的自由.
    在这个练习里, 我们要用一个简单的非确定性命令扩展 Imp 来学习这个扩展对响程
    序等价性有什么影响.  这个新命令写作 [HAVOC X], [X] 是一个标识符.
    执行 [HAVOC X] 的作用是给 [X] 分配一个不确定的 _'任意'_ 数字. 比如,
    计算这个程序之后:

      HAVOC Y;;
      Z ::= Y * 2

    [Y] 的值可以是任意变量, 且 [Z] 的值是 [Y] 的两倍 (所以 [Z] 总是偶数).
    注意, 我们并没有讨论输出值的 _'概率'_ -- 只是这里在执行非确定性代码后有
    非常多（无穷）的可能的不同的输出.
    某种意义上来说 [HAVOC] 大致相当与C语言中的未初始化变量. 经过了 [HAVOC]
    变量获得一个任意的但是不会改变的数字.  语言定义中非确定性大部分来源于程序员
    对程序到底作出了什么选择并不那么关心 (好处是能让编译器有自由选择运行速度更快的方法).
    我们称这个新语言为 _Himp_ (``在 Imp 上扩展了 [HAVOC]''). *)

Module Himp.

(** 为了形式化这个语言, 我们先在命令定义里增加一条. *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.                (* <---- 新的 *)

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' l" := (CHavoc l) (at level 60).

(** **** Exercise: 2 stars (himp_ceval)  *)
(** 现在, 我们必须扩展操作语义. 这里提供了一个 [ceval] 关系的模板, 规定了
    其大步语义. 现在为了形式化 [HAVOC] 规则还需要怎样的扩充？ *)

Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
      aeval st a1 = n ->
      (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
      c1 / st \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
      beval st b1 = false ->
      c2 / st \\ st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
      beval st b1 = true ->
      c1 / st \\ st' ->
      (WHILE b1 DO c1 END) / st' \\ st'' ->
      (WHILE b1 DO c1 END) / st \\ st''
(* FILL IN HERE *)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** 作为合理的检查, 下面的命题使用你的定义应该是可证的: *)

Example havoc_example1 : (HAVOC X) / empty_state \\ t_update empty_state X 0.
Proof.
(* FILL IN HERE *) Admitted.

Example havoc_example2 :
  (SKIP;; HAVOC Z) / empty_state \\ t_update empty_state Z 42.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** 最后, 我们重新定义和之前相同的等价性定理: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  c1 / st \\ st' <-> c2 / st \\ st'.

(** 这个定义对于可终止的程序仍然是合理的, 然后我们来用它证明非确定性程序的等价
    或者非等价. *)

(** **** Exercise: 3 stars (havoc_swap)  *)
(** 下面的两个程序等价吗? *)

Definition pXY :=
  HAVOC X;; HAVOC Y.

Definition pYX :=
  HAVOC Y;; HAVOC X.

(** 如果你认为他是等价的, 证明它是等价的, 如果认为它是不等价的, 也给出证明. *)


Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (havoc_copy)  *)
(** 下面的两个程序等价吗? *)

Definition ptwice :=
  HAVOC X;; HAVOC Y.

Definition pcopy :=
  HAVOC X;; Y ::= AId X.

(** 如果你认为他是等价的, 证明它是等价的, 如果认为它是不等价的, 也给出证明.
    (Hint: 你也许会发现 [assert] 策略很有用.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** 我们使用的程序等价的定义在无限循环的程序上的结果有点复杂. 因为 [cequiv] 
    描述的是 _'程序能够终止时'_ 两个程序的输出等价. 但是, 在有类似 Himp 的
    非确定性的语言里，有些程序总是停机，有些程序总是死循环，还有一些程序会
    非确定性地在某些时候停机或者在另外一些时候不断循环。下面习题的最后一部分展示了这个现象.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)  *)
(** 考虑下面两个命令: *)

Definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END.

Definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END.

(** 直觉上, 这两个程序有相同的终止行为: 要么都死循环, 要么终止在同一个状态.
    我们用下面的引理可以分别捕获 [p1] 和 [p2] 的终止行为: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ p1 / st \\ st'.
Proof. (* FILL IN HERE *) Admitted.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ p2 / st \\ st'.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)  *)
(** 你应该用这些引理证明 p1 和 p2 确实等价. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advancedM (p3_p4_inequiv)  *)
(** 证明下面的程序 _'不等价'_ . (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END.

Definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).


Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)  *)
(** Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if when given a same starting
    state [st], the set of possible terminating states is the same for
    both programs. If [p5] terminates, what should the final state be?
    Conversely, is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END.

Definition p6 : com :=
  X ::= ANum 1.


Theorem p5_p6_equiv : cequiv p5 p6.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * 附加题 *)

(** **** Exercise: 4 stars, optional (for_while_equiv)  *)
(** 这个练习是 Imp.v 中 可选练习[add_for_loop] 的扩展,
    就是那个让你扩展出类似C风格的for循环命令的练习.  证明命令:

      for (c1 ; b ; c2) {
          c3
      }

    等价于:

       c1 ; 
       WHILE b DO
         c3 ;
         c2
       END
*)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (swap_noninterfering_assignments)  *)
(** (Hint: 你也许需要 [functional_extensionality] 来完成此题.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)  *)
(** 这个练习里我们定义一个非对称的程序等价变形, 叫做
    _'程序近似'_ （ _program approximation_ ）。 当每个能让 [c1] 终止的初始状态
    也能让 [c2] 终止到相同的状态，我们就说程序 [c1] _'近似'_ 程序 [c2] 。
    下面形式化定义程序近似: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  c1 / st \\ st' -> c2 / st \\ st'.

(** 例如, 程序 [c1 = WHILE X <> 1 DO X ::= X - 1 END]
    近似 [c2 = X ::= 1], 但是 [c2] 不近似 [c1]
    因为 [c1] 在 [X = 0] 时死循环, 但是 [c2] 不会. 如果两个程序互相近似,
    那么他们等价. *)

(** 请找出互不近似的两个程序 [c3] 和 [c4]. 证明他们互不近似. *)

Definition c3 : com (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** 找到一个程序 [cmin] 近似所有别的程序。
    给出形式化的 [cmin_minimal] 证明。 *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** 最后，再找出程序近似的一个不太直观的属性 （当从左到右时）。
    给出形式化的 [zprop_preserving] 证明。 *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** $Date: 2017-03-05 13:25:50 -0800 (Sun, 05 Mar 2017) $ *)

