(** * 后记 *)

(** 恭喜：我们完成了！ *)

(* ################################################################# *)
(** * 回顾一下 *)

(** 我们已经覆盖了很多内容。下面是快速阅览...
   - _'函数式编程'_：
          - "声明式" 编程风格 (在不变的数据结构上递归，
            而非在可变的数组或指针结构上循环）
          - 高阶函数
          - 多态 *)

(**
     - _'逻辑'_, 软件工程的数学基础：

          逻辑               微积分
        --------   ~   -----------------
        软件工程       机械工程/土木工程

          - 递归定义的集合，关系
          - 归纳证明
          - 证明对象 *)

(**
     - _Coq_, 一个工业级的证明助理
          - 函数式核心语言
          - 核心策略
          - 自动化
*)

(**
     - _'编程语言基础'_
           - 记法和定义上的技巧，用于精确地描述
                - 抽象语法
                - 操作语义
                    - 大步风格
                    - 小步风格
                - 类型系统
           - 程序等价性
           - 霍尔逻辑
           - 类型系统的基础元理论
              - 可进性与维型性
           - 子类型理论
*)

(* ################################################################# *)
(** * 四处瞧瞧 *)

(** 这些核心主题的大规模应用可以在任何地方找到，无论是正在进行的研究项目，
    还是现实世界的软件系统。这里有几个最近的例子，涉及对真实世界的软件和
    硬件系统形式化的，机器检查的验证，让你对当今正的发展有直观的认识...
    无论是进行中的研究项目，还是用于现实世界的软件系统，在它们之中都能看到
    这些核心主题的大规模应用。为了让你对相关内容的应用及其发展有某种程度上的认识，
    下面介绍一些新近的软件和硬件系统；它们的设计中均使用了形式化的、机器检查的证明，
    而且已经在现实世界中得到应用了。 *)

(* ----------------------------------------------------------------- *)
(** *** CompCert *)
(** _CompCert_ 是一个完全验证过的，带优化的 C 编译器，它支持几乎整个 ISO C90/ANSI C
    标准。它能生成 x86、ARM 和 PowerPC 处理器的代码。CompCert 完全由 Gallina 写成，
    并通过 Coq 的提取机制转换成高效的 OCaml 程序。
    “CompCert 项目考察了可用于关键嵌入式软件的现实编译器的形式化验证。
    这种经过验证的编译器具有数学上的，机器检查过的证明，它所生成的
    可执行代码的行为与源程序的语义完全相同。通过排除编译器引入 Bug
    的可能，经过验证的编译器加强了对源程序应用形式化方法所能得到的保证。”
    2011 年，CompCert 被包含了一个使用 CSmith 工具对大量现实世界的
    C 编译器进行模糊测试的划时代研究中。CSmith 的作者写道：
(* TODO(osc): wrong code error 需要到 csmith 上查看含义 *)
      - 引人注目的的是，我们在其它编译器中找到的中端缺陷在 CompCert
        的结果中并不存在。截至 2011 年初，CompCert 的开发版是我们测试过的
        唯一一个 CSmith 无法找到错误代码造成错误的编译器。
        这并不是因为我们做的测试还不够多：我们已经在这个任务上花了六个CPU年。
        CompCert 明显的牢不可破性强有力地证明了使用明确的，经过机器验证安全性检查的
        证明框架来开发编译器优化，对编译器用户具有切实的好处。
    http://compcert.inria.fr *)

(* ----------------------------------------------------------------- *)
(** *** seL4 *)
(** _seL4_ 是一个完全验证过的微内核，它被认为是世界上第一个通过了
    实现正确性和强制安全性的端到端证明的 OS 内核。它以 C 和 ARM 汇编实现，
    并使用 Isabelle 进行了规范化和验证。其代码是开源的。
    「seL4 已经得到了全面的形式化验证：一个数学上严格的过程证明了
    其可执行代码在硬件上运行时正确地实现了（而且只会有）规范所描述的行为。
    此外，我们还证明了该规范拥有期望的安全性和安全属性（完整性和保密性）...
    该验证的实现成本比传统的高可靠性开发方式明显更低，同时还提供了传统方法
    无法提供的保证。」
    https://sel4.systems. *)

(* ----------------------------------------------------------------- *)
(** *** CertiKOS *)
(** _CertiKOS_ 是一个干净的，完全验证过的虚拟机管理器，以 CompCert C
    编写，并通过 Coq 验证。
    「CertiKOS 项目致力于开发一个新颖实用的，用于构建大规模认证系统软件
    的编程基础设施。通过结合编程语言，操作系统和形式化方法的最新进展，
    我们希望攻克以下研究问题：(1) 何种 OS 内核结构能够对可扩展性，
    安全性和弹性提供最佳支持? (2) 哪种语义模型和程序逻辑能为它们提供
    最佳抽象？ (3) 什么编程语言和环境最适合开发这种认证的内核？
    (4) 如何建立自动化设施，使认证软件的开发真正具有规模？」
    http://flint.cs.yale.edu/certikos/ *)

(* ----------------------------------------------------------------- *)
(** *** Ironclad *)
(** _Ironclad 应用集_是一组完全验证过的 Web 应用，包括一个安全地签署声明的
    「公证人」，一个密码散列器，一个多用户信任的计数器，和一个差异私有化的
    数据库。
    这套系统以面向验证的编程语言 Dafny 编写，并使用基于霍尔逻辑的
    Boogie 验证工具验证。
    「Ironclad 应用能够让用户安全地将其数据传输到远程机器，
    并保证该机器上执行的每个指令都遵循该应用所应有行为的形式化的、抽象的规范。
    这不仅消除了如缓冲区溢出，解析错误或数据泄漏之类的实现缺陷，
    它还会告诉用户应用在任何时候所应具有的行为。我们通过完整的底层软件验证提供这些保障，
    而在这之后，我们会通过加密和安全硬件来实现从已验证的软件到远程用户之间的安全通道。」
    https://github.com/Microsoft/Ironclad/tree/master/ironclad-apps *)

(* ----------------------------------------------------------------- *)
(** *** Verdi *)
(** _Verdi_ 是一个用于实现并形式化验证分布式系统的框架。
    「Verdi 支持从概念到现实的几种不同的故障模型。Verdi 的已验证的系统变换器
    （verified system transformers）包含一些通用的容错技巧。
    开发者可在理想化的故障模型中验证应用，
    然后对其应用 VST 来得到一个保证能在更具对抗性的环境中拥有类似性质的应用。
    Verdi 使用 Coq 证明助理开发，而这些验证的系统提取为 OCaml 用于执行。Verdi 系统
    包含了带容错的键值存储，以获得与相对应的未经验证的版本相当的性能。」
    http://verdi.uwplse.org *)

(* ----------------------------------------------------------------- *)
(** *** DeepSpec *)
(** _'深度规范科学（The Science of Deep Specification）'_ 是 NSF 的一个「远征」项目
    （从2016年到2020年），它专注于软件和硬件的完整功能的正确性的规范和验证。
    它也赞助了一些研讨会和暑期班。
      - 网站：http://deepspec.org/
      - 概览展示：
          - http://deepspec.org/about/
          - https://www.youtube.com/watch?v=IPNdsnRWBkk *)

(* ----------------------------------------------------------------- *)
(** *** REMS *)
(** _REMS_ 是一个来自欧洲的有关主流系统严格化工程（Rigorous Engineering of Mainstream Systems）
    的项目。它已经为一系列被用于现实世界中的关键的接口、协议和 API 提供了包含了许多细节的形式化规范
    这些应用包括：
      C 语言，
      ELF 链接器格式，
      ARM、Power、MIPS、CHERI 和 RISC-V 指令集，
      ARM 和 Power 处理器的弱内存模型，以及
      POSIX 文件系统。
    「该项目专注于轻量级严格化方法：（设计过程和之后的）精确规范和针对测试的规范，
    仅在某些情况下进行完全验证。该项目强调建立有用（且可重用）的语义和工具。
    我们正为一些关键的计算抽象（处理器架构、编程语言、并发操作系统接口、以及网络协议）
    建立准确而全面的数学模型，同时我们也在研究如何做到这一点，并探讨如何将这些模型应用到
    新的验证研究，以及新系统和编程语言的研究中。为了支持这一切，我们也在开发新的规范工具及其基础。」
    http://www.cl.cam.ac.uk/~pes20/rems/ *)

(* ----------------------------------------------------------------- *)
(** *** 其它 *)

(** 还有更多。其它值得一看的项目包括：
      - Vellvm（LLVM 优化 pass 的形式化标准和验证）
      - Zach Tatlock 的形式化验证的浏览器
      - Tobias Nipkow 的经过形式化验证的 Java 子集
      - CakeML 一个经过验证的 ML 编译器
      - Greg Morrisett 的形式化 x86 指令集规范以及 RockSalt 软件缺陷隔离工具
        （一个更好，更快，更安全的 Google Native Client）
      - Ur/Web，一个嵌入在 Coq 中的，经过验证的 web 应用编程语言
      - Princeton 验证软件工具链
*)

(* ################################################################# *)
(** * 继续前行 *)

(** 对欲求不满的人．．．
       - 本书中一些可选章节覆盖的主题可能对你有用。你可以从
         内容列表 以及
         章节依赖图 中找到它们。
       - 编程语言及形式化验证的顶级会议：
            - Principles of Programming Langauges (POPL)
            - Programming Language Design and Implementation (PLDI)
            - SPLASH/OOPSLA
            - International Conference on Functional
              Programming (ICFP)
            - Computer Aided Verification (CAV)
            - Interactive Theorem Proving (ITP)
            - Principles in Practice workshop (PiP)
            - CoqPL workshop
       - 更多与函数式编程相关的内容：
            - Learn You a Haskell for Great Good, by Miran Lipovaca
              [Lipovaca 2011].
            - Real World Haskell, by Bryan O'Sullivan, John Goerzen,
              and Don Stewart [O'Sullivan 2008]
            - ...以及 Haskell、OCaml、Scheme、Racket、Scala、F sharp
              等其它优秀的书籍。
       - 更多与霍尔逻辑和程序验证相关的内容：
            - The Formal Semantics of Programming Languages: An
              Introduction, by Glynn Winskel [Winskel 1993].
            - 许多实用的验证工具如微软的 Boogie system，
              Java Extended Static Checking 等。
       - 更多编程语言基础：
            - Concrete Semantics with Isabelle/HOL, by Tobias Nipkow
              and Gerwin Klein [Nipkow 2014]
            - Types and Programming Languages, by Benjamin C. Pierce
              [Pierce 2002].
            - Practical Foundations for Programming Languages, by
              Robert Harper [Harper 2016].
            - Foundations for Programming Languages, by John
              C. Mitchell [Mitchell 1996].
       - 更多 Coq 相关:
           - Verified Functional Algorithms, by Andrew Appel
             [Chlipala 2013].
           - Certified Programming with Dependent Types, by Adam
             Chlipala [Chlipala 2013].
           - 交互式定理证明与程序开发：
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran [Bertot 2004].
           - Iron Lambda (http://iron.ouroborus.net/) 是一个关于函数式编程形式化的集合，
             它包含将多种函数式语言（它们的复杂性逐步增加）形式化的 Coq 代码。
             它填补了本课程与最新研究论文所涵盖内容之间的缝隙。
             该集合包含多种有关 STLC 与多态 λ-演算（即 System F）相关性质
             （至少包含其可进性与维型性）的证明。 *)

(* $Date: 2017-03-05 13:25:50 -0800 (Sun, 05 Mar 2017) $ *)
