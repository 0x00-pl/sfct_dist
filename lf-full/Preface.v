(** * Preface *)

(* ################################################################# *)
(** * 简介 *)

(** This electronic book is a course on _Software Foundations_, the
    mathematical underpinnings of reliable software.  Topics include
    basic concepts of logic, computer-assisted theorem proving, the
    Coq proof assistant, functional programming, operational
    semantics, Hoare logic, and static type systems.  The exposition
    is intended for a broad range of readers, from advanced
    undergraduates to PhD students and researchers.  No specific
    background in logic or programming languages is assumed, though a
    degree of mathematical maturity will be helpful.

    The principal novelty of the course is that it is one hundred
    percent formalized and machine-checked: the entire text is
    literally a script for Coq.  It is intended to be read
    alongside (or inside) an interactive session with Coq.  All the
    details in the text are fully formalized in Coq, and most of the
    exercises are designed to be worked using Coq.

    The files are organized into a sequence of core chapters, covering
    about one semester's worth of material and organized into a
    coherent linear narrative, plus a number of "offshoot" chapters
    covering additional topics.  All the core chapters are suitable
    for both upper-level undergraduate and graduate students. *)


(* ################################################################# *)
(** * 导论 *)

(** Building reliable software is hard.  The scale and complexity of
    modern systems, the number of people involved in building them,
    and the range of demands placed on them make it extremely
    difficult to build software that is even more-or-less correct,
    much less 100%% correct.  At the same time, the increasing degree
    to which information processing is woven into every aspect of
    society greatly amplifies the cost of bugs and insecurities.

    Computer scientists and software engineers have responded to these
    challenges by developing a whole host of techniques for improving
    software reliability, ranging from recommendations about managing
    software projects teams (e.g., extreme programming) to design
    philosophies for libraries (e.g., model-view-controller,
    publish-subscribe, etc.) and programming languages (e.g.,
    object-oriented programming, aspect-oriented programming,
    functional programming, ...) to mathematical techniques for
    specifying and reasoning about properties of software and tools
    for helping validate these properties.  The present course is
    focused on this last set of techniques.

    The text weaves together five conceptual threads:

    (1) basic tools from _logic_ for making and justifying precise
        claims about programs;

    (2) the use of _proof assistants_ to construct rigorous logical
        arguments;

    (3) _functional programming_, both as a method of programming that
        simplifies reasoning about programs and as a bridge between
        programming and logic;

    (4) formal techniques for _reasoning about the properties of
        specific programs_ (e.g., the fact that a sorting function or
        a compiler obeys some formal specification); and

    (5) the use of _type systems_ for establishing well-behavedness
        guarantees for _all_ programs in a given programming
        language (e.g., the fact that well-typed Java programs cannot
        be subverted at runtime).

    Each of these is easily rich enough to fill a whole course in its
    own right, and tackling all of them together naturally means that
    much will be left unsaid.  Nevertheless, we hope readers will find
    that these themes illuminate and amplify each other and that
    bringing them together creates a good foundation for digging into
    any of them more deeply.  Some suggestions for further reading can
    be found in the [Postscript] chapter.  Bibliographic
    information for all cited works can be found in the file
    [Bib]. *)

(* ================================================================= *)
(** ** Logic *)

(** Logic is the field of study whose subject matter is _proofs_ --
    unassailable arguments for the truth of particular propositions.
    Volumes have been written about the central role of logic in
    computer science.  Manna and Waldinger called it "the calculus of
    computer science," while Halpern et al.'s paper _On the Unusual
    Effectiveness of Logic in Computer Science_ catalogs scores of
    ways in which logic offers critical tools and insights.  Indeed,
    they observe that, "As a matter of fact, logic has turned out to
    be significiantly more effective in computer science than it has
    been in mathematics.  This is quite remarkable, especially since
    much of the impetus for the development of logic during the past
    one hundred years came from mathematics."

    In particular, the fundamental tools of _inductive proof_ are
    ubiquitous in all of computer science.  You have surely seen them
    before, perhaps in a course on discrete math or analysis of
    algorithms, but in this course we will examine them much more
    deeply than you have probably done so far. *)

(* ================================================================= *)
(** ** 证明助理 *)

(** 逻辑学与计算机科学之间的思想交流并不是单方面的：
    计算机科学也对逻辑学做出了重要的贡献，
    其中之一就是发展了可帮助构造命题/证明的软件工具。
    这些工具分为两类：
       - _'自动化定理证明器'_ 提供了一键式操作：它们接受一个命题，
         然后返回 _'真'_ 或 _'假'_ (或有时为 _'未知：超时'_ )。
         尽管它们的能力仅限于特定种类的推理中，但在近几年却大幅成熟并应用于多种场合，
         自动化定理证明器的例子包括 SAT 求解器，SMT 求解器以及模型检查器（Model Checker）。
       - _'证明助理'_  是一种混合式工具，它能将构建证明中比较常规的部分自动化，
         而更困难的部分则依赖于人类解决。常用的证明助理包括
         Isabelle、Agda、Twelf、ACL2、PVS 以及 Coq，还有很多其它的。
    本课程围绕 Coq 展开。它是一个自 1983 年以来主要在法国开发的证明助理，
    近年来吸引了大量来自研究机构和业界的社区用户。
    Coq 为机器验证的形式化论证的交互式开发提供了丰富的环境。Coq 系统的内核是一个简单的证明验证器，
    它保证只会进行正确的推论步骤。在此内核之上，Coq 环境提供了高级的证明开发设施，
    包括一个包含各种定义和引理的庞大的库，用于半自动化构造证明的强大策略，
    以及一个专门为特殊情况定义新的自动证明策略的专用编程语言。
    Coq 已成为各种跨计算机科学和数学研究的关键推动者：
    - 作为一个 _'编程语言的建模平台'_ ，
      Coq 成为了研究员对复杂语言定义进行描述和论证的一个标准工具。
      例如，它被用来检查 JavaCard 平台的安全性，得到了最高等级的通用准则验证，
      它还被用在 x86 和 LLVM 指令集以及 C 之类的编程语言的形式化规范中。
    - 作为一个 _'形式化验证软件的开发环境'_ ，Coq 被用来构建：
      CompCert，一个完全验证过的 C 优化编译器；
      CertiKos，一个完全验证过的，用于证明浮点数相关精妙算法的正确性；
      Coq 也是 CertiCrypt，一个用于论证密码学算法安全性的环境的基础。
      它也被用来构建开源 RISC-V 处理器的已验证实现。
    - 作为一个 _'带依赖类型的函数式编程的现实环境'_ ，Coq 激发了大量的创新。
      例如 Ynot 系统嵌入了「关系式霍尔推理」（一个 _'霍尔逻辑'_ 的扩展，我们会在后面看到它）。
    - 作为一个 _'高阶逻辑的证明助理'_ ，Coq 被用于证实数学中一些重要的结果。
      例如 Coq 可在证明中包含复杂计算的能力，使其开发出第一个形式化验证的四色定理证明。
      此前数学家们对该证明颇有争议，因为其中一部分用程序对大量组态进行了检查。
      在 Coq 的形式化中，所有东西都被检查了，自然包括计算方面的正确性。
      近年来，Feit-Thompson 定理在更大的努力下用 Coq 形式化了，
      这是对有限单群进行分类的第一大步。
   顺便一提，如果你对 Coq 这个名字感到好奇，INRIA (法国国家研究实验室，Coq
   主要在这里开发）上的 Coq 官方网站给出了解释：
   「一些法国计算机科学家有用动物命名软件的传统：像 Caml、Elan、Foc、Phox
   都心照不宣地遵循这种默契。在法国，「Coq」是雄鸡，发音也像
   Calculus of Constructions 的首字母缩写（CoC），后者是 Coq 的基础。」
   高卢雄鸡是法国的象征。C-o-q 还是 Thierry Coquand 名字的前三个字母，
   他是 Coq 的早期开发者之一。 *)

(* ================================================================= *)
(** ** 函数式编程 *)

(** _'函数式编程'_ 既代表几乎可以在任何编程语言中使用的一系列惯用法，也代表着一族
    以这些习惯用法为侧重点设计的编程语言，包括 Haskell、OCaml、Standard ML、F##、
    Scala、Scheme、Racket、Common Lisp、Erlang 还有 Coq。
    函数式编程已经有数十年历史了--实际上，它甚至可以追溯到 1930
    年代 Church 发明的 λ-演算，那时候还没有计算机呢！自 90 年代初以来，
    函数式编程激起了业内软件工程师和语言设计者浓厚的兴趣，它还在
    Jane St. Capital、Microsoft、Facebook 和 Ericsson
    等公司的高价值系统中发挥着关键的作用。
    函数式编程最根本的原则是，计算应当尽可能地 _'纯粹'_ ，也就是说，
    执行代码的唯一效果应当是只产生一个结果：计算应当没有 _'副作用'_ ，
    即与输入/输出、可变量的赋值、指针重定向等等脱离。
    例如，一个命令式的排序函数会接受一个数字列表，通过重组指针使列表得以排序；
    而一个纯粹的排序函数则会取一个列表，返回一个含有同样数字，但是已排序的新列表。
    这种编程风格最明显的好处之一，就是它能让程序变得更容易理解和论证。
    如果对某个数据结构的所有操作都会返回新的数据结构，而旧有的结构没有变动，
    那么我们便无需担心它的共享方式，因为程序中一部分的改变并不会破坏另一部分的属性。
    在并发程序中，线程间共享的每一个可变状态都是致命 Bug 的潜在来源，
    因此这方面的考虑尤为关键。事实上，业界最近对函数式编程的兴趣大部分来源于此，
    即它在并发中表现出的简单行为。
    人们对函数式编程感到兴奋的另一原因与前文所述的原因相关：
    函数式程序通常比命令式程序更容易并行化。
    如果一个计算除了产生结果之外没有其它的作用，那么它在 _'何时'_ 执行便不再重要。
    同样，如果一个数据结构不会被破坏性地修改，那么它可以跨核心或网络地被随意复制。
    其实，「映射-归纳」（Map-Reduce）的惯用法就是函数式编程的经典例子，
    它在大规模分布式查询处理器（如 Hadoop）中处于核心地位，并被 Google
    用来索引整个互联网。
    对于本课程而言，函数式编程还有另一个重要的吸引力：
    它在逻辑与计算机科学之间架起了一座桥梁。事实上，Coq
    本身即可视作一个小巧却有着极强表达能力的函数式编程语言，
    以及一组用于陈述和证明逻辑断言的工具的结合体。进而言之，
    当我们更加深入地审视它时，会发现 Coq 的这两方面其实基于几乎相同的底层机制
    -- _'命题即类型，程序即证明'_ ，可谓殊途同归。 *)

(* ================================================================= *)
(** ** 程序验证 *)

(** 本书的前三分之一用于发展逻辑学以及函数式编程的概念框架，提升用
    Coq 对非平凡构造进行建模和论证的熟练度。此后，我们会逐渐将重点转移到
    对构建可靠软件（和硬件）的事业而言至关重要的两个主题上：
    用于证明特定 _'程序'_ 具体属性的技巧，以及用于证明整个编程 _'语言'_ 共通属性的技术。
    对于这两个主题来说，我们首先要找出一种用将程序表示为数学对象的方法，
    以此来对二者进行精确的描述，以及用函数或关系表示它们的行为。
    对此而言，我们的工具是抽象语法（Abstract Syntax）和操作语义（Operational
    Semantics），一种通过编写抽象解释器来指定程序行为的方法。
    首先，我们尽量用「大跨步」的方式来产生更加简单可读的操作语义；
    之后，我们会转换到更加详细的「小碎步」风格，这样能有效地区分不同种类的「非最终」
    程序的行为，这种方式适用于更加广泛的语言特性，包括并发。
    我们要仔细考虑的第一个编程语言是 _Imp_ ，一个小巧的玩具编程语言，
    它包含了传统命令式编程的核心特性：变量、赋值、条件和循环。
    我们会学习两种不同的方法来对 Imp 程序的属性进行论证。
    首先，若两个 Imp 程序在任何初始内存状态下启动都有相同的行为，
    那么我们便认为二者是 _'等价的'_ 。这种等价的概念便成为了判定元程序
    （操控其它程序的程序，比如编译器和优化器）正确性的标准。
    我们会为 Imp 构建一个简单的优化器并证明其正确性。
    之后，我们会发展出一套方法论，用于证明特定 Imp 程序的行为是否满足其形式化规范。
    我们会介绍 _'霍尔三元组'_ （Hoare triples）的概念：带有前置和后置条件的 Imp
    程序描述了在它启动时，内存中的什么应该为真；在它终止后，它保证内存中的什么为真。
    也会介绍 _'霍尔逻辑'_ （Hoare Logic）的推理原则：一种内建了循环不变式（loop-invariant）
    等概念的「领域专用逻辑」，以便对命令式程序进行组合推理。
    本课程的这一部分意在让读者尝试各种现实中软件和硬件的证明工作，
    以此来获得所需要的关键思想和数学工具。*)

(* ================================================================= *)
(** ** 类型系统 *)

(** 我们的最后一个主题为 _'类型系统'_ ，它覆盖了课程最后的三分之一。
    它是一组强大的工具，用于构建给定语言中 _'所有'_ 程序的属性。
    类型系统是最久经考验、最流行也是最成功的一类形式化验证技术的例子，
    它被称作 _'轻量级形式化方法'_ （lightweight formal methods）。
    它们是低调而强大的论证技术，以至于自动检查器可以内建在在编译器、
    连接器或程序分析器中，而程序员无需熟悉底层理论便可应用。
    其它轻量级形式化方法的例子包括硬件和软件的模型检查器、契约检查器，
    以及运行时属性监视技术，它用来检测一个系统中某些组件的行为是否遵循规范）。
    该主题使得本课程终归圆满：我们在这一部分研究的语言，即 _'简单类型化 λ-演算'_ ，
    它本质上就是 Coq 核心自身的一个简化模型！
*)

(* ================================================================= *)
(** ** 扩展阅读 *)

(** 此书旨在自成一体，不过想要对特定主题进行深入研究的读者，可以在 [Postscript]
    一章中找到建议的扩展阅读。 *)

(* ################################################################# *)
(** * 实用指南 *)

(* ================================================================= *)
(** ** 章节依赖 *)

(** 章节之间的依赖关系以及一些建议的路径图可以在文件
    [deps.html] 中找到。 *)

(* ================================================================= *)
(** ** 系统需求 *)

(** Coq 可以在 Windows、Linux 和 OS X 上运行。你需要：
       - 一个最近的 Coq 安装，可以从 Coq 主页获得。所有内容都能在 8.4（或 8.5）上运行。
       - 一个能跟 Coq 交互的 IDE。目前为止有两个选项：
           - Proof General 是一个基于 Emacs 的 IDE，Emacs 用户应该更喜欢这个。
             它需要另外安装（Google 搜索「Proof General」）。
             爱作死的 Emacs 党也可以试试 [company-coq] 和 [control-lock]
             之类的扩展。
           - CoqIDE 是一个更简单的独立 IDE。它随 Coq 一起发布，所以若你已经安装了
             Coq，它应该「刚好能用」。它也可以通过对应的依赖从头编译安装，
             不过在某些平台上还需要额外安装 GUI 库之类的东西。 *)

(* ================================================================= *)
(** ** 练习 *)

(** Each chapter includes numerous exercises.  Each is marked with a
    "star rating," which can be interpreted as follows:

       - One star: easy exercises that underscore points in the text
         and that, for most readers, should take only a minute or two.
         Get in the habit of working these as you reach them.

       - Two stars: straightforward exercises (five or ten minutes).

       - Three stars: exercises requiring a bit of thought (ten
         minutes to half an hour).

       - Four and five stars: more difficult exercises (half an hour
         and up).

    Also, some exercises are marked "advanced," and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge and a deeper cut at the material.

    _Please do not post solutions to the exercises in a public place_. 
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  We especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)

(* ================================================================= *)
(** ** 下载 Coq 文件 *)

(** 一个包含本书「发布版」的所有源代码的 tar 包
    （包含一组 Coq 脚本和 HTML 文件）可在此获得：

        http://www.cis.upenn.edu/~bcpierce/sf

    本书的中文版可在此获得：

        https://github.com/MarisaKirisame/SFCT

    （如果你是在一门课程中使用本书的，那么你的教授可能让你访问本地的修改版，
    此时你应当使用它们而非发布版。）*)

(* ################################################################# *)
(** * 对授课员的标准 *)

(** 如果你有意用这些课件授课，那肯定会发现希望改进或增加的东西。我们欢迎你的贡献！
    为保证法律上的简单性和单一责任制，任何情况下都不应出现许可条款的的调整，
    授权的转移等等，我们要求所有贡献者（即，任何可访问开发者仓库的人）根据
    「作者记录」为他们的贡献赋予版权信息如下：
      - I hereby assign copyright in my past and future contributions
        to the Software Foundations project to the Author of Record of
        each volume or component, to be licensed under the same terms
        as the rest of Software Foundations.  I understand that, at
        present, the Authors of Record are as follows: For Volumes 1
        and 2, known until 2016 as "Software Foundations" and from
        2016 as (respectively) "Logical Foundations" and "Programming
        Foundations," the Author of Record is Benjamin Pierce.  For
        Volume 3, "Verified Functional Algorithms", the Author of
        Record is Andrew W. Appel. For components outside of
        designated Volumes (e.g., typesetting and grading tools and
        other software infrastructure), the Author of Record is
        Benjamin Pierce.
    请您向 Benjamin Pierce 发一封电子邮件，描述一下你自己，
    以及你打算如何使用这些课件，内容包括
       (1) 以上版权转让协议，以及
       (2) 执行 "htpasswd -s -n NAME" 后产生的结果，
    其中 NAME 是你喜欢的用户名。
    我们为你设置 subversion 仓库和开发者邮件列表的访问权限。
    在仓库中你会找到一个包含更多指引的 [INSTRUCTORS] 文件。*)

(* ################################################################# *)
(** * 翻译版 *)

(** 感谢翻译志愿者团队的努力，_'Software Foundations'_
    有了可以阅读的日文版
    [http://proofcafe.org/sf]。
    中文版还在填坑= =||
*)

(** $Date: 2017-03-05 13:25:50 -0800 (Sun, 05 Mar 2017) $ *)
