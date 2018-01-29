(** * VFA: Verified Functional Algorithms *)

(* ----------------------------------------------------------------- *)
(** *** by Andrew W. Appel *)
(* ----------------------------------------------------------------- *)
(** *** Warning! Beta release! *)

(** This textbook is in beta release.  Do not use this
   without permission from Andrew Appel. *)

(* ################################################################# *)
(** * 简介 *)

(** This electronic book is Volume 3 of the _Software Foundations_
    series, which presents the mathematical underpinnings of reliable software.

    In this volume you will learn how to specify and verify (prove the
    correctness of) sorting algorithms,  binary search trees, balanced
    binary search trees, and  priority queues.  Before using  this book,
    you should have some understanding of these algorithms and data
    structures, available in any standard undergraduate algorithms 
    textbook.

    You should understand all the material in
    Software Foundations Volume 1 (Logic Foundations), 
    but you will not need anything from Volume 2.
    The exposition here is intended for a broad range of readers, 
    from advanced undergraduates to PhD students and researchers. 

    The principal novelty of _Software Foundations_ is that it is one hundred
    percent formalized and machine-checked: the entire text is
    literally a script for Coq.  It is intended to be read alongside
    an interactive session with Coq.  All the details in the text are
    fully formalized in Coq, and the exercises are designed to be
    worked using Coq. *)

(* ################################################################# *)
(** * 实用指南 *)

(* ================================================================= *)
(** ** 章节依赖 *)

(** Before using _Verified Functional Algorithms_, read
    (and do the exercises in) these chapters of
    _Software Foundations Volume I_:
      Preface, Basics, Induction, Lists, Poly, Tactics, Logic,
      IndProp, Maps, and perhaps (ProofObjects), (IndPrinciples).

    In this volume, the core path is:

    [VFA] -> [Perm] -> [Sort] -> [SearchTree] -> [Redblack]

    with many optional chapters whose dependencies are,

    - [Sort] -> [Multiset] or [Selection] or [Decide]
    - [SearchTree] -> [ADT] or [Extraction]
    - [Perm] -> [Trie]
    - [Sort] -> [Selection] -> [SearchTree] -> [ADT] -> [Priqueue] -> [Binom]

    The [Color] chapter is advanced material that should not be
    attempted until the student has had experience with most
    of the earlier chapters, or other experience using Coq.
*)

(* ================================================================= *)
(** ** 系统需求 *)

(** Coq runs on Windows, Linux, and OS X.  The Preface of
    Volume 1 describes the Coq installation you will need.
    This edition was built with Coq 8.5pl2.

   In addition, two of the chapters ask you to compile and run
  an Ocaml program; having Ocaml installed on your computer is
  helpful, but not essential. *)

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

    Also, some exercises are marked "advanced", and some are marked
    "optional."  Doing just the non-optional, non-advanced exercises
    should provide good coverage of the core material.  Optional
    exercises provide a bit of extra practice with key concepts and
    introduce secondary themes that may be of interest to some
    readers.  Advanced exercises are for readers who want an extra
    challenge (and, in return, a deeper contact with the material).

    _Please do not post solutions to the exercises in any public place_: 
    Software Foundations is widely used both for self-study and for
    university courses.  Having solutions easily available makes it
    much less useful for courses, which typically have graded homework
    assignments.  The authors especially request that readers not post
    solutions to the exercises anyplace where they can be found by
    search engines.
*)

(* ================================================================= *)
(** ** 下载 Coq 文件 *)

(** A tar file containing the full sources for the "release version"
    of these notes (as a collection of Coq scripts and HTML files) is
    available here:

        http://www.cs.princeton.edu/~appel/vfa

    If you are using the notes as part of a class, your professor
    may give you access to a locally extended version of the files,
    which you should use instead of the release version.
*)

(* ================================================================= *)
(** ** For instructors and contributors *)

(** If you intend to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!

    To keep the legalities of the situation clean and to have a single
    point of responsibility in case the need should ever arise to
    adjust the license terms, sublicense, etc., we ask all
    contributors (i.e., everyone with access to the developers'
    repository) to assign copyright in their contributions to the
    appropriate "author of record," as follows:

        _I hereby assign copyright in my past and future contributions
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
        Benjamin Pierce._

    To get started, please send an email to Benjamin Pierce, describing
    yourself and how you plan to use the materials and including 
       (1) the above copyright transfer text and 
       (2) the result of doing "htpasswd -s -n NAME"
    where NAME is your preferred user name.

    We'll set you up with access to the subversion repository and 
    developers' mailing lists.  In the repository you'll find a 
    file [INSTRUCTORS] with further instructions. *)

