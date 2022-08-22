# 3-lisp: an infinite tower of meta-circular interpreters.

<a href="https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L259"><img src="https://nikitadanilov.github.io/3-lisp/epigraph.png"/></a>

## Précis
3-lisp is a dialect of Lisp designed and implemented by [Brian C. Smith](https://en.wikipedia.org/wiki/Brian_Cantwell_Smith)
as part of his PhD. thesis [Procedural Reflection in Programming Languages](https://dspace.mit.edu/handle/1721.1/15961) (what this thesis refers to as "[reflection](https://en.wikipedia.org/wiki/Reflective_programming)" 
is nowadays more usually called "[reification](https://en.wikipedia.org/wiki/Reification_(computer_science))"). 3-lisp program is conceptually executed by an interpreter written in 3-lisp that is itself executed by an interpreter written in 3-lisp and so on *ad infinitum*. This forms a (countably) infinite tower of meta-circular (*v.i.*) interpreters. *reflective lambda* is a function that is executed one tower level above its caller. Reflective lambdas provide a very general language extension mechanism.

## Meta-circular interpreters
An [interpreter](https://en.wikipedia.org/wiki/Interpreter_(computing)) is a
program that executes programs written in some programming language.

A [meta-circular interpreter](https://en.wikipedia.org/wiki/Meta-circular_evaluator) is an interpreter for a programming language written in that language. Meta-circular interpreters can be used to clarify or define semantics of the language by reducing the full language to a sub-language in which the interpreter is expressed.  Historically, such *definitional interpreters* become popular within the functional programming community, see the classical [Definitional interpreters for higher-order programming languages](https://surface.syr.edu/cgi/viewcontent.cgi?article=1012&context=lcsmith_other). Certain important techniques were classified and studied in the framework of meta-circular interpretation, for example, [continuaiton passing style](https://en.wikipedia.org/wiki/Continuation-passing_style) can be understood as a mechanism that makes meta-circular interpretation independent of the [evaluation strategy](https://en.wikipedia.org/wiki/Evaluation_strategy): it allows an eager meta-lanaguge to interpret a lazy object language and *vice versa*. As a by-product, a continuation passing style interpreter is essentially a state machine and so can be inplemented in hardware, see [The Scheme-79 chip](https://dspace.mit.edu/handle/1721.1/6334). Similarly, *[de-functionalisation](https://www.brics.dk/RS/08/4/BRICS-RS-08-4.pdf)* of languages with higher-order functions, obtains for them first-order interpreters. But meta-circular interpreters occur in imperative contexts too, for example, the usual proof of the [Böhm–Jacopini theorem](https://en.wikipedia.org/wiki/Structured_program_theorem) (interestingly, it was [Corrado Böhm](https://en.wikipedia.org/wiki/Corrado_B%C3%B6hm) who first introduced meta-circular interpreters in his 1954 PhD. thesis) constructs for an Algol-like language a meta-circular interpreter expressed in some goto-less subset of the language and then [specialises](https://en.wikipedia.org/wiki/Partial_evaluation) this interpreter for a particular program in the source language.

Given a language with a meta-circular interpreter, suppose that the language is extended with a mechanism to *trap* to the meta-level. For example, in a lisp-like language, that trap can be a new special form `(reflect FORM)` that directly executes (rather than interprets) `FORM` within the interpreter. Smith is mostly interested in reflective (*i.e.*, reification) powers obtained this way, and it is clear that meta-level trap provides a very general lanaguage extension method: one can add new primitives, data types, flow and sequencing control operators, *etc*. But if you try to add `reflect` to an existing LISP meta-circular interpreter (for example, see p. 13 of [LISP 1.5 Programmers Manual](https://www.softwarepreservation.org/projects/LISP/book/LISP%201.5%20Programmers%20Manual.pdf)) you'd hit a problem: `FORM` cannot be executed at the meta-level, because at this level it is not a form, but an [S-expression](https://en.wikipedia.org/wiki/S-expression).

## Meta-interpreting machine code
To understand the nature of the problem, consider a very simple case: the object lanaguage is the machine language (or equivalently the assembly language) of some processor. Suppose that the interpreter for the machine code is written in (or, more realistically, compiled to) the same machine language. The interpreter maintains the state of the simulated processor that is, among other things registers and memory. Say, the object (interpreted) code can access a register, `R0`, then the interpreter has to keep the contents of this register somewhere, but typically not in *its* (interpreter's) `R0`. Similarly, a memory word visible to the interpreted code at an address `ADDR` is stored by the interpreter at some, generally different, address `ADDR'` (although, by applying the [contractive mapping theorem](https://en.wikipedia.org/wiki/Banach_fixed-point_theorem) and a *lot* of hand-waving one might argue that there will be at least one word stored at the same address at the object- and meta-levels). Suppose that the interpreted machine lanaguage has the usual sub-routine call-return instructions `call ADDR` and `return` and is extended with a new instruction `reflect ADDR` that forces the interpreter to call the sub-routine `ADDR`. At the very least the interpreter needs to convert `ADDR` to the matching `ADDR'`. This might not be enough because, for example, the object-level sub-routine `ADDR` might not be contiguous at the meta-level, *i.e.*, it is not guaranteed that if `ADDR` maps to `ADDR'` then `(ADDR + 1)` maps `(ADDR' + 1)`. This example demonstrates that a reflective interpreter needs a systematic and efficient way of converting or translating between object- and meta-level representations. If such method is somehow provided, `reflect` is a very powerful mechanism: by modifying interpreter state and code it can add new instructions, addressing modes, condition bits, branch predictors, *etc*.

## N-LISP for a suitable value of N
In his thesis Prof. Smith analyses what would it take to construct a dialect of LISP for which a faithful reflective meta-circular interpreter is possible. He starts by defining a formal model of computation with an (extremely) rigorous distinction between meta- and object- levels (and, hence, between [use and mention](https://en.wikipedia.org/wiki/Use%E2%80%93mention_distinction)). It is then determined that this model can not be satisfactory applied to the *traditional* LISP (which is called `1-LISP` in the thesis and is mostly based on [Maclisp](https://en.wikipedia.org/wiki/Maclisp)). The reason is that LISP's notion of [evaluation](https://en.wikipedia.org/wiki/Eval#Lisp) conflates two operations: [normalisation](https://en.wikipedia.org/wiki/Normal_form_(abstract_rewriting)) that operates within the level and [reference](https://en.wikipedia.org/wiki/Referent) that moves one level down. A dialect of LISP that consistently separates normalisation and reference is called `2-LISP` (the then new [Scheme](https://en.wikipedia.org/wiki/Scheme_(programming_language)) is called `LISP-1.75`). Definition of `2-LISP` occupies the bulk of the thesis, which the curious reader should consult for (exciting, believe me) details.

Once `2-LISP` is constructed, adding reflective capability to it is relatively straightforward. Meta-level trap takes form of a special [lambda expression](https://en.wikipedia.org/wiki/Anonymous_function#Lisp):

	(lambda reflect [ARGS ENV CONT] BODY)

When this lambda function is applied (at the object level), the body is directly executed (not interpreted) at the meta-level with `ARGS` bound to the meta-level representation of the actual paremeters, `ENV` bound to the *environment* (basicaly, the list of identifiers and the values they are bound to) and `CONT` bound to the [continuation](https://en.wikipedia.org/wiki/Continuation). Environment and continuation together represent the `3-LISP` interpreter state (much like registers and memory represent the machine language interpreter state), this representation goes all the way back to [SECD machine](https://en.wikipedia.org/wiki/SECD_machine), see [The Mechanical Evaluation of Expressions](https://doi.org/10.1093%2Fcomjnl%2F6.4.308).

Here is the fragment of `3-LISP` meta-circular interpreter code that handles `lambda reflect` (together with "ordinary" lambda-s, denoted by `lambda simple`):

<a href="https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L1570"><img src="https://nikitadanilov.github.io/3-lisp/reduce.png"/></a>

## Implementation
It is of course not possible to run an infinite tower of interpreters directly.

<img src="https://nikitadanilov.github.io/3-lisp/infinity.png"/>

`3-LISP` implementation creates a meta-level on demand, when a reflective lambda is invoked. At that moment the state of the meta-level interpreter is synthesised (*e.g.*, [see](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L1586) `make-c1` in the listing above). The implementation takes pain to detect when it can drop down to a lower level, which is not entirely simple because a reflective lambda can, instead of returning (that is, invoking the supplied continuation), run a potentually modified version of read-eval-loop (called `READ-NORMALISE-PRINT` ([see](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L1563)) in `3-LISP`) which does not return. There is a lot on non-trivial machinery operating behind the scenes and though the implementation modestly proclaims itself [EXTREMELY INEFFICIENT](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L33) it is, in fact, remarkably fast.

## Porting
I was unable to find a digital copy of the `3-LISP` sources and so manually retyped the sources from the appendix of the thesis. The transcription in [3-lisp.lisp](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp) (2003 lines, 200K characters) preserves the original pagination and character set, see the comments at the top of the file. Transcription was mostly straight-forward except for a few places where the PDF is illegible (for example, [here](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.lisp#L396)) all of which fortunately are within comment blocks.

The sources are in [CADR machine](https://dspace.mit.edu/handle/1721.1/5718) dialect of LISP, which, save for some minimal and no longer relevant details, is equivalent to Maclisp.

`3-LISP` implementation does not have its own parser or interpreter. Instead it uses flexibility built in a lisp reader (see, [readtables](https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node192.html)) to parse, interpret and even compile `3-LISP` with a very small amount of additional code. Amazingly, this more than 40 years old code, which uses arcane features like readtable customisation, runs on a modern [Common Lisp](https://en.wikipedia.org/wiki/Common_Lisp) platform after a very small set of changes: some functions got renamed (`CASEQ` to `CASE`, `*CATCH` to `CATCH`, *etc*.), some functions are missing (`MEMQ`, `FIXP`), some signatues changed (`TYPEP`, `BREAK`, `IF`). See [3-lisp.cl](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.cl) for details.

Unfortunately, the port does not run on *all* modern Common Lisp implementations, because it relies on the proper support for [backquotes](https://www.gnu.org/software/emacs/manual/html_node/elisp/Backquote.html) across recursive reader [invocations](https://github.com/nikitadanilov/3-lisp/blob/master/3-lisp.cl#L92):

    ;;     Maclisp maintains backquote context across recursive parser
    ;;     invocations. For example in the expression (which happens within defun
    ;;     3-EXPAND-PAIR)
    ;;
    ;;         `\(PCONS ~,a ~,d)
    ;;
    ;;     the backquote is consumed by the top-level activation of READ. Backslash
    ;;     forces the switch to 3-lisp readtable and call to 3-READ to handle the
    ;;     rest of the expression. Within this 3-READ activation, the tilde forces
    ;;     switch back to L=READTABLE and a call to READ to handle ",a". In Maclisp,
    ;;     this second READ activation re-uses the backquote context established by
    ;;     the top-level READ activation. Of all Common Lisp implementations that I
    ;;     tried, only sbcl correctly handles this situation. Lisp Works and clisp
    ;;     complain about "comma outside of backquote". In clisp,
    ;;     clisp-2.49/src/io.d:read_top() explicitly binds BACKQUOTE-LEVEL to nil.

Among Common Lisp implementations I tried, only [sbcl](https://www.sbcl.org/) supports it properly. After reading Common Lisp [Hyperspec](http://www.lispworks.com/documentation/common-lisp.html), I believe that it is Maclisp and sbcl that implement the specification correctly and other implementations are faulty.

## Conclusion
Procedural Reflection in Programming Languages is, inspite of its age, a very interesting read. Not only in contains an implementation of a refreshingly new and bold idea (it is not even immediately obvious that infinite reflective towers can at all be implemented, not to say with any reasonable degree of efficiency), it is based on an interplay between mathematics and programming: the model of computation is proposed and afterwards implemented in `3-LISP`. Because the model is implemented in an actual running program, it has to be specified with extreme precision (which would make [Tarski](https://en.wikipedia.org/wiki/Alfred_Tarski) and [Łukasiewicz](https://en.wikipedia.org/wiki/Jan_%C5%81ukasiewicz) tremble), and any execution of the `3-LISP` interpreter validates the model. 

