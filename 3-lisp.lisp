;; -*- common-lisp -*-

;; 3-lisp implementation from Procedural Reflection in Programming Languages,
;; volume i., Brian Cantwell Smith, February 1982, Appendix, pp. 708--751.
;; http://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TR-272.pdf

;;; -*- Mode:LISP; Package:User; Base: 10. -*-                                      Page 1      001
;;;                                                                                             002
;;;                             3-LISP                                                          003
;;;                             ======                                                          004
;;;                                                                                             005
;;; A statically scoped, higher order, semantically rationalised, procedurally                  006
;;; reflective dialect of LISP, supporting SIMPLE and REFLECTIVE procedures.                    007
;;;                                                                                             008
;;; This is a straightforward and EXTREMELY INEFFICIENT implementation; the                     009
;;; intent is merely to manifest the basic 3-LISP functionality.  A variety                     010
;;; of techniques could increase the efficiency by several orders of magnitude                  011
;;; (most obvious would be to avoid consing explicit continuation structures at                 012
;;; each step of NORMALISE).  With some ingenuity 3-LISP could be implemented                   013
;;; as efficiently as any other dialect.                                                        014
;;;                                                                                             015
;;; 1. Structural Field:                                                                        016
;;; --------------------                                                                        017
;;;                                                                                             018
;;;     Structure Type     Designation             Notation                                     019
;;;                                                                                             020
;;;     1. Numerals     -- Numbers              -- sequence of digits                           021
;;;     2. Booleans     -- Truth values         -- $T or $F                                     022
;;;     3. Pairs        -- Functions (& appns)  -- (<exp> . <exp>)                              023
;;;     4. Rails        -- Sequences            -- [<exp> <exp> ... <exp>]                      024
;;;     5. Handles      -- S-expressions        -- '<exp>                                       025
;;;     6. Atoms        -- (whatever bound to)  -- sequences of alphanumerics                   026
;;;                                                                                             027
;;; a. There is no derived notion of a LIST, and no atom NIL.                                   028
;;; b. Pairs and rails are pseudo-composite; the rest are atomic.                               029
;;; c. Numerals, booleans, and handles are all normal-form and canonical.                       030
;;;    Some rails (those whose elements are normal form) and some pairs                         031
;;;    (the closures) are normal form, but neither type is canonical.                           032
;;;    No atoms are normal form.                                                                033
                                                                                              ; 034
;;; 2. Semantics:  The semantical domain is types as follows:                                   035
;;; -------------                                                                               036
;;;                                       ___ numeral                                           037
;;;                                      |___ boolean                                           038
;;;                 ____ s-expression ___|___ pair                                              039
;;;                |                     |___ rail                                              040
;;;                |                     |___ handle                                            041
;;;                |                     |___ atom                                              042
;;;      Object ___|                                                                            043
;;;                |                      ___ number                                            044
;;;                |____ abstraction ____|___ truth-value                                       045
;;;                |                     |___ sequence                                          046
;;;                |                                                                            047
;;;                |_________________________ function                                          048
                                                                                              ; 049
;;; 3. Notation                                                                                 050
;;; -----------                                                                                 051
;;;                                                                                             052
;;; Each structural field category is notated with a distinguishable notational                 053
;;; category, recognisable in the first character. as follows (thus 3-LISP                      054
;;; could be parsed by a grammar with a single character look-ahead):                           055
;;;                                                                                             056
;;;     1. Digit        -->  Numeral      4. Left bracket    --> Rail                           057
;;;     2. Dollar sign  -->  Boolean      5. Single quote    --> Handle                         058
;;;     3. Left paren   -->  Pair         6. Non-digit       --> Atom                           059
;;;                                                                                             060
;;; The only exceptions are that numerals can have a leading "+" or "-", and in                 061
;;; this implementation an atom may begin with a numeral providing it contains                  062
;;; at least one non-digit (since MACLISP supports that).                                       063
;;;                                                                                 Page 1:1    064
;;; BNF Grammar  Double quotes surround object level constants, "←" indicates                   065
;;; -----------  concatenation, brackets delineate groupings, "*" means                         066
;;;              zero-or-more repetition, and "|" separates alternatives:                       067
;;;                                                                                             068
;;; formula     ::= [break←]* form [←break]*                                                    069
;;; form        ::= L-numeral | L-boolean | L-pair | L-rail | L-handle | L-atom                 070
;;;                                                                                             071
;;; L-numeral   ::= ["+"← | "-"←]* digit [←digit]*                                              072
;;; L-boolean   ::= "$T" | "$F"                                                                 073
;;; L-pair      ::= "("← formula ←"."← formula ←")"                                             074
;;; L-rail      ::= "["← [formula←]* "]"                                                        075
;;; L-handle    ::= "'"← formula                                                                076
;;; L-atom      ::= [character←]* non-digit [←character]*                                       077
;;;                                                                                             078
;;; character   ::= digit | non-digit                                                           079
;;; non-digit   ::= alphabetic | special                                                        080
;;;                                                                                             081
;;; digit       ::= "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" | "0"                   082
;;; alphabetic  ::= "a" | "b" | "c" | ... | "A" | "B" | "C" | ... etc.                          083
;;; special     ::= "*" | "-" | "+" | "/" | "@" | "#" | "%" | "&" | "<" | ">" |                 084
;;;                 "←" | "=" | "\" | "?" | ":" | "~" | "!"                                     085
;;; reserved    ::= "'" | ";" | "(" | ")" | "[" | "]" | "{" | "}" | "|" | """ |                 086
;;;                 "," | "." | "↑" | "`" | "$" | <space> | <end-of-line>                       087
;;;                                                                                             088
;;; break       ::= <space> | <end-of-line> | comment                                           089
;;; comment     ::= ";" [←character | ←reserved | ←<space> ]* <end-of-line>                     090
;;;                                                                                             091
;;; The Lexical Notation Interpretation Function THETA (by category):                           092
;;; -----------------------------------------------------------------                           093
;;;                                                                                             094
;;; L-numeral   -- Numerals in the standard fashion;                                            095
;;; L-boolean   -- $T and $F to each of the two booleans;                                       096
;;; L-pair      -- A new (otherwise inaccessible) pair whose CAR is THETA of                    097
;;;                the first formula and whose CDR is THETA of the second;                      098
;;; L-rail      -- A new (otherwise inaccessible) tail whose elements are THETA                 099
;;;                of each of the constituent formulae;                                         100
;;; L-handle    -- The handle of THETA of the constituent formula.                              101 [sic. "." vs. ";"]
;;; L-atom      -- The corresponding atom.                                                      102
;;;                                                                                             103
;;; NOTES:                                                                                      104
;;;                                                                                             105
;;; 1. Case is ignores (converted to upper case on input)                                       106
;;; 2. Notational Sugar:                                                                        107
;;;                                                                                             108
;;;     "(<e1> <e2> ... <en>)" abbreviates "(<e1> . [<e2> ... <en>])"                           109
;;;                                                                                             110
;;; 3. We use exclamation point in place of down-arrow, since MACLISP does                      111
;;;    not support the latter character (in it not in ASCII, sadly).                            112
;;; 4. A Summary of the use of reserved characters:                                             113
;;;                                                                                             114
;;;    a:  (  -- starts pairs                h:  .  -- in "[ ... ]" for JOIN                    115
;;;    b:  )  -- ends pairs                  i:  ↑  -- NAME                                     116
;;;    c:  .  -- in "( ... )" for CDR        j:  !  -- REFERENT                                 117
;;;    d:  [  -- starts rails               (k:  :  -- DYNAMIC)                                 118
;;;    e:  ]  -- ends rails                  l:  `  -- Backquote a la MACLISP                   119 [sic. capitalisation]
;;;    f:  '  -- starts handles              m:  ,  --    "      "  "    "                      120
;;;    g:  ;  -- starts comments (to CRLF)   n:  ~  -- Switch to MACLISP                        121
;;;                                                                                             122
;;;    A-g are primitive, h-m are sugar, and n in implementation-specific.  In                  123
;;;    this implementation, since "!" is used for REFERENT (it should be                        124
;;;    down-arrow), it is reserved rather than special.  Similarly, "~" is                      125
;;;    reserved in this implementation for the MACLISP escape.  Finally, the                    126
;;;    characters "{", "}", "|" and """ are reserved but not currently used                     127
;;;    (intended for sacks, arbitrary atom names (a la MACLISP) and strings).                   128
;;;                                                                                 Page 1:2    129
;;; 4. Processor:                                                                               130
;;; -------------                                                                               131
;;;                                                                                             132
;;; The main driving loop of the processor is a READ-NORMALISE-PRINT loop                       133
;;; (see item 6, below), taking expressions into normal-form co-designators.                    134
;;; The normal form designators for each of the semantic types are:                             135
;;;                                                                                             136
;;;        Semantic type                Normal form designator (NFD)                            137
;;;                                                                                             138
;;;     1. Numbers                      Numerals                                                139
;;;     2. Truth-values                 Boolean constants                                       140
;;;     3. S-expressions                Handles                                                 141
;;;     4. Sequences                    Rails of NFD's of the elements                          142
;;;     5. Functions                    Pairs: (<type> <env> <pattern> <body>)                  143
;;;     6. Environments                 Rails: [['<a1> '<b1>] ['<a2> '<b2>] ... ]               144
;;;                                                                                             145
;;; 1-3 are CANONICAL, 4-6 are not.  Thus, A = B implies ↑A = ↑B only if A and                  146
;;; B designate numbers, truth-values, or s-expressions                                         147
                                                                                              ; 148
;;; 5. Primitive procedures:                                                                    149
;;; ------------------------                                                                    150
;;;                                                                                             151
;;;     Summary (fuller definitions are given below):                                           152
;;;                                                                                             153
;;; Typing:       TYPE                  -- defined over 10 types (4 syntactic)                  154
;;; Identity:     =                     -- defined over s-expressions, truth-                   155
;;;                                        values, sequences, and numbers                       156
;;; Structural:   PCONS, CAR, CDR       -- to construct and examine pairs                       157
;;;               LENGTH, NTH, TAIL     -- to examine rails and sequences                       158
;;;               RCONS, SCONS, PREP    -- to construct  "   "      "                           159
;;; Modifiers:    RPLACA, RPLACD        -- to modify pairs                                      160
;;;               RPLACN, RPLACT        -- "    "    rails                                      161
;;; Functions:    SIMPLE, REFLECT       -- make procedures from expressions                     162
;;; Control:      EF                    -- an extensional if-then-else conditional              163
;;; Semantics:    NAME, REFERENT        -- to mediate between sign & signified                  164
;;; Arithmetic:   +, -, *, /            -- as usual                                             165
;;; I/O:          READ, PRINT, TERPRI   -- as usual                                             166
;;; Reflection:   LEVEL                 -- the current reflective level                         167
;;;                                                                                             168
;;; The following kernel functions need NOT be primitive: they are defined in                   169
;;; the reflective model in terms of the above:                                                 170
;;;                                                                                             171
;;;     DEFINE, LAMBDA, NORMALISE, REDUCE, SET, BINDING, MACRO                                  172
;;;                                                                                             173
;;; Syntax and definitions:                                                                     174
;;;                                                                                             175
;;;     Form of use             Designation (environment relative):                             176
;;;                                                                                             177
;;;  (TYPE <exp>)           -- The atom indicating the type of <exp> (one of                    178
;;;                            the 10 on the fringe of the tree in #1, above)                   179
;;;                                                                                             180
;;;  (= <a> <b>)            -- Truth if <a> and <b> are the same, falsity                       181
;;;                            otherwise, providing <a> and <b> are of the                      182
;;;                            same type and are s-expressions, truth-values,                   183
;;;                            sequences, or numbers                                            184
;;;                                                                                             185
;;;  (PCONS <a> <b>)        -- A (new) pair whose CAR is <a> and CDR is <b>                     186
;;;  (CAR <a>)              -- The CAR of pair <a>                                              187
;;;  (CDR <a>)              -- The CDR of pair <b>                                              188
;;;  (RPLACA <a> <b>)       -- The new CAR <b> of modified pair <a>                             189
;;;  (RPLACD <a> <b>)       -- The new CDR <b> of modified pair <a>                             190
;;;                                                                                             191
;;;  (LENGTH <a>)           -- The length of rail or sequence <a>                               192
;;;  (NTH <n> <a>)          -- The <n>th element of rail of sequence <a>                        193
;;;  (TAIL <n> <a>)         -- Tail of rail/seq <a> starting after <n>th element                194
;;;  (RCONS <a1> ... <ak>)  -- A new rail whose elements are <a1>, ... , <ak>                   195 [sic. comma spacing]
;;;  (SCONS <a1> ... <ak>)  -- The sequence whose elements are <a1>, ..., <ak>                  196
;;;  (PREP <a> <rs>)        -- A new rail/seq whose 1st is <a>, 1st tail is <b>                 197 [sic. <b>, leg. <rs>]
;;;  (RPLACN <n> <a> <b>)   -- The new <n>th element <b> of modified rail <a>                   198
;;;  (RPLACT <n> <a> <b>)   -- The new <n>th tail <b> of modified rail <a>                      199
;;;                                                                                 Page 1:3    200
;;;  (SIMPLE  <e> <p> <b>)  -- NOT FOR CASUAL USE! (The function of given type                  201
;;;  (REFLECT <e> <p> <b>)     designated by the lambda abstraction of pattern                  202
;;;                            <p> over expression <b> in environment <e>)                      203
;;;                                                                                             204
;;;  (EF <p> <a> <b>)       -- <a>, if <p> designates truth; <b> is falsity.                    205 [sic. full stop]
;;;                                                                                             206
;;;  (NAME <a>)             -- The (or a) normal-form designator of <a>                         207
;;;  (REFERENT <a> <env>)   -- The object designated by <a> in environment <env>                208
;;;                                                                                             209
;;;  (+ <a> <b>)            -- The sum, difference, produce, and quotient of                    210 [sic. "produce", leg. "product"]
;;;  (- <a> <b>)               <a> and <b>, respectively                                        211
;;;  (* <a> <b>)                                                                                212
;;;  (/ <a> <b>)                                                                                213
;;;                                                                                             214
;;;  (READ)                 -- The s-expression notated by the next formula in                  215
;;;                            the input stream.                                                216 [sic. full stops]
;;;  (PRINT <a>)            -- <a>, which has just been printed.                                217
;;;                                                                                             218
;;;  (LEVEL)                -- The number of the current reflective level.                      219
                                                                                              ; 220
;;; 6. Processor Top Level:                                                                     221
;;; -----------------------                                                                     222
;;;                                                                                             223
;;; Each reflective level of the processor is assumed to start off                              224
;;; running the following function:                                                             225
;;;                                                                                             226
;;;   (define READ-NORMALISE-PRINT                                                              227
;;;      (lambda simple [env]                                                                   228
;;;         (block (prompt (level))                                                             229
;;;                (let [[normal-form (normalise (read) env id)]]                               230
;;;                   (prompt (level))                                                          231
;;;                   (print normal-form)                                                       232
;;;                   (read-normalise-print env)))))                                            233
;;;                                                                                             234
;;; The way this is imagined to work is as follows: the very top processor                      235
;;; level (infinitely high up) is invoked by someone (say, God, or some                         236
;;; functional equivalent) normalising the expression (READ-NORMALISE-PRINT                     237
;;; GLOBAL).  When it reads an expression, it is given the input string                         238
;;; "(READ-NORMALISE-PRINT GLOBAL"), which causes the level below it to read                    239
;;; an expression, which is in turn given "(READ-NORMALISE-PRINT GLOBAL)",                      240
;;; and so forth, until finally the second reflective level is given                            241
;;; "(READ-NORMALISE-PRINT GLOBAL)". This types "1>" on the console,                            242
;;; and awaits YOUR input.                                                                      243
;;;                                                                                             244
;;; 7. Environments:                                                                            245
;;; ----------------                                                                            246
;;;                                                                                             247
;;; Environments are sequences of two-element sequences, with each sub-sequence                 248
;;; consisting of a variable and a binding (both of which are of course                         249
;;; expressions).  A normal-form environment designator, therefore, is a rail of                250
;;; rails, with each rail consisting of two handles.  Variables are looked up                   251
;;; starting at the front (i.e. the second element of the first subrail whose                   252
;;; first element is the variable is the binding of that variable in that                       253
;;; environment).  Environments can also share tails: this is implemented by                    254
;;; normal-form environment designators sharing tails (this is used heavily in                  255
;;; the GLOBAL/ROOT/LOCAL protocols, and so forth).  Effecting a side effect on                 256
;;; the standard normal-form environment designator CHANGES what the environment                257
;;; is, which is as it should be.  Each level is initialised with the same global               258
;;; environment (the implementation does not support root environments -- see                   259
;;; note 11).                                                                       Page 1:4    260
;;;                                                                                             261
;;; 8. Implementation:                                                                          262
;;; ------------------                                                                          263
;;;                                                                                             264
;;;     3-LISP Structural Type:    MACLISP implementation:                                      265
;;;                                                                                             266
;;;     1. Numerals             -- Numerals                                                     267
;;;     2. Booleans             -- The atoms $T and $f                                          268
;;;     3. Pairs                -- Pairs                                                        269
;;;     4. Rails                -- (~RAIL~ <e1> ... <en>)  (but see note 9)                     270
;;;     5. Handles              -- (~QUOTE~ . <exp>)                                            271
;;;     6. Atoms                -- atoms (except for $T, $F, ~RAIL~, ~QUOTE~,                   272
;;;                                ~C0~, ~C1~, ~C2~, ~C3~, ~C4~, ~C5~, ~PRIM~,                  273
;;;                                and NIL)                                                     274
;;;                                                                                             275
;;; The main processor functions constantly construct MACLISP representations                   276
;;; of the 3-LISP normal-form designators of the continuations and environments                 277
;;; that WOULD be being used if the processor were running reflectively.  In                    278
;;; this way functions that reflect can be given the right arguments without                    279
;;; further ado.  In assembling these continuations and environments (see                       280
;;; 3-NORMALISE etc.), the code assumes that the incoming values are already in                 281
;;; normal form.  A more efficient but trickier strategy would be to put these                  282
;;; objects together only if and when they were called for; I haven't attempted                 283
;;; that here.  This would be all made simpler if both environments and                         284
;;; continuations were functions abstractly defined: no copying of structure                    285
;;; would ever be needed, since the appropriate behaviour could be wrapped                      286
;;; around the information in whatever form it was encoded in the primitive                     287
;;; implementation.                                                                             288
;;;                                                                                             289
;;; Two major recognition strategies are used for efficiency.  Those instances                  290
;;; of the four STANDARD continuation types that were generated by the MACLISP                  291
;;; version of the processor are trapped and decoded primitively: if this were                  292
;;; not done the processor would reflect at each step.  Also, explicit calls to                 293
;;; REDUCE and NORMALISE are trapped and run directly by the implementing                       294
;;; processor: this is not strictly necessary, but unless it were done the                      295
;;; processor might never come down again after reflecting up.                                  296
;;;                                                                                             297
;;; The standard continuation types, called C0 - C3, are identified in the                      298
;;; comments and in the definitions of NORMALISE and REDUCE (q.v.), and listed                  299
;;; below.  These types must be recognised by 3-APPLY and 3-REDUCE, so that the                 300
;;; implementing processor can drop down whenever possible, whether or not the                  301
;;; explicit interpretation of a (non-primitive) reflective function has                        302
;;; intervened.  The atoms ~C0~, ~C1~, ~C2~, and ~C3~ -- called the SIMPLE                      303
;;; ALIASES -- are used instead of the primitive SIMPLE closure as the function                 304
;;; type (i.e. as the CAR of the continuation closures).   These atoms are also                 305 [sic. triple space]
;;; MACLISP function names to effect the continuation).  The implementation                     306
;;; makes these atoms look = to the SIMPLE closure, so that the user cannot                     307
;;; tell different atoms are being used, but so that the continuations can be                   308
;;; trapped.                                                                                    309
;;;                                                                                             310
;;; Three other simple aliases are used (~C4~, ~C5~, and ~PRIM~).  ~C4~ is used                 311
;;; to identify the continuation used by READ-NORMALISE-PRINT, since the higher                 312
;;; level READ-NORMALISE-PRINT continuation may not explicitly exist.  ~C5~ is                  313
;;; used by the IN-3-LISP macro to read in 3-LISP code embedded within MACLISP                  314
;;; (it can therefore be used to read in 3-LISP code in files and so forth).                    315
;;; ~PRIM~ is used in normal-form designators of primitive procedures.  Thus,                   316
;;; while PCONS in the initial global environment looks to a 3-LISP program to                  317
;;; normalise to (<SIMPLE> '[ ... <global>] '[A B] '(PCONS A B)), in fact the                   318
;;; CAR of that form is ~PRIM~, not <SIMPLE>.                                                   319
;;;                                                                                             320
;;; The four standard continuations:                                                            321
;;;                                                                                             322
;;;    C0:  Accept the normalised function designator in an application.                        323
;;;    C1:  Accept the normalised arguments for a SIMPLE application.                           324
;;;    C2:  Accept the normalised first element in a rail fragment.                             325
;;;    C3:  Accept the normalised tail of a rail fragment.                                      326
;;;                                                                                             327
;;;   (C4:  Identifies top level call of READ-NORMALISE-PRINT.)                                 328
;;;   (C5:  Used in order to read in 3-LISP structures by IN-3-LISP.)                           329
;;; Programming conventions:                                                        Page 1:5    331 [sic. no 330]
;;;                                                                                             332
;;; Special variables are prefixed with "3=".  Procedures are prefixed with "3-".               333
;;; If they operate on MACLISP structures implementing 3-LISP structures, the                   334
;;; procedure name is defined with respect to the operation viewed with respect                 335
;;; to the 3-LISP structure.  For example, 3-EQUAL returns T if the two arguments               336
;;; encode the same 3-LISP structure.                                                           337
;;;                                                                                             338
;;; NOTE: in fall 1981, the implementation was minimally changed to run on an MIT               339
;;; CARD machine, not in MACLISP.  The only concessions to the new base were in                 340
;;; the treatment of I/O and interrupts; no particular features of the CARD have                341
;;; been used.  It should therefore require minimal work to retrofit it to a                    342
;;; MACLISP base.                                                                               343
                                                                                              ; 344
;;; 9. Rails: Implementation and Management:                                                    345
;;; ----------------------------------------                                                    346
;;;                                                                                             347
;;; The implementation of rails is tricky, because RPLACT modifications must be                 348
;;; able to take effect on the 0'th tail, as well as subsequent ones, requiring                 349
;;; either the use of full bi-directional linkages, or "invisible pointers" (a                  350
;;; true LISP-machine implementation could perhaps use the underlying invisible                 351
;;; pointer facility) and special circularity checking.  We choose the latter                   352
;;; option.  The implementation (where "+" means one of more, "*" means zero or                 353
;;; more) of a rail is:                                                                         354
;;;                                                                                             355
;;;     [a b ... z]   ==>   (<~RAIL~>+ a <~RAIL~>* b ... <~RAIL~>* z <~RAIL~>*)                 356
;;;                                                                                             357
;;; where the ~RAIL~ atoms are effectively invisible, but begin every rail that                 358
;;; is given out to the outside world (and can thus be used to distinguish                      359
;;; rails from 3-LISP cons pairs).  Just reading in [A B ... Z] generates                       360
;;; (~RAIL~ A B ... Z).                                                                         361
;;;                                                                                             362
;;; Unless RPLACT's are done, the number of ~RAIL~ atoms cannot exceed the number               363
;;; of elements.  With arbitrary RPLACT'ing, the efficiency can get arbitrarily                 364
;;; bad (although it could be corrected back to a linear constant of 2 by a                     365
;;; compacting garbage collector.)                                                              366 [sic. stop placement]
;;;                                                                                             367
;;; 10. User Interface:                                                                         368
;;; -------------------                                                                         369
;;;                                                                                             370
;;; To run 3-LISP, load the appropriate one of the following FASL files:                        371
;;;                                                                                             372
;;;     ML:     ML:BRIAN;3-LISP FASL                                                            373 [illegible: colon or semicolon?]
;;;     PARC:   [Phylum]<BrianSmith>3-lisp>3-lisp.qfasl                                         374
;;;                                                                                             375
;;; The processor can be started up by executing (3-LISP), and re-initialised                   376
;;; completely at any point by executing (3-INIT) (both in MACLISP).  The                       377
;;; READ-NORMALISE-PRINT loop prints the current reflective level to the left                   378
;;; of the prompt character.  The following interrupt characters are defined:                   379
;;;                                                                                             380
;;;     a. Control-E    -- Toggles between MACLISP and 3-LISP.                                  381
;;;                                                                                             382
;;;     b. Control-G    -- Quit to level 1       (regular quit in MACLISP)                      383 [sic. full stop]
;;;     c. Control-F    -- Quit to current level (regular quit in MACLISP)                      384
;;;                                                                                             385
;;; To read in and manipulate files, surround an arbitrary number of                            386
;;; expressions with the MACLISP wrapping macro IN-3-LISP, and precede each                     387
;;; 3-LISP expression with a backslash, so that it will be read in by the                       388
;;; 3-LISP reader.  Then load the file as if it were a regular MACLISP file.                    389
;;; For example:                                                                                390
;;;                                                                                             391
;;;     (in-3-lisp                                                                              392
;;;       \(define increment (lambda simple [x] (+ x 1)))                                       393
;;;       \(define quit      (lambda reflect [] 'QUIT)))                                        394
;;;                                                                                             395
;;; Equivalent, and with the advantage that TAGS and ? see the definitions, is:                 396 [illegible symbol.]
;;;                                                                                             397
;;;     (in-3-lisp \[                                                                           398
;;;                                                                                             399
;;;     (define increment (lambda simple [x] (+ x 1)))                                          400
;;;     (define quit      (lambda reflect ? 'QUIT))               ])                            401
;;;                                                                                 Page 1:6    404 [sic. no 402, 403]
;;; 11. Limitations of the Implementation:                                                      405
;;; --------------------------------------                                                      406
;;;                                                                                             407
;;; There are a variety of respects in which this implementation is incomplete                  408
;;; or flawed:                                                                                  409
;;;                                                                                             410
;;; 1. Side effects to the reflective procedures will not be noticed -- in a                    411
;;;    serious implementation these procedures would want to be kept in a pure                  412
;;;    page so that side effects to them could be trapped, causing one level                    413
;;;    of reflective deferral.                                                                  414
;;;                                                                                             415
;;; 2. Reflective deferral is not yet support at all.  No problems are                          416 [sic. leg. "supported"]
;;;    expected; it merely needs attention.                                                     417
;;;                                                                                             418
;;; 3. In part because I think it may be a bad idea, this implementation does                   419
;;;    not support a root environment protocol.                                                 420
;;;                                                                                             421
;;; 12. Obvious Extensions:                                                                     422
;;; -----------------------                                                                     423
;;;                                                                                             424
;;; Obvious extensions to the implementation fall into two groups: those that                   425
;;; would increase the efficiency of the implementation, but not change its                     426
;;; basic functionality, and those that would extent that functionality.                        427
;;; Regarding the first, the following are obvious candidates:                                  428
;;;                                                                                             429
;;; 1. Get rid of the automatic consing of continuation and environment                         430
;;;    structures, as mentioned earlier.                                                        431
;;;                                                                                             432
;;; 2. Support various intensional procedures (LAMBDA, IF, COND, MACRO, SELECT,                 433
;;;    and so forth) as primitives.  This would require the virtual provision                   434
;;;    of all of the continuation structure at the reflective level that would                  435
;;;    have been generated has the definitions used here been used explicitly:                  436
;;;    it wouldn't be trivial.  Unless, of course, the language was redefined                   437
;;;    to include these as primitives (but the current proof of its finiteness                  438
;;;    depends on no reflective primitives, so this too would take some work).                  439
;;;                                                                                             440
;;; Functional extensions include:                                                              441
;;;                                                                                             442
;;; 1. Make the bodies of LAMBDA, LET, COND, etc. take multiple expressions                     443
;;;    (i.e. be virtual BLOCK bodies).                                                          444
;;;                                                                                             445
;;; 2. Strings (all normal-form string designators, perhaps called "STRINGERS")                 446
;;;    could be added.                                                                          447
                                                                                              ; 448

;;;                                                                                 Page 2      001
;;;                                                                                             002
;;;                                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;;                                                                                             006
;;;                                                                                             007
;;;                                                                                             008
;;;                                                                                             009
;;;                                                                                             010
;;;                                                                                             011
;;;                                                                                             012
;;;                                                                                             013
;;;                                                                                             014
;;;                                                                                             015
;;;                                                                                             016
;;;                                                                                             017
;;;                                                                                             018
;;;                                                                                             019
;;;                                                                                             020
;;;                                                                                             021
;;;                                                                                             022
;;;                                                                                             023
;;;                                                                                             024
;;;                                                                                             025
;;;                                                                                             026
;;;                                                                                             027
;;;                                                                                             028
;;;                                                                                             029
;;;                                                                                             030
;;;                                                                                             031
;;;                                                                                             032
;;;                                                                                             033
;;;                                                                                             034
;;;                                                                                             035
;;;                                                                                             036
;;;                                                                                             037
;;;                                                                                             038
;;;                                                                                             039
;;;                                                                                             040
;;;                                                                                             041
;;;                                                                                             042
;;;                                                                                             043
;;;                                                                                             044
;;;                                                                                             045
;;;                                                                                             046
;;;                                                                                             047
;;;                                                                                             048
;;;                                                                                             049
;;;                                                                                             050
;;;                                                                                             051
;;;                                                                                             052
;;;                                                                                             053
;;;                                                                                             054
;;;                                                                                             055
;;;                                                                                             056
;;;                                                                                             057
;;;                                                                                             058
;;;                                                                                             059
;;;                                                                                             060
;;;                                                                                             061
;;;                                                                                             062
;;;                                                                                             063
;;;                                                                                             064
;;;                                                                                             065
;;;                                                                                             066
;;;                                                                                             067
;;;                                                                                             068
;;;                                                                                             069
;;;                                                                                             070
;;;                                                                                             071
;;;                                                                                             072
;;;                                                                                             073
;;;                                                                                             074
;;;                                                                                             075
;;;                                                                                             076
;;;                                                                                             077
;;;                                                                                             078
;;;                                                                                             079
;;;                                                                                             080
;;;                                                                                             081
;;;                                                                                             082
;;;                                                                                             083
;;;                                                                                             084
;;;                                                                                             085
;;;                                                                                             086
;;;                                                                                             087
;;;                                                                                             088
;;;                                                                                             089
;;;                                                                                             090
;;;                                                                                             091
;;;                                                                                             092
;;;                                                                                             093
;;;                                                                                             094
;;;                                                                                             095
;;;                                                                                             096
;;;                                                                                             097
;;;                                                                                             098
;;;                                                                                             099

;;;                                                                                             000
;;;                                                                                             001
;;;                                                                                             002
;;;                                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;;                                                                                             006
;;;                                                                                             007
;;;                                                                                             008
;;;                                                                                             009
;;;                                                                                             010
;;;                                                                                             011
;;;                                                                                             012
;;;                                                                                             013
;;;                                                                                             014
;;;                                                                                             015
;;;                                                                                             016
;;;                                                                                             017
;;;                                                                                             018
;;;                                                                                             019
;;;                                                                                             020
;;;                                                                                             021
;;;                                                                                             022
;;;                                                                                             023
;;;                                                                                             024
;;;                                                                                             025
;;;                                                                                             026
;;;                                                                                             027
;;;                                                                                             028
;;;                                                                                             029
;;;                                                                                             030
;;;                                                                                             031
;;;                                                                                             032
;;;                                                                                             033
;;;                                                                                             034
;;;                                                                                             035
;;;                                                                                             036
;;;                                                                                             037
;;;                                                                                             038
;;;                                                                                             039
;;;                                                                                             040
;;;                                                                                             041
;;;                                                                                             042
;;;                                                                                             043
;;;                                                                                             044
;;;                                                                                             045
;;;                                                                                             046
;;;                                                                                             047
;;;                                                                                             048
;;;                                                                                             049
;;;                                                                                             050
;;;                                                                                             051
;;;                                                                                             052
;;;                                                                                             053
;;;                                                                                             054
;;;                                                                                             055
;;;                                                                                             056
;;;                                                                                             057
;;;                                                                                             058
;;;                                                                                             059
;;;                                                                                             060
;;;                                                                                             061
;;;                                                                                             062
;;;                                                                                             063
;;;                                                                                             064
;;;                                                                                             065
;;;                                                                                             066
;;;                                                                                             067
;;;                                                                                             068
;;;                                                                                             069
;;;                                                                                             070
;;;                                                                                             071
;;;                                                                                             072
;;;                                                                                             073
;;;                                                                                             074
;;;                                                                                             075
;;;                                                                                             076
;;;                                                                                             077
;;;                                                                                             078
;;;                                                                                             079
;;;                                                                                             080
;;;                                                                                             081
;;;                                                                                             082
;;;                                                                                             083
;;;                                                                                             084
;;;                                                                                             085
;;;                                                                                             086
;;;                                                                                             087
;;;                                                                                             088
;;;                                                                                             089
;;;                                                                                             090
;;;                                                                                             091
;;;                                                                                             092
;;;                                                                                             093
;;;                                                                                             094
;;;                                                                                             095
;;;                                                                                             096
;;;                                                                                             097
;;;                                                                                             098
;;;                                                                                             099

;;;                                                                                             000
;;;                                                                                             001
;;;                                                                                             002
;;;                                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;;                                                                                             006
;;;                                                                                             007
;;;                                                                                             008
;;;                                                                                             009
;;;                                                                                             010
;;;                                                                                             011
;;;                                                                                             012
;;;                                                                                             013
;;;                                                                                             014
;;;                                                                                             015
;;;                                                                                             016
;;;                                                                                             017
;;;                                                                                             018
;;;                                                                                             019
;;;                                                                                             020
;;;                                                                                             021
;;;                                                                                             022
;;;                                                                                             023
;;;                                                                                             024
;;;                                                                                             025
;;;                                                                                             026
;;;                                                                                             027
;;;                                                                                             028
;;;                                                                                             029
;;;                                                                                             030
;;;                                                                                             031
;;;                                                                                             032
;;;                                                                                             033
;;;                                                                                             034
;;;                                                                                             035
;;;                                                                                             036
;;;                                                                                             037
;;;                                                                                             038
;;;                                                                                             039
;;;                                                                                             040
;;;                                                                                             041
;;;                                                                                             042
;;;                                                                                             043
;;;                                                                                             044
;;;                                                                                             045
;;;                                                                                             046
;;;                                                                                             047
;;;                                                                                             048
;;;                                                                                             049
;;;                                                                                             050
;;;                                                                                             051
;;;                                                                                             052
;;;                                                                                             053
;;;                                                                                             054
;;;                                                                                             055
;;;                                                                                             056
;;;                                                                                             057
;;;                                                                                             058
;;;                                                                                             059
;;;                                                                                             060
;;;                                                                                             061
;;;                                                                                             062
;;;                                                                                             063
;;;                                                                                             064
;;;                                                                                             065
;;;                                                                                             066
;;;                                                                                             067
;;;                                                                                             068
;;;                                                                                             069
;;;                                                                                             070
;;;                                                                                             071
;;;                                                                                             072
;;;                                                                                             073
;;;                                                                                             074
;;;                                                                                             075
;;;                                                                                             076
;;;                                                                                             077
;;;                                                                                             078
;;;                                                                                             079
;;;                                                                                             080
;;;                                                                                             081
;;;                                                                                             082
;;;                                                                                             083
;;;                                                                                             084
;;;                                                                                             085
;;;                                                                                             086
;;;                                                                                             087
;;;                                                                                             088
;;;                                                                                             089
;;;                                                                                             090
;;;                                                                                             091
;;;                                                                                             092
;;;                                                                                             093
;;;                                                                                             094
;;;                                                                                             095
;;;                                                                                             096
;;;                                                                                             097
;;;                                                                                             098
;;;                                                                                             099

;;;                                                                                             000
;;;                                                                                             001
;;;                                                                                             002
;;;                                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;;                                                                                             006
;;;                                                                                             007
;;;                                                                                             008
;;;                                                                                             009
;;;                                                                                             010
;;;                                                                                             011
;;;                                                                                             012
;;;                                                                                             013
;;;                                                                                             014
;;;                                                                                             015
;;;                                                                                             016
;;;                                                                                             017
;;;                                                                                             018
;;;                                                                                             019
;;;                                                                                             020
;;;                                                                                             021
;;;                                                                                             022
;;;                                                                                             023
;;;                                                                                             024
;;;                                                                                             025
;;;                                                                                             026
;;;                                                                                             027
;;;                                                                                             028
;;;                                                                                             029
;;;                                                                                             030
;;;                                                                                             031
;;;                                                                                             032
;;;                                                                                             033
;;;                                                                                             034
;;;                                                                                             035
;;;                                                                                             036
;;;                                                                                             037
;;;                                                                                             038
;;;                                                                                             039
;;;                                                                                             040
;;;                                                                                             041
;;;                                                                                             042
;;;                                                                                             043
;;;                                                                                             044
;;;                                                                                             045
;;;                                                                                             046
;;;                                                                                             047
;;;                                                                                             048
;;;                                                                                             049
;;;                                                                                             050
;;;                                                                                             051
;;;                                                                                             052
;;;                                                                                             053
;;;                                                                                             054
;;;                                                                                             055
;;;                                                                                             056
;;;                                                                                             057
;;;                                                                                             058
;;;                                                                                             059
;;;                                                                                             060
;;;                                                                                             061
;;;                                                                                             062
;;;                                                                                             063
;;;                                                                                             064
;;;                                                                                             065
;;;                                                                                             066
;;;                                                                                             067
;;;                                                                                             068
;;;                                                                                             069
;;;                                                                                             070
;;;                                                                                             071
;;;                                                                                             072
;;;                                                                                             073
;;;                                                                                             074
;;;                                                                                             075
;;;                                                                                             076
;;;                                                                                             077
;;;                                                                                             078
;;;                                                                                             079
;;;                                                                                             080
;;;                                                                                             081
;;;                                                                                             082
;;;                                                                                             083
;;;                                                                                             084
;;;                                                                                             085
;;;                                                                                             086
;;;                                                                                             087
;;;                                                                                             088
;;;                                                                                             089
;;;                                                                                             090
;;;                                                                                             091
;;;                                                                                             092
;;;                                                                                             093
;;;                                                                                             094
;;;                                                                                             095
;;;                                                                                             096
;;;                                                                                             097
;;;                                                                                             098
;;;                                                                                             099

;;;                                                                                             000
;;;                                                                                             001
;;;                                                                                             002
;;;                                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;;                                                                                             006
;;;                                                                                             007
;;;                                                                                             008
;;;                                                                                             009
;;;                                                                                             010
;;;                                                                                             011
;;;                                                                                             012
;;;                                                                                             013
;;;                                                                                             014
;;;                                                                                             015
;;;                                                                                             016
;;;                                                                                             017
;;;                                                                                             018
;;;                                                                                             019
;;;                                                                                             020
;;;                                                                                             021
;;;                                                                                             022
;;;                                                                                             023
;;;                                                                                             024
;;;                                                                                             025
;;;                                                                                             026
;;;                                                                                             027
;;;                                                                                             028
;;;                                                                                             029
;;;                                                                                             030
;;;                                                                                             031
;;;                                                                                             032
;;;                                                                                             033
;;;                                                                                             034
;;;                                                                                             035
;;;                                                                                             036
;;;                                                                                             037
;;;                                                                                             038
;;;                                                                                             039
;;;                                                                                             040
;;;                                                                                             041
;;;                                                                                             042
;;;                                                                                             043
;;;                                                                                             044
;;;                                                                                             045
;;;                                                                                             046
;;;                                                                                             047
;;;                                                                                             048
;;;                                                                                             049
;;;                                                                                             050
;;;                                                                                             051
;;;                                                                                             052
;;;                                                                                             053
;;;                                                                                             054
;;;                                                                                             055
;;;                                                                                             056
;;;                                                                                             057
;;;                                                                                             058
;;;                                                                                             059
;;;                                                                                             060
;;;                                                                                             061
;;;                                                                                             062
;;;                                                                                             063
;;;                                                                                             064
;;;                                                                                             065
;;;                                                                                             066
;;;                                                                                             067
;;;                                                                                             068
;;;                                                                                             069
;;;                                                                                             070
;;;                                                                                             071
;;;                                                                                             072
;;;                                                                                             073
;;;                                                                                             074
;;;                                                                                             075
;;;                                                                                             076
;;;                                                                                             077
;;;                                                                                             078
;;;                                                                                             079
;;;                                                                                             080
;;;                                                                                             081
;;;                                                                                             082
;;;                                                                                             083
;;;                                                                                             084
;;;                                                                                             085
;;;                                                                                             086
;;;                                                                                             087
;;;                                                                                             088
;;;                                                                                             089
;;;                                                                                             090
;;;                                                                                             091
;;;                                                                                             092
;;;                                                                                             093
;;;                                                                                             094
;;;                                                                                             095
;;;                                                                                             096
;;;                                                                                             097
;;;                                                                                             098
;;;                                                                                             099
