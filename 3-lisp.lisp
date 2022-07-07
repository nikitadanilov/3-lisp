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
;;; 2. Semantics:  The semantical domain is typed as follows:                                   035
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
;;; Equivalent, and with the advantage that TAGS and @ see the definitions, is:                 396
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
;;; Declaration and Macros:                                                                     002
;;; =======================                                                                     003
                                                                                              ; 004
(declare                                                                                      ; 005
  (special                                                                                    ; 006
    3=simple-aliases 3=global-environment 3=states 3=level 3=break-flag                       ; 007
    3=in-use 3=readtable L=readtable S=readtable 3=a2 3=a2 3=a3 3=a4                          ; 008
    3=normalise-closure 3=reduce-closure 3=simple-closure 3=reflect-closure                   ; 009
    3=id-closure 3=backquote-depth ignore 3=process)                                          ; 010
  (*lexpr 3-read 3-read* 3-error))                                                            ; 011
                                                                                              ; 012
;;; (herald 3-LISP)                                                                             013
                                                                                              ; 014
(eval-when (load eval compile)                                                                ; 015
                                                                                              ; 016
(defmacro list? (x) `(eq (typep ,x) 'list))                                                   ; 017
(defmacro 1st (l) `(car ,l))                                                                  ; 018
(defmacro 2nd (l) `(cadr ,l))                                                                 ; 019
(defmacro 3rd (l) `(caddr ,l))                                                                ; 020
                                                                                              ; 021
)                                                                                             ; 022
                                                                                              ; 023
(defmacro 3-primitive-simple-id (proc) `(card (3r-3rd (cdr ,proc))))                          ; 024
                                                                                              ; 025
(defmacro 3-numeral (e) `(fixp ,e))                                                           ; 026
(defmacro 3-boolean `(memq ,e '($T $F)))                                                      ; 027
                                                                                              ; 028
(defmacro 3-bind (vars vals env)                                                              ; 029
   `(cons '~RAIL~ (nconc (3-bind* ,vars ,vals) ,env)))                                        ; 030
                                                                                              ; 031
;;; Two macros having to do with input:                                                         032
                                                                                              ; 033
(defmacro in-3-lisp (&rest body)                                                              ; 034
   `(progn (or (boundp '3=global-environment) (3-init))                                       ; 035
           ,@(do ((exprs body (cdr exprs))                                                    ; 036
                  (forms nil (cons `(3-lispify ',(car exprs)) forms)))                        ; 037
                 ((null exprs) (nreverse forms)))))                                           ; 038
                                                                                              ; 039
(defmacro ~3-BACKQUOTE (expr) (3-expand expr nil))                                            ; 040
                                                                                              ; 041
;;; 3-NORMALISE*   If MACLISP were tail-recursive, calls to this would                          042
;;; ------------   simply call 3-NORMALISE.  Sets up the loop variables                         043
;;;                and jumps to the top of the driving loop.                                    044
                                                                                              ; 045
(defmacro 3-normalise* (exp env cont)                                                         ; 046
   `(progn (setq 3=a1 ,exp 3=a2 ,env 3=a3 ,cont)                                              ; 047
           (throw '3-main-loop 'nil)))                                                        ; 048
                                                                                              ; 049
;;; The rest of the macro definitions are RAIL specific:                                        050
                                                                                              ; 051
(defmacro 3r-1st (exp) `(car (3-strip ,exp)))                                                 ; 052
(defmacro 3r-2nd (exp) `(car (3-strip (3-strip ,exp))))                                       ; 053
(defmacro 3r-3rd (exp) `(car (3-strip (3-strip (3-strip ,exp)))))                             ; 054
(defmacro 3r-4th (exp) `(car (3-strip (3-strip (3-strip (3-strip ,exp))))))                   ; 055
                                                                                              ; 056
;;; Macros for RAIL management:                                                                 057
                                                                                              ; 058
;;; 3-STRIP           -- Returns a rail with all ~RAIL~ headers removed.  Have                  059
;;; -------              have to step through as many headers as have built up.                 060 [sic. "have"]
;;;                                                                                             061
;;; 3-STRIP*          -- Returns the last header of arg -- used for RPLACD, and                 062
;;; --------             to establish rail identify.  Steps down through headers.               063
                                                                                              ; 064
(eval-when (load eval compile)                                                                ; 065
                                                                                              ; 066
(defmacro 3-strip (rail)                                                                      ; 067
   `(do ((rest (cdr ,rail) (cdr rest)))                                                       ; 068
        ((not (eq (car rest) '~RAIL~)) rest)))                                                ; 069
                                                                                  ; Page 2:1    070
(defmacro 3-strip* (rail)                                                                     ; 071
   `(do ((rest ,rail (cdr rest)))                                                             ; 072
        ((not (eq (cadr rest) '~RAIL~)) rest)))                                               ; 073
                                                                                              ; 074
)                                                                                             ; 075
                                                                                              ; 076
;;; 3-LENGTH*         -- Return the length of a 3-LISP rail.                                    077 [sic. "return" vs. "returns"]
                                                                                              ; 078
(defmacro 3-length* (rail)                                                                    ; 079
   `(do ((n 0 (1+ n))                                                                         ; 080
         (rail (3-strip ,rail) (3-strip rail)))                                               ; 081
        ((null rail) n)))                                                                     ; 082
                                                                                              ; 083
                                                                                  ; Page 3      001
;;; Input/Output:                                                                               002
;;; =============                                                                               003
;;;                                                                                             004
                                                                                              ; 005
;;; A special readtable (3=READTABLE) is used to read in 3-LISP notation, since                 006
;;; it must be parsed differently from MACLISP notation.  The 3-LISP READ-                      007
;;; NORMALISE-PRINT loop uses this; in addition, a single expression will be                    008
;;; read in under the 3-LISP reader if preceded by backslash ("\") in the                       009
;;; MACLISP reader.  Similarly, a single expression will be read in by the                      010
;;; MACLISP reader if preceded with a tilde ("~") in the 3-LISP reader.                         011
;;;                                                                                             012
;;; MACLISP and 3-LISP both support backquote.  The readers and the backquotes                  013
;;; can be mixed, but be cautious: the evaluated or normalised expression must                  014
;;; be read in with the right reader.  For example, a MACLISP backquoted                        015
;;; expression can contain a 3-LISP fragment with a to-be-evaluated-by-MACLISP                  016
;;; constituent, but a tilde is required before it, so that the MACLISP reader                  017
;;; will see it.  Example: "`\[value ~,(plus x y)]".  ",@" and ",." are not                     018
;;; supported by the 3-LISP backquote.                                                          019
;;;                                                                                             020
;;; Any 3-LISP backquoted expression will expand to a new-structure-creating                    021
;;; expression at the level of the back-quote, down to and including any level                  022 [sic. hyphenation]
;;; including a comma'ed expression.  Thus `[] expands to (rcons), `[[a b c] [d                 023
;;; ,e f]] expands to (rcons '[a b c] (rcons 'd e 'f)), and so forth.  This is                  024
;;; done so as to minimise the chance of unwanted shared tails, but to avoid                    025
;;; unnecessary structure consing.  We use `[] in place of (rcons) many times in                026
;;; the code.                                                                                   027
;;;                                                                                             028
;;; Expressions like "~~C0~" are necessary in order to get the aliases into                     029
;;; 3-LISP, since the first tilde flips readers.  Once 3-LISP has been                          030
;;; initialised the aliases will be rejected: to reload a function containing an                031
;;; alias, temporarily bind 3=simple-aliases to NIL.                                            032
;;;                                                                                             033
;;; There are two special read macro characters, for name and referent (MACLISP                 034
;;; and 3-LISP versions).  (Ideallt these would be uparrow and downarrow, but                   035
;;; down-arrow is unfortunately not an ASCII character):                                        036 [sic. hyphenation]
;;;                                                                                             037
;;;      Form           MACLISP expansion       3-LISP expansion                                038
;;;                                                                                             039
;;;     1. ↑<exp>       (3-NAME <exp>)          (NAME <exp>)                                    040
;;;     2. !<exp>       (3-REF <exp>)           (REFERENT <exp> (current-env))                  041
                                                                                              ; 042
(eval-when (load eval compile)                                                                ; 043
                                                                                              ; 044
;;; Five constants needed to be defined for 3-LISP structures to be read in:                    045
                                                                                              ; 046
(setq S=readtable readtable                       ; Save the system readtable                 ; 047
      L=readtable (copy-readtable)                ; and name two special ones:                ; 048
      3=readtable (copy-readtable)                ; one for LISP, one for 3-LISP.             ; 049
      3=simple-aliases nil                        ; Make these NIL so we can read             ; 050
      3=backquote-depth 0)                        ; in the aliases in this file!              ; 051
                                                                                              ; 052
;;; The following has been modified from the original MACLISP to enable it to                   053
;;; operate under the I/O protocols of the MIT LISP machine:                                    054
                                                                                              ; 055
(login-setq readtable L=readtable)                ; Needed in order to read this file.        ; 056
                                                                                              ; 057
(let ((readtable L=readtable))                                                                ; 058
   (set-syntax-macro-char #/\ #'(lambda (l s) (3-read s)))                                    ; 059
   (set-syntax-macro-char #/↑ #'(lambda (l s) `(cons '~QUOTE~ ,(read s))))                    ; 060
   (set-syntax-macro-char #/! #'(lambda (l s) `(3-ref ,(read s))))                            ; 061
   (set-syntax-from-description #/] 'si:single))        ; So "~FOO]" will work.               ; 062
                                                                                  ; Page 3:1  ; [sic. no line number]
                                                                                              ; 063
(let ((readtable 3=readtable))                                                                ; 064
   (set-syntax-macro-char #/~ #'(lambda (l s) (let ((readtable L=readtable)) (read s))))      ; 065
   (set-syntax-macro-char #/! #'(lambda (l s) `(referent ~RAIL~ ,(3-read*s)                   ; 066
                                                         (current-env ~RAIL~))))              ; 067
   (set-syntax-macro-char #/↑ #'(lambda (l s) `(name ~RAIL~ ,(3-read* s))))                   ; 068
   (set-syntax-macro-char #/' #'(lambda (l s) `(~QUOTE~ . ,(3-read* s))))                     ; 069
   (set-syntax-macro-char #/( #'(lambda (l s) (3-read-pair s)))                               ; 070
   (set-syntax-macro-char #/[ #'(lambda (l s) (3-read-rail s)))                               ; 071
   (set-syntax-macro-char #/` #'(lambda (l s) (3-backq-macro s)))                             ; 072
   (set-syntax-macro-char #/, #'(lambda (l s) (3-comma-macro s)))                             ; 073
   (set-syntax-from-description #/) 'si:single)                                               ; 074
   (set-syntax-from-description #// 'si:single)                                               ; 075
   (set-syntax-from-description #/$ 'si:single)                                               ; 076
   (set-syntax-from-description #/] 'si:single)                                               ; 077
   (set-syntax-from-description #/. 'si:single))                                              ; 078
                                                                                              ; 079
;;; 3-READ(*)  Read in one 3-LISP s-expression (*-version assumes the                           080
;;;            3-LISP readtable is already in force, and accepts an                             081
;;;            optional list of otherwise illegal atoms to let through).                        082
                                                                                              ; 083
(defun 3-read (&optional stream)                                                              ; 084
   (let ((readtable 3=readtable)) (3-read* stream)))                                          ; 085
                                                                                              ; 086
(defun 3-read* (stream &optional OK)                                                          ; 087
   (let ((token (read stream)))                                                               ; 088
      (cond ((memq token OK) token)                                                           ; 089
            ((memq token '(|)| |.| |]|)) (3-illegal-char token))                              ; 090
            ((or (memq token '(~RAIL~ ~QUOTE~ NIL))                                           ; 091
                 (memq token 3=simple-aliases)) (3-illegal-atom token))                       ; 092
            ((eq token '/$) (3-read-boolean stream))                                          ; 093
            (t token))))                                                                      ; 094
                                                                                              ; 095
(defun 3-read-booleam (stream)                                                                ; 096
   (let ((a (readch stream)))                                                                 ; 097
      (cond ((memq a '(T /t)) '$T)                                                            ; 098
            ((memq a '(F /f)) '$F)                                                            ; 099
            (t (3-illegal-boolean a)))))                                                      ; 100
                                                                                              ; 101
(defun 3-read-pair (stream)                                                                   ; 102
   (let ((a (3-read* stream))                                                                 ; 103
         (b (3-read* stream '(|.| |)|))))                                                     ; 104
      (if (eq b '|.|)                                                                         ; 105
          (prog1 (cons a (3-read* stream))                                                    ; 106
                 (setq b (read stream))                                                       ; 107
                 (if (not (eq b '|)|)) (3-illegal-char b)))                                   ; 108
          (do ((b b (3-read* stream '(|)|)))                                                  ; 109
               (c nil (cons b c)))                                                            ; 110
              ((eq b '|)|) (list* a '~RAIL~ (nreverse c)))))))                                ; 111
                                                                                              ; 112
(defun 3-read-rail (stream)                                                                   ; 113
   (do ((a nil (cons b a))                                                                    ; 114
        (b (3-read* stream '(|]|)) (3-read* stream '(|]|))))                                  ; 115
       ((eq b '|]|) (cons '~RAIL~ (nreverse a)))))                                            ; 116
                                                                                              ; 117
)                                       ; End of eval-when                                    ; 118
                                                                                  ; Page 3:2  ; [sic. no line number]
(eval-when (eval load compile)          ; Start another eval-when, since the following        ; 119
                                        ; needs to be read in using 3-READ                    ; 120
                                                                                              ; 121
;;; BACKQUOTE    3-BACKQ-MACRO and 3-COMMA-MACRO are run on reading: they                       122
;;; ---------    put calls to ~3-BACKQUOTE and ~3-COMMA into the structures                     123
;;;              they build, which are then run on exit.  This allows the                       124
;;;              expansion to happen from the inside out.                                       125
                                                                                              ; 126
(defun 3-backq-macro (stream)                                                                 ; 127
   (let ((3=backquote-depth (1+ 3=backquote-depth)))                                          ; 128
      (macroexpand (list '~3-BACKQUOTE (read stream)))))                                      ; 129
                                                                                              ; 130
(defun 3-comma-macro (stream)                                                                 ; 131
   (if (< 3=backquote-depth 1) (3-error '|Unscoped comma|))                                   ; 132
   (let ((3=backquote-depth (1- 3=backquote-depth)))                                          ; 133
      (cons '~3-COMMA (read stream))))                                                        ; 134
                                                                                              ; 135
;;; The second argument to the next 3 procedures is a flag: NIL if the                          136
;;; backquote was at this level; T is not (implying that coalescing can                         137
;;; happen if possible).                                                                        138
                                                                                              ; 139
(defun 3-expand (x f)                                                                         ; 140
   (caseq (3-type x)                                                                          ; 141
      (PAIR (3-expand-pair x f))                                                              ; 142
      (RAIL (3-expand-rail x f))                                                              ; 143
      (T ↑x)))                                                                                ; 144
                                                                                              ; 145
(defun 3-expand-pair (x f)                                                                    ; 146
   (cond ((eq (car x) '~3-COMMA) (cdr x))       ; Found a ",<expr>".                          ; 147
         ((eq (car x) '~3-BACKQUOTE)            ; Recursive use of backq, so                  ; 148
          (3-expand (macroexpand x) f))         ; expand the inner one of then                ; 149
         (t (let ((a (3-expand (car x) t))      ; this one.                                   ; 150
                  (d (3-expand (cdr x) t)))                                                   ; 151
               (if (and f (3-handle a) (3-handle d))                                          ; 152
                   ↑(cons (cdr a) (cdr d))      ; Do the cons now if possible;                ; 153
                   `\(PCONS ~,a ~,d))))))       ; else use MACLISP's backquote                ; 154
                                                ; to form a call to PCONS.                    ; 155
                                                                                              ; 156
(defun 3-expand-rail (rail f)                                                                 ; 157
   (do ((rail (3-strip rail) (3-strip rail))                                                  ; 158
        (elements nil (cons (3-expand (car rail) t) elements)))                               ; 159
       ((null rail)                                                                           ; 160
        (if (and f (apply 'and (mapcar '3-handle elements)))                                  ; 161
            ↑(cons '~RAIL~ (mapcar 'cdr (nreverse elements)))                                 ; 162
            `(RCONS ~RAIL~ ,@(nreverse elemenets))))))                                        ; 163
                                                                                              ; 164
)                                                 ; end of eval-when                          ; 165
                                                                                  ; Page 3:3  ; [sic. no line number]
                                                                                              ; 166
;;; 3-PRINT    Print out <exp> in 3-LISP notation using notational sugar if                     167
;;; -------    possible.  No preliminary CR is printed (use TERPRI).  Some                      168
;;;            attempt is made to avoid printing known circular structures                      169
;;;            (like <SIMPLE> and <REFLECT> and obvious circular environments                   170
;;;            of a sort that would be generated by Z).                                         171
                                                                                              ; 172
(defun 3-print (exp)                                                                          ; 173
   (caseq (3-type exp)                                                                        ; 174
      (numeral (princ exp))                                                                   ; 175
      (boolean (princ exp))                                                                   ; 176
      (atom    (if (memq exp 3=simple-aliases)                                                ; 177
                   (princ '<simple>)                                                          ; 178
                   (prin1 exp)))                                                              ; 179
      (handle  (princ '|'|) (3-print !exp))                                                   ; 180
      (pair    (cond ((eq exp 3=simple-closure) (princ '<simple>))                            ; 181
                     ((eq exp 3=reflect-closure) (princ '<reflect>))                          ; 182
                     (t (princ '|(|)                                                          ; 183
                        (3-print (car exp))                                                   ; 184
                        (if (3-rail (cdr exp))                                                ; 185
                            (if (3-circular-closure-p exp)                                    ; 186
                                (progn (princ '| <circular-env>|)                             ; 187
                                       (3-print-elements (cddr exp) 't))                      ; 188
                                (3-print-elements (cdr exp) 't))                              ; 189
                            (princ '| . |) (3-print (cdr exp)))                               ; 190
                        (princ '|)|))))                                                       ; 191
      (rail    (princ '|[|)                                                                   ; 192
               (3-print-elements exp 'nil)                                                    ; 193
               (princ '|]|))))                                                                ; 194
                                                                                              ; 195
(defun 3-print-elements (list flag)                                                           ; 196
   (let ((global (3-strip 3=global-environment)))                                             ; 197
        (do ((list (3-strip list) (3-strip list))                                             ; 198
             (flag flag 't))                                                                  ; 199
            ((null list))                                                                     ; 200
            (if (eq list global)                                                              ; 201
                (return (princ '| ... <global>|)))                                            ; 202
            (if flag (princ '| |))                                                            ; 203
            (3-print (car list)))))                                                           ; 204
                                                                                              ; 205
(defun 3-prompt (level)                                                                       ; 206
   (terpri)                                                                                   ; 207
   (princ level)                                                                              ; 208
   (princ '|> |))                                                                             ; 209
                                                                                              ; 210
(defun 3-circular-closure-p (exp)                                                             ; 211
   (and (< 0 (3-length (cdr exp)))                                                            ; 212
        (3-rail (3r-1st (cdr exp)))                                                           ; 213
        (< 0 (3-length (3r-1st (cdr exp))))                                                   ; 214
        (let ((env? (3r-1st (3r-1st (cdr exp)))))                                             ; 215
            (and (3-rail env?)                                                                ; 216
                 (< 1 (3-length env?))                                                        ; 217
                 (3-handle (3r-1st env?))                                                     ; 218
                 (3-atom !(3r-1st env?))                                                      ; 219
                 (3-handle (3r-2nd env?))                                                     ; 220
                 (eq exp !(3r-2nd env?))))))                                                  ; 221
                                                                                              ; 222
                                                                                  ; Page 4    ; [sic. no line number]
                                                                                              ; 001
;;; Main Processor:                                                                             002
;;; ===============                                                                             003
;;;                                                                                             004
;;;                                                                                             005
;;; 3-NORMALISE and 3-REDUCE    The second clause in the following takes care                   006
;;; ------------------------    of numerals, booleans, handles, normal-form                     007
;;;                             function designators (applications in term of                   008
;;; the functions SIMPLE, MACRO, and REFLECT whose args are in normal form),                    009
;;; and normal-form sequence designators (rails whose elements are all in                       010
;;; normal-form).  Thus all normal-form expressions normalise to themselves,                    011
;;; even those (like rails and function designators) that are not canonical                     012
;;; designators of their referents.                                                             013
                                                                                              ; 014
(defun 3-normalise (exp env cont)                                                             ; 015
   (cond ((3-atom exp) (3-apply cont (3-binding exp env)))                                    ; 016
         ((3-normal exp) (3-apply cont exp))                                                  ; 017
         ((3-rail exp) (3-normalise-rail exp env cont))                                       ; 018
         (t (3-reduce (car exp) (cdr exp) env cont))))                                        ; 019
                                                                                              ; 020
(defun 3-reduce (proc args env cont)                                                          ; 021
   (3-normalise* proc env                                                                     ; 022
      `\(~~C0~ [['proc ~,↑proc] ['args ~,↑args] ['env ~,↑env] ['cont ~,↑cont]]  ; C0          ; 023
               '[proc*]                                                                       ; 024
               '(selectq (procedure-type proc*)                                               ; 025
                  [reflect ((simple . !(cdr proc*)) args env cont)]                           ; 026
                  [simple (normalise args env (make-c1 proc* cont))]))))                      ; 027
                                                                                              ; 028
;;; 3-NORMALISE-RAIL    Normalise (the first element of) a rail.                                029
;;; ----------------                                                                            030
                                                                                              ; 031
(defun 3-normalise-rail (rail env cont)                                                       ; 032
   (if (null (3-strip rail))                                                                  ; 033
       (3-apply cont rail)                                                                    ; 034
       (3-normalise* (3r-1st rail) env                                                        ; 035
          `\(~~C2~ [['rail ~,↑rail] [`env ~,↑env] [`cont ~,↑cont]]              ; C2          ; 036
                   '[element*]                                                                ; 037
                   '(normalise-rail (rest tail) env                                           ; 038
                       (lambda simple [rest*]                                                 ; 039
                         (cont (prep element* rest*))))))))                                   ; 040
                                                                                              ; 041
;;; 3-PRIMITIVE-REDUCE-SIMPLE  The way each primitive function is treated is                    042
;;; -------------------------  highly dependent on the way that 3-LISP                          043
;;;                            structures are encoded in MACLISP                                044
                                                                                              ; 045
(defun 3-primitive-reduce-simple (proc args cont)                                             ; 046
  (3-rail-check args)                                                                         ; 047
  (if (eq proc 'referent)                                                                     ; 048
      (3-normalise* !(3r-1st args) (3r-2nd args) cont)                                        ; 049
      (3-apply cont                                                                           ; 050
        (caseq proc                                                                           ; 051
          (simple   `(,3=simple-closure . ,args))                                             ; 052
          (reflect  `(,3=reflect-closure . ,args))                                            ; 053
          (type     ↑(3-ref-type (3r-1st args)))                                              ; 054
          (ef       (if (eq (3-bool-check (3r-1st args)) '$T)                                 ; 055
                        (3r-2nd args) (3r-3rd args)))                                         ; [sic. no line number]
          (pcons    ↑(cons !(3r-1st args) !(3r-2nd args)))                                    ; 056
          (car      ↑(car (3-pair-check !(3r-1st args))))                                     ; 057
          (cdr      ↑(cdr (3-pair-check !(3r-1st args))))                                     ; 058
          (length   (3-length (3r-1st args)))                                                 ; 059
          (nth      (3-nth (3r-1st args) (3r-2nd args)))                                      ; 060
          (tail     (3-tail (3r-1st args) (3r-2nd args)))                                     ; 061
          (prep     (3-prep (3r-1st args) (3r-2nd args)))                                     ; 062
          (rcons    (3-rcons (3-rail-check args)))                                            ; 063
          (scons    (3-scons (3-rail-check args)))                                            ; 064
          (rplaca   ↑(rplaca (3-pair-check !(3r-1st args)) !(3r-2nd args)))                   ; 065
          (rplacd   ↑(rplacd (3-pair-check !(3r-1st args)) !(3r-2nd args)))                   ; 066
          (rplacn   ↑(3-rplacn (3r-1st args) !(3r-2nd args) !(3r-3rd args)))                  ; 067
          (rplact   ↑(3-rplact (3r-1st args) !(3r-2nd args) !(3r-3rd args)))                  ; 068
	                                                                          ; Page 4:1  ; [sic. no line number]
          (=        (if (3-equal (3r-1st args) (3r-2nd args)) '$T '$F))                       ; 069
          (read     ↑(3-read))                                                                ; 070
          (print    (3-print !(3r-1st args)) (princ '/ ) '$T)                                 ; 071
          (terpri   (terpri) '$T)                                                             ; 072
          (+        (+ (3-num-check (3r-1st args)) (3-num-check (3r-2nd args))))              ; 073
          (*        (* (3-num-check (3r-1st args)) (3-num-check (3r-2nd args))))              ; 074
          (-        (- (3-num-check (3r-1st args)) (3-num-check (3r-2nd args))))              ; 075
          (//       (// (3-num-check (3r-1st args)) (3-num-check (3r-2nd args))))             ; 076
          (name     ↑(3r-1st args))                                                           ; 077
          (*rebind  (3-rebind !(3r-1st args) (3r-2nd args) (3r-3rd args)))  ; for             ; 078
          (level    3=level)                                                ; efficiency      ; 079
          (t (3-implementation-error))))))                                                    ; 080
                                                                                  ; Page 5    ; 001
;;; Continuation Application:                                                                   002
;;; =========================                                                                   003
;;;                                                                                             004
;;; 3-APPLY   Called with 3-LISP continuations, has to sort them out and do                     005
;;; -------   the right non-reflected thing with those that are tokens of the                   006
;;;           six types (C0 - C5) that are primitively recognized.  In                          007
;;; addition, redexes in terms of primitive procedures (identified by PRIM)                     008
;;; are recognised.  We assume a continuation of the form                                       009
;;; (<simple> . [env [arg] body]), and a standard environment structure.                        010
                                                                                              ; 011
(defmacro 3a-env (cont) `(3r-1st (cdr ,cont)))                                                ; 012
(defmacro 3a-arg (cont) `(3r-2nd (cdr ,cont)))                                                ; 013
(defmacro 3a-1st (env)  `!(3r-2nd (3r-1st ,env)))                                             ; 014
(defmacro 3a-2nd (env)  `!(3r-2nd (3r-2nd ,env)))                                             ; 015
(defmacro 3a-3rd (env)  `!(3r-2nd (3r-3rd ,env)))                                             ; 016
(defmacro 3a-4th (env)  `!(3r-2nd (3r-4th ,env)))                                             ; 017
                                                                                              ; 018
(defun 3-apply (cont normal-form)                                                             ; 019
  (let ((env (3a-env cont)))                                                                  ; 020
    (if (memq (car cont) 3=simple-aliases)                                                    ; 021
        (funcall (car cont) env cont normal-form)                                             ; 022
        (let ((new-level (3-increment-level)))    ; REFLECT UP!                               ; 023
           (3-reduce cont ↑`\[~,normal-form]      ; ===========                               ; 024
                     (car new-level) (cdr new-level))))))                                     ; 025
                                                                                              ; 026
;;; C0:  Accept a normalised function designator from a pair.  Dispatch                         027
;;; ---  on the function type: if it is SIMPLE, normalise the args; if                          028
;;;      primitive reflective, go do it; otherwise reflect up explicitly.                       029
                                                                                              ; 030
(defun ~C0~ (env cont proc)                                                                   ; 031
  ignore cont                                                                                 ; 032
  (let ((args (3a-2nd env))                                                                   ; 033
        (env  (3a-3rd env))                                                                   ; 034
        (cont (3a-4th env)))                                                                  ; 035
     (caseq (3-proc-type proc)                                                                ; 036
       (simple (3-normalise* args env                                                         ; 037
                 `\(~~C1~ [['proc ~,↑proc] ['args ~,↑args]      ; C1                          ; 038
                           ['env ~,↑env] ['cont ~,↑cont]]                                     ; 039
                          '[args*]                                                            ; 040
                          '(cond [(= proc* ↑referent)                                         ; 041
                                 (normalise !(1st args) !(2nd args) cont)]                    ; 042 [sic. indentation]
                                 [(primitive proc*) (cont ↑(!proc* . !args*))]                ; 043
                                 [$T (normalise (body proc*)                                  ; 044
                                                (bind (pattern proc*) args* (env proc*))      ; 045
                                                cont)]))))                                    ; 046 [sic. indentation]
       (reflect (let ((nlevel (3-increment-level))      ; REFLECT UP!                         ; 047
                      (proc (cdr proc)))                ; ===========                         ; 048
                  (3-normalise* !(3r-3rd proc)                                                ; 049
                                (3-bind !(3r-2nd proc)                                        ; 050
                                        `\[~,↑args ~,env ~,cont]                              ; 051
                                        (3r-1st proc))                                        ; 052
                                (cdr nlevel)))))))                                            ; 053
                                                                                  ; Page 5:1  ; [sic. no line number]
                                                                                              ; 054
;;; C1:  Accept the normalised arguments to a SIMPLE application.  Dispatch                     055
;;; ---  on primitives, and reflect down in case we encounter a call to a                       056
;;;      continuation we ourselves once put together.  Also trap explicit calls                 057
;;;      to NORMALISE and REDUCE, for efficinecy.                                               058
                                                                                              ; 059
(defun ~C1~ (env cont args*)                                                                  ; 060
   ignore cont                                                                                ; 061
   (let ((proc (3a-1st env)))                                                                 ; 062
      (cond ((eq (car proc) '~PRIM~)                                                          ; 063
             (3-argument-check args* proc)                                                    ; 064
             (3-primitive-reduce-simple (3-primitive-simple-id proc)                          ; 065
                                        args*                                                 ; 066
                                        (3a-4th env)))                                        ; 067
            ((memq (car proc) 3=simple-aliases)                                               ; 068
             (3-drop-level (3a-3rd env) (3a-4th env))           ; REFLECT DOWN                ; 069
             (3-apply proc !(3r-1st args*)))                    ; ============                ; 070
            ((eq proc 3=normal-closure)                                                       ; 071
             (3-drop-level (3a-3rd env) (3a-4th))               ; REFLECT DOWN                ; 072
             (3-normalise* !(3r-1st args*)                      ; ============                ; 073
                           (3r-2nd args*)                                                     ; 074
                           (3r-3rd args*)))                                                   ; 075
            ((eq proc 3=reduce-closure)                                                       ; 076
             (3-drop-level (3a-3rd env) (3a-4th env))           ; REFLECT DOWN                ; 077
             (3-reduce !(3r-1st args*)                          ; ============                ; 078
                       !(3r-2nd args*)                                                        ; 079
                       (3r-3rd args*)                                                         ; 080
                       (3r-4th args*)))                                                       ; 081
            (t (let ((proc* (cdr proc)))                                                      ; 082
                  (3-normalise*                                                               ; 083
                        !(3r-3rd proc*)                                                       ; 084
                        (3-bind !(3r-2nd proc*) args* (3r1st proc*))                          ; 085
                        (3a-4th env)))))))                                                    ; 086
                                                                                              ; 087
;;; C2:  Accept the normalised first element in a rail fragment.                                088
;;; ---  Normalise the rest.                                                                    089
                                                                                              ; 090
(defun ~C2~ (env cont element*)                                                               ; 091
   ignore cont                                                                                ; 092
   (3-normalise-rail                                                                          ; 093
        (3-tail* 1 (3a-1st env))                                                              ; 094
        (3a-2nd env)                                                                          ; 095
        `\(~~C3~ ~,(nconc `\[['element* ~,↑element*]] env)      ; C3                          ; 096
                 '[rest*]                                                                     ; 097
                 '(cont (prep element* rest*)))))                                             ; 098
                                                                                              ; 099
;;; C3:  Accept the normalised tail of a rail fragment.  Put the first                          100
;;; ---  element on the front.                                                                  101
                                                                                              ; 102
(defun ~C3~ (env cont rest*)                                                                  ; 103
   ignore cont                                                                                ; 104
   (3-apply (3a-4th env) (nconc `\[~,(3a-1st env)] rest*)))                                   ; 105
                                                                                              ; 106
;;; C4:  Accept an expression normalised for the top level of a                                 107
;;; ---  READ-NORMALISE-PRINT loop.  Print it out and read another.                             108
;;;                                                                                             109
;;; On entry here ENV will be bound to the environment of the C4 closure, CONT                  110
;;; will be bound to the whole C4 closure, and NORMAL-FORM will be bound to a                   111
;;; designator of the result of the NORMALISE at the level below.                               112
                                                                                              ; 113
(defun ~C4~ (env cont normal-form)                                                            ; 114
   (3-prompt 3=level)                                                                         ; 115
   (3-print !normal-form)                                                                     ; 116
   (3-prompt 3=level)                                                                         ; 117
   (3-drop-level 3=global-environment cont)                                                   ; 118
   (3-normalise* (3-read) (3-binding 'env env) 3=id-closure))                                 ; 119
                                                                                              ; 120
;;; C5:  Accept the result of normalising an expression wrapped in an                           121
;;; ---  IN-3-LISP macro.  Return answer to the caller.                                         122
                                                                                              ; 123
(defun ~C5~ (env cont normal-form)                                                            ; 124
   ignore env cont                                                                            ; 125
   (*throw '3-exit normal-form))                                                              ; 126
                                                                                              ; 127
(defun 3-argument-check (args proc)                                                           ; 128
  (let ((pattern !(3r-2nd (cdr proc))))                                                       ; 129
    (if (and (3-rail pattern)                                                                 ; 130
             (not (= (3-length args) (3-length pattern))))                                    ; 131
        (3-error '|Wrong number of arguments to a primitive: |                                ; 132
                 `\(~,(car !(3r-3rd proc)) . ~,args)))))                                      ; 133
                                                                                              ; 134
                                                                                  ; Page 6    ; 001
;;; Environments:                                                                               002
;;; =============                                                                               003
;;;                                                                                             004
;;; 3-BINDING   Look up a binding in a 3-LISP standard environment                              005
;;; ---------   designator, but, for efficiency, bypass rail type-checking.                     006
                                                                                              ; 007
(defun 3-binding (var env)                                                                    ; 008
   (3-atom-check var)                                                                         ; 009
   (3-rail-check env)                                                                         ; 010
   (do ((env (3-strip env) (3-strip env)))                                                    ; 011
       ((null env) (3-error `(,var unbound variable -- BINDING)))                             ; 012
      (if (eq var !(3r-1st (car env))) (return !(3r-2nd (car env))))))                        ; 013
                                                                                              ; 014
;;; 3-BIND   Bind variable structure to argument structure.  Destructures on                    015
;;; ------   rails and sequences.  For efficiency, does rail manipulation by                    016
;;;          itself, saving time and cons'es.  The DO constructs a reversed                     017
;;;          MACLISP rail designator, NREVERSEd on exit.                                        018
                                                                                              ; 019
(defun 3-bind* (pattern vals)                                                                 ; 020
  (caseq (3-type pattern)                                                                     ; 021
    (atom `(\[~,↑pattern ~,↑vals]))                                                           ; 022
    (rail (caseq (3-type vals)                                                                ; 023
           (rail (do ((binds nil (nconc (3-bind* (car pattern) (car vals)) binds))            ; 024
                      (pattern (3-strip pattern) (3-strip pattern))                           ; 025
                      (vals (3-strip vals) (3-strip vals)))                                   ; 026
                     ((or (null pattern) (null vals))                                         ; 027
                      (cond ((and (null pattern) (null vals))                                 ; 028
                             (nreverse binds))                                                ; 029
                            ((null vals) (3-error '|Too few arguments supplied|))             ; 030
                            (t (3-error '|Too many arguments supplied|))))))                  ; 031
           (handle (if (3-rail !vals)                                                         ; 032
                       (do ((binds nil (nconc (3-bind* (car pattern) ↑(car vals))             ; 033
                                              binds))                                         ; 034
                            (pattern (3-strip pattern) (3-strip pattern))                     ; 035
                            (vals (3-strip !vals) (3-strip vals)))                            ; 036
                           ((or (null pattern) (null vals))                                   ; 037
                            (cond ((and (null pattern) (null vals))                           ; 038
                                   (nreverse binds))                                          ; 039
                                  ((null vals) (3-error '|Too few arguments supplied|))       ; 040
                                  (t (3-error '|Too many arguments supplied|)))))             ; 041
                       (3-type-error vals '|ATOM, RAIL, or RAIL DESIGNATOR|)))                ; 042
           (t (3-type-error vals '|ATOM, RAIL, or RAIL DESIGNATOR|))))                        ; 043
    (t (3-type-error vals '|ATOM, RAIL, or RAIL DESIGNATOR|))))                               ; 044
                                                                                              ; 045
(defun 3-rebind (var binding env)                                                             ; 046
   (3-atom-check var)                                                                         ; 047
   (3-rail-check env)                                                                         ; 048
   (if (not (3-normal binding))                                                               ; 049
       (3-error '(binding not in normal form -- REBIND/:) binding))                           ; 050
   (do ((env (3-strip* env) (3-strip* (cdr env))))                                            ; 051
       ((null (cdr env)) (nconc env `\[[~,↑val ~,binding]]))                                  ; 052
      (if (eq var !(3r-1st (cadr env)))                                                       ; 053
          (return (3-rplacn 2 (cadr env) binding))))                                          ; 054
   binding)                                                                                   ; 055
                                                                                              ; 056
                                                                                  ; Page 7    ; 001
;;; Reflective state management:                                                                002
;;; ============================                                                                003
;;;                                                                                             004
;;; 3-STATES is a queue of the environment and continuation of each reflective                  005
;;; level ABOVE the current one (the value of 3=LEVEL), if they were ever                       006
;;; explicitly generated (all relevant ones BELOW the current level are of                      007
;;; course being passed around explicitly in 3-LISP programs).                                  008
                                                                                              ; 009
(defun 3-drop-level (env cont)                                                                ; 010
   (push (cons env cont) 3=states)                                                            ; 011
   (setq 3=level (1- 3=level)))                                                               ; 012
                                                                                              ; 013
(defun 3-increment-level ()                                                                   ; 014
   (setq 3=level (1+ 3=level))                                                                ; 015
   (if (not (null 3=states))                                                                  ; 016
       (pop 3=states)                                                                         ; 017
       (cons 3=global-environment                                                             ; 018
             `\(~~C4~ ~,(nconc `\[['env ~,↑3=global-environment]]                             ; 019
                               3=global-environment)                                          ; 020
                      '[normal-form]                                                          ; 021
                      '(block (prompt (level))                                                ; 022
                              (print normal-form)                                             ; 023
                              (read-normalise-print env))))))                                 ; 024
                                                                                              ; 025
                                                                                  ; Page 8    ; 001
;;; Rail Management:                                                                            002
;;; ================                                                                            003
;;;                                                                                             004
;;;                                                                                             005
;;; 3-RCONS   Make a new rail (or sequence designator) out of the args                          006
;;; 3-SCONS                                                                                     007
;;; -------                                                                                     008
                                                                                              ; 009
(defun 3-rcons (args)                                                                         ; 010
  (do ((args (3-strip (3-rail-check args)) (3-strip args))                                    ; 011
       (new nil (cons !(car args) new)))                                                      ; 012
      ((null args) ↑(cons '~RAIL~ (nreverse new)))))                                          ; 013
                                                                                              ; 014
(defun 3-scons (args)                                                                         ; 015
  (do ((args (3-strip (3-rail-check args)) (3-strip args))                                    ; 016
       (new nil (cons (car args) new)))                                                       ; 017
      ((null args) (cons '~RAIL~ (nreverse new)))))                                           ; 018
                                                                                              ; 019
;;; 3-RS  Macro that takes two forms, one for rails and one for sequences,                      020
;;; ----  and wraps the appropariate type dispatch around them.                                 021
                                                                                              ; 022
(defmacro 3-rs (exp rail-form seq-form)                                                       ; 023
   `(caseq (3-type ,exp)                                                                      ; 024
       (handle ,rail-form)                                                                    ; 025
       (rail ,seq-form)                                                                       ; 026
       (t (3-ref-type-err ,exp '|RAIL OR SEQUENCE|))))                                        ; 027
                                                                                              ; 028
;;; 3-PREP      -- These four kinds are defined over both rails and sequences.                  029
;;; 3-LENGTH       They are all defined in terms of *-versions, which operate                   030
;;; 3-TAIL         on the implementing rails.                                                   031
;;; 3-NTH                                                                                       032
                                                                                              ; 033
(defun 3-prep (el exp)                                                                        ; 034
   (3-rs exp ↑(list* '~RAIL~ !el (3-rail-check !exp))                                         ; 035
              (list* '~RAIL el exp)))                                                         ; 036
                                                                                              ; 037
(defun 3-length (exp)                                                                         ; 038
   (3-rs exp (3-length* (3-rail-check !exp))                                                  ; 039
             (3-length* exp)))                                                                ; 040
                                                                                              ; 041
(defun 3-tail (n exp)                                                                         ; 042
   (3-rs exp ↑(3-tail* n (3-rail-check !exp))                                                 ; 043
              (3-tail* n exp)))                                                               ; 044
                                                                                              ; 045
(defun 3-nth (n exp)                                                                          ; 046
   (3-rs exp ↑(car (3-nthcdr* n (3-rail-check !exp)))                                         ; 047
              (car (3-nthcdr* n exp))))                                                       ; 048
                                                                                              ; 049
;;; 3-RPLACN   Defined onlu on RAILS.                                                           050
;;; --------                                                                                    051
                                                                                              ; 052
(defun 3-rplacn (n rail el)                                                                   ; 053
   (rplacn (3-nthcdr* n (3-rail-check rail)) el)                                              ; 054
   rail)                                                                                      ; 055
                                                                                              ; 056
(defun 3-nthcdr* (n rail)                                                                     ; 057
   (if (< n 1) (3-index-error n rail))                                                        ; 058
   (do ((i 1 (1+ i))                                                                          ; 059
        (rest (3-strip rail) (3-strip rest)))                                                 ; 060
       ((or (= n i) (null rest))                                                              ; 061
        (if (null rest)                                                                       ; 062
            (3-index-error n rail)                                                            ; 063
            rest))))                                                                          ; 064
                                                                                  ; Page 8:1  ; 065
(defun 3-tail* (n o-rail)                                                                     ; 066
  (if (< n 0) (3-index-error n o-rail))                                                       ; 067
  (if (zerop n)                                                                               ; 068
      o-rail                                                                                  ; 069
      (do ((i 0 (1+ i))                                                                       ; 070
           (rail (3-strip* o-rail) (3-strip* (cdr rail))))                                    ; 071
          ((or (= n i) (null (cdr rail)))                                                     ; 072
           (if (= n i)                                                                        ; 073
               (if (eq (car rail) '~RAIL~)                                                    ; 074
                   rail                                                                       ; 075
                   (let ((tail (cons '~RAIL~ (cdr rail))))                                    ; 076
                     (rplacd rail tail) ; Splice in a new header                              ; 077
                     tail))                                                                   ; 078
               (3-error `(,n is too large for a tail of) o-rail))))))                         ; 079
                                                                                              ; 080
;;; RPLACT is what all the trouble is about.  A tempting implementation is:                     081
;;;                                                                                             082
;;;   (defmacro 3-rplact (n r1 r2) `(cdr (rplacd (3-tail ,n ,r1) ,r2)))                         083
;;;                                                                                             084
;;; but this has two problems.  First, it can generate an unnecessary header,                   085
;;; since 3-TAIL may construct one, even though r2 is guaranteed to have one                    086
;;; already.  Second, some uses of this (such as (RPLACT 1 X X)) would generate                 087
;;; circular structures.  The following version avoids these problems:                          088
                                                                                              ; 089
(defun 3-rplact (n r1 r2)                                                                     ; 090
   (3-rail-check r1)                                                                          ; 091
   (3-rail-check r2)                                                                          ; 092
   (if (< n 0) (3-index-error n r1))                                                          ; 093
   (do ((i 0 (1+ i))                                                                          ; 094
        (last r1 rail)                                                                        ; 095
        (rail (3-strip* r1) (3-strip* (cdr rail))))                                           ; 096
       ((or (= n 1) (null (cdr rail)))                                                        ; 097
        (progn                                                                                ; 098
         (if (not (= n i)) (3-index-error n r1))                                              ; 099
         (if (let ((r2-headers (do ((r2 r2 (cdr r2))                                          ; 100
				    (heads nil (cons r2 heads)))                              ; 101
				   ((not (eq (car r2) '~RAIL~)) heads))))                     ; 102
	       (do ((r1-header (cdr last) (cdr r1-header)))                                   ; 103
		   ((not (eq (car r1-header) '~RAIL~)) 't)                                    ; 104
		 (if (memq r1-header r2-headers) (return 'nil))))                             ; 105
	     (rplacd rail r2))                                                                ; 106
	 r1))))                                                                               ; 107
                                                                                              ; 108
                                                                                  ; Page 9    ; 001
;;; Typing and Type Checking:                                                                   002
;;; =========================                                                                   003
                                                                                              ; 004
(eval-when (load eval compile)                  ; Backquote needs this                        ; 005
                                                                                              ; 006
(defun 3-type (exp)                                                                           ; 007
    (cond ((fixp exp) 'numeral)                                                               ; 008
          ((memq exp '($T $F)) 'boolean)                                                      ; 009
          ((symbolp exp) 'atom)                                                               ; 010
          ((eq (car exp) '~RAIL~) 'rail)                                                      ; 011
          ((eq (car exp) '~QUOTE~) 'handle)                                                   ; 012
          (t 'pair)))                                                                         ; 013
                                                                                              ; 014
)                                               ; end of eval-when                            ; 015
                                                                                              ; 016
;;; 3-boolean and 3-numeral are macros, defined above.                                          017
                                                                                              ; 018
(defun 3-atom (e) (and (symbolp e) (not (memq e '($T $F)))))                                  ; 019
(defun 3-rail (e) (and (list? e) (eq (car e) '~RAIL~)))                                       ; 020
(defun 3-pair (e) (eq (3-type e) 'pair))                                                      ; 021
                                                                                              ; 022
(eval-when (load eval compile)                                                                ; 023
(defun 3-handle (e)  (and (list? e) (eq (car e) '~QUOTE~)))                                   ; 024
)                                                                                             ; 025
                                                                                              ; 026
(defun 3-atom-check   (e) (if (3-atom e)    e (3-type-error e 'atom)))                        ; 027
(defun 3-rail-check   (e) (if (3-rail e)    e (3-type-error e 'rail)))                        ; 028
(defun 3-pair-check   (e) (if (3-pair e)    e (3-type-error e 'pair)))                        ; 029
(defun 3-handle-check (e) (if (3-handle e)  e (3-type-error e 'handle)))                      ; 030
(defun 3-num-check    (e) (if (3-numeral e) e (3-type-error e 'numeral)))                     ; 031
(defun 3-bool-check   (e) (if (3-boolean e) e (3-type-error e 'boolean)))                     ; 032
                                                                                              ; 033
;;; 3-REF-TYPE   Returns the type of the entity designated by the 3-LISP                        034
;;; ----------   object encoded as the argument.                                                035
                                                                                              ; 036
(defun 3-ref-type (exp)                                                                       ; 037
  (caseq (3-type exp)                                                                         ; 038
    (numeral 'number)                                                                         ; 039
    (boolean 'truth-value)                                                                    ; 040
    (rail    'sequence)                                                                       ; 041
    (handle  (3-type (cdr exp)))                                                              ; 042
    (pair    (if (or (eq (car exp) 3=simple-closure)                                          ; 043
                     (eq (car exp) 3=reflect-closure)                                         ; 044
                     (memq (car exp) 3=simple-alises))                                        ; 045
                 'function                                                                    ; 046
                 (3-error '(not in normal form -- REF-TYPE/:) exp)))                          ; 047
    (atom    (3-error '(not in normal form -- REF-TYPE/:) exp))))                             ; 048
                                                                                              ; 049
;;; 3-REF   Returns the referent of the argument, which must either be a                        050
;;; -----   handle or a rail of handles, since the only kinds of ref's we                       051
;;;         can return are s-expressions.                                                       052
                                                                                              ; 053
(defun 3-ref (exp)                                                                            ; 054
  (cond ((3-handle exp) (cdr exp))                                                            ; 055
        ((3-rail exp)                                                                         ; 056
         (do ((rail (3-strip exp) (3-strip rail))                                             ; 057
              (elements nil (cons !(car rail) elements)))                                     ; 058
             ((null rail) (cons '~RAIL~ (nreverse elements)))                                 ; 059
           (if (not (3-handle (car rail)))                                                    ; 060
               (3-ref-type-error exp '|SEQUENCE OF S-EXPRESSIONS|))))                         ; 061
        (t (3-ref-type-error exp '|S-EXPRESSION OR SEQUENCE OF S-EXPRESSIONS|))))             ; 062
                                                                                              ; 063
;;; 3-PROC-TYPE   Returns the procedure type of the argument                                    064 [sic. no full stop]
;;; -----------                                                                                 065
                                                                                              ; 066
(defun 3-proc-type (proc)                                                                     ; 067
  (3-pair-check proc)                                                                         ; 068
  (cond ((eq (car proc) 3=simple-closure) 'simple)                                            ; 069
        ((memq (car proc) 3=simple-aliases) 'simple)                                          ; 070
        ((eq (car proc) 3=reflect-closure) 'reflect)                                          ; 071
        (t (3-type-error proc 'closure))))                                                    ; 072
;;;                                                                               ; Page 10   ; 001
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

