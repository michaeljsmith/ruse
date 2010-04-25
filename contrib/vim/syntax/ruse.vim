" This script incorrectly recognizes some junk input as numerals:
" parsing the complete system of Scheme numerals using the pattern
" language is practically impossible: I did a lax approximation.
 
" Initializing:

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

syn case ignore

" Fascist highlighting: everything that doesn't fit the rules is an error...

syn match	ruseError	oneline    ![^ \t()\[\]";]*!
syn match	ruseError	oneline    ")"

" Quoted and backquoted stuff

syn region ruseQuoted matchgroup=Delimiter start="['`]" end=![ \t()\[\]";]!me=e-1 contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

syn region ruseQuoted matchgroup=Delimiter start="['`](" matchgroup=Delimiter end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseQuoted matchgroup=Delimiter start="['`]#(" matchgroup=Delimiter end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

syn region ruseStrucRestricted matchgroup=Delimiter start="(" matchgroup=Delimiter end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseStrucRestricted matchgroup=Delimiter start="#(" matchgroup=Delimiter end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

" Popular Scheme extension:
" using [] as well as ()
syn region ruseStrucRestricted matchgroup=Delimiter start="\[" matchgroup=Delimiter end="\]" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseStrucRestricted matchgroup=Delimiter start="#\[" matchgroup=Delimiter end="\]" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

syn region ruseUnquote matchgroup=Delimiter start="," end=![ \t\[\]()";]!me=e-1 contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseUnquote matchgroup=Delimiter start=",@" end=![ \t\[\]()";]!me=e-1 contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

syn region ruseUnquote matchgroup=Delimiter start=",(" end=")" contains=ALL
syn region ruseUnquote matchgroup=Delimiter start=",@(" end=")" contains=ALL

syn region ruseUnquote matchgroup=Delimiter start=",#(" end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseUnquote matchgroup=Delimiter start=",@#(" end=")" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

syn region ruseUnquote matchgroup=Delimiter start=",\[" end="\]" contains=ALL
syn region ruseUnquote matchgroup=Delimiter start=",@\[" end="\]" contains=ALL

syn region ruseUnquote matchgroup=Delimiter start=",#\[" end="\]" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc
syn region ruseUnquote matchgroup=Delimiter start=",@#\[" end="\]" contains=ALLBUT,ruseStruc,ruseSyntax,ruseFunc

" R5RS Scheme Functions and Syntax:

if version < 600
  set iskeyword=33,35-39,42-58,60-90,94,95,97-122,126,_
else
  setlocal iskeyword=33,35-39,42-58,60-90,94,95,97-122,126,_
endif

syn keyword ruseSyntax lambda and or if cond case define let let* letrec
syn keyword ruseSyntax begin do delay set! else =>
syn keyword ruseSyntax quote quasiquote unquote unquote-splicing
syn keyword ruseSyntax define-syntax let-syntax letrec-syntax syntax-rules

syn keyword ruseFunc not boolean? eq? eqv? equal? pair? cons car cdr set-car!
syn keyword ruseFunc set-cdr! caar cadr cdar cddr caaar caadr cadar caddr
syn keyword ruseFunc cdaar cdadr cddar cdddr caaaar caaadr caadar caaddr
syn keyword ruseFunc cadaar cadadr caddar cadddr cdaaar cdaadr cdadar cdaddr
syn keyword ruseFunc cddaar cddadr cdddar cddddr null? list? list length
syn keyword ruseFunc append reverse list-ref memq memv member assq assv assoc
syn keyword ruseFunc symbol? symbol->string string->symbol number? complex?
syn keyword ruseFunc real? rational? integer? exact? inexact? = < > <= >=
syn keyword ruseFunc zero? positive? negative? odd? even? max min + * - / abs
syn keyword ruseFunc quotient remainder modulo gcd lcm numerator denominator
syn keyword ruseFunc floor ceiling truncate round rationalize exp log sin cos
syn keyword ruseFunc tan asin acos atan sqrt expt make-rectangular make-polar
syn keyword ruseFunc real-part imag-part magnitude angle exact->inexact
syn keyword ruseFunc inexact->exact number->string string->number char=?
syn keyword ruseFunc char-ci=? char<? char-ci<? char>? char-ci>? char<=?
syn keyword ruseFunc char-ci<=? char>=? char-ci>=? char-alphabetic? char?
syn keyword ruseFunc char-numeric? char-whitespace? char-upper-case?
syn keyword ruseFunc char-lower-case?
syn keyword ruseFunc char->integer integer->char char-upcase char-downcase
syn keyword ruseFunc string? make-string string string-length string-ref
syn keyword ruseFunc string-set! string=? string-ci=? string<? string-ci<?
syn keyword ruseFunc string>? string-ci>? string<=? string-ci<=? string>=?
syn keyword ruseFunc string-ci>=? substring string-append vector? make-vector
syn keyword ruseFunc vector vector-length vector-ref vector-set! procedure?
syn keyword ruseFunc apply map for-each call-with-current-continuation
syn keyword ruseFunc call-with-input-file call-with-output-file input-port?
syn keyword ruseFunc output-port? current-input-port current-output-port
syn keyword ruseFunc open-input-file open-output-file close-input-port
syn keyword ruseFunc close-output-port eof-object? read read-char peek-char
syn keyword ruseFunc write display newline write-char call/cc
syn keyword ruseFunc list-tail string->list list->string string-copy
syn keyword ruseFunc string-fill! vector->list list->vector vector-fill!
syn keyword ruseFunc force with-input-from-file with-output-to-file
syn keyword ruseFunc char-ready? load transcript-on transcript-off eval
syn keyword ruseFunc dynamic-wind port? values call-with-values
syn keyword ruseFunc ruse-report-environment null-environment
syn keyword ruseFunc interaction-environment

" ... so that a single + or -, inside a quoted context, would not be
" interpreted as a number (outside such contexts, it's a ruseFunc)

syn match	ruseDelimiter	oneline    !\.[ \t\[\]()";]!me=e-1
syn match	ruseDelimiter	oneline    !\.$!
" ... and a single dot is not a number but a delimiter

" This keeps all other stuff unhighlighted, except *stuff* and <stuff>:

syn match	ruseOther	oneline    ,[a-z!$%&*/:<=>?^_~+@#%-][-a-z!$%&*/:<=>?^_~0-9+.@#%]*,
syn match	ruseError	oneline    ,[a-z!$%&*/:<=>?^_~+@#%-][-a-z!$%&*/:<=>?^_~0-9+.@#%]*[^-a-z!$%&*/:<=>?^_~0-9+.@ \t\[\]()";]\+[^ \t\[\]()";]*,

syn match	ruseOther	oneline    "\.\.\."
syn match	ruseError	oneline    !\.\.\.[^ \t\[\]()";]\+!
" ... a special identifier

syn match	ruseConstant	oneline    ,\*[-a-z!$%&*/:<=>?^_~0-9+.@]*\*[ \t\[\]()";],me=e-1
syn match	ruseConstant	oneline    ,\*[-a-z!$%&*/:<=>?^_~0-9+.@]*\*$,
syn match	ruseError	oneline    ,\*[-a-z!$%&*/:<=>?^_~0-9+.@]*\*[^-a-z!$%&*/:<=>?^_~0-9+.@ \t\[\]()";]\+[^ \t\[\]()";]*,

syn match	ruseConstant	oneline    ,<[-a-z!$%&*/:<=>?^_~0-9+.@]*>[ \t\[\]()";],me=e-1
syn match	ruseConstant	oneline    ,<[-a-z!$%&*/:<=>?^_~0-9+.@]*>$,
syn match	ruseError	oneline    ,<[-a-z!$%&*/:<=>?^_~0-9+.@]*>[^-a-z!$%&*/:<=>?^_~0-9+.@ \t\[\]()";]\+[^ \t\[\]()";]*,

" Non-quoted lists, and strings:

syn region ruseStruc matchgroup=Delimiter start="(" matchgroup=Delimiter end=")" contains=ALL
syn region ruseStruc matchgroup=Delimiter start="#(" matchgroup=Delimiter end=")" contains=ALL

syn region ruseStruc matchgroup=Delimiter start="\[" matchgroup=Delimiter end="\]" contains=ALL
syn region ruseStruc matchgroup=Delimiter start="#\[" matchgroup=Delimiter end="\]" contains=ALL

" Simple literals:
syn region ruseString start=+\%(\\\)\@<!"+ skip=+\\[\\"]+ end=+"+

" Comments:

syn match	ruseComment	";.*$"


" Writing out the complete description of Scheme numerals without
" using variables is a day's work for a trained secretary...

syn match	ruseOther	oneline    ![+-][ \t\[\]()";]!me=e-1
syn match	ruseOther	oneline    ![+-]$!
"
" This is a useful lax approximation:
syn match	ruseNumber	oneline    "[-#+0-9.][-#+/0-9a-f@i.boxesfdl]*"
syn match	ruseError	oneline    ![-#+0-9.][-#+/0-9a-f@i.boxesfdl]*[^-#+/0-9a-f@i.boxesfdl \t\[\]()";][^ \t\[\]()";]*!

syn match	ruseBoolean	oneline    "#[tf]"
syn match	ruseError	oneline    !#[tf][^ \t\[\]()";]\+!

syn match	ruseChar	oneline    "#\\"
syn match	ruseChar	oneline    "#\\."
syn match       ruseError	oneline    !#\\.[^ \t\[\]()";]\+!
syn match	ruseChar	oneline    "#\\space"
syn match	ruseError	oneline    !#\\space[^ \t\[\]()";]\+!
syn match	ruseChar	oneline    "#\\newline"
syn match	ruseError	oneline    !#\\newline[^ \t\[\]()";]\+!

" Synchronization and the wrapping up...

syn sync match matchPlace grouphere NONE "^[^ \t]"
" ... i.e. synchronize on a line that starts at the left margin

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_ruse_syntax_inits")
  if version < 508
    let did_ruse_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink ruseSyntax		Statement
  HiLink ruseFunc		Function

  HiLink ruseString		String
  HiLink ruseChar		Character
  HiLink ruseNumber		Number
  HiLink ruseBoolean		Boolean

  HiLink ruseDelimiter	Delimiter
  HiLink ruseConstant		Constant

  HiLink ruseComment		Comment
  HiLink ruseMultilineComment	Comment
  HiLink ruseError		Error

  HiLink ruseExtSyntax	Type
  HiLink ruseExtFunc		PreProc
  delcommand HiLink
endif

let b:current_syntax = "ruse"
