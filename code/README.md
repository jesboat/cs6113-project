Files for "Towards Mechanized Proof of Noninterference"

This is not actually a fully working implementation.  The proofs do not reflect
the final version discussed in the paper because some necessary changes were
determined very late into writing.  The code included here was the status of the
Coq and related files as of the deadline.  We will soon make the repository for
these proofs public after the deadline.

File summary:

Makefile
  Runs the coq compiler on the files in the correct order.  Also has a clean
command for removing all of the compiled files, cleaning the directory.

parser-frontend.rkt
parser.rkt
plai-typed-18Feb2013.plt
racket-datatypes.rkt
racket-util.rkt
ragg.plt
  Files related to an abandoned attempt to have a parser read in a program in
TinyML^2 for processing by the functions in the Coq code.

Rel.v
SfLib.v
  Utility libraries borrowed from the e-book Software Foundations.

identifiers.v
  Legacy file, not required by any of the other Coq files and could have been
dropped.

syntax.v
  Basic syntax for TinyML^2.  Does not include the syntax fix mentioned in the
paper, since we realized this fix would work after the fact.  Types are included
in value nodes for simpler reasoning.  Ideally the parser and/or a verified type
inference engine would assign these types.

operational_semantics.v
  Operational semantics proofs and definitions.

type_rules.v
  Typing relations and related functions.  Beginning of the proof of
substitution lemma.
