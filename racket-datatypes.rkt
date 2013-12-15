#lang plai-typed
(require (typed-in racket (number->string : (number -> string))))
(require (typed-in racket (remove-duplicates : ((listof 'a) -> (listof 'a)))))

(define-type expression 
  [Value (val : value)]
  [Application (fun : value) (arg : value) ]
  [Let-Bind (name : symbol) (bind : value) (body : expression)]
  [Ite (test : value) (then : expression) (otherwise : expression)]
  [Expression_Evaluation_Pair (left : expression) (right : expression)]
  )

(define-type value 
  [Identifier (varname : symbol)]
  [Unit]
  [Integer (val : number)]
  [Fix (arg : symbol) (body : expression) ]
  [Void]
  [Value_Evaluation_Pair (left : value)  (right : value)]
)
 
(define-values (log-symbol get-symbols)
  (local 
   [(define symbol-list (list))
	(define (log-symbol s) 
	  (begin 
		(set! symbol-list (cons s symbol-list)) 
		(symbol->string s)))
	(define (get-symbols) 
	  (map symbol->string (remove-duplicates symbol-list)))]
   (values log-symbol get-symbols)))


(define (to-coq-expr ast)
  (type-case expression ast
	[Value (val) (string-append 
				  "Value (" 
				  (string-append (to-coq-val val) ")"))]
	[Application 
	 (fun arg) 
	 (stringlist->string 
	  (list "Application (" (to-coq-val fun) ") (" (to-coq-val arg) ") "))]
	[Let-Bind 
	 (name bind body) 
	 (stringlist->string 
	  (list "Let_Bind (" (log-symbol name) ") 
      (" (to-coq-val bind)  ") (" (to-coq-expr body) ") "))]
	[Ite 
	 (test then otherwise)
	 (stringlist->string
	  (list "If ("(to-coq-val test) ") 
                ("(to-coq-expr then) ") 
                ("(to-coq-expr otherwise) ") "))]
	[Expression_Evaluation_Pair 
	 (left right)
	 (stringlist->string
	  (list "Expression_Evaluation_Pair ("(to-coq-expr left) ") ("(to-coq-expr right) ") "))]))

(define (to-coq-val v) 
  (type-case value v
	[Identifier (v) (string-append " Identifier " (log-symbol v))]
	[Unit () " Unit "]
	[Integer (val) (string-append " Integer " (number->string val))]
	[Fix (arg bod) 
		 (stringlist->string 
		  (list 
		   " Fix ("(log-symbol arg) ") (" (to-coq-expr bod) ") "))]
	[Void () " Void "]
	[Value_Evaluation_Pair (l r)
	 (stringlist->string
	  (list "Value_Evaluation_Pair (" (to-coq-val l) ") (" 
			(to-coq-val r) ") "))]))


(define (stringlist->string s)
  (cond
	[(empty? s) ""]
	[(empty? (rest s)) (first s)]
	[else (string-append (first s) (stringlist->string (rest s)))]))

