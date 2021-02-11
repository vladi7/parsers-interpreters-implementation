#lang racket
; === Parser and Interpreter,

(provide run-parser)
(provide run)

; --- syntax

;  op ::= +
;      |  -
;      |  *
;
; exp ::= id
;      |  num
;      |  "lam" id exp0
;      |  "@" exp1 exp2 
;      |  "if" exp0 exp1 exp2
;      |  op exp1 exp2 
;      |  "begin" exp1 exp2
;      |  "let" id exp1 exp0
;      |  "new" id id
;      |  "get" exp1 "." id
;      |  "set" exp1 "." id exp2
  
; === lexical analysis

; --- tokens

(struct IdentT (string))
(struct NumT (num))
(struct PlusT ())
(struct MinusT ())
(struct TimesT ())
(struct LambdaT ())
(struct ApplyT ())
(struct IfT ())
(struct BeginT ())
(struct LetT ())
(struct NewT ())
(struct GetT ())
(struct SetT ())
(struct DotT ())

(define (char->digit ch)
  (- (char->integer ch) (char->integer #\0)))
  
(define (lexer chars)
   (if (null? chars)
      null
      (let ([current (first chars)] [remain (rest chars)])
         (cond
	   [(eq? current #\@) (cons (ApplyT) (lexer remain))]
	   [(eq? current #\+) (cons (PlusT) (lexer remain))]
	   [(eq? current #\-) (cons (MinusT) (lexer remain))]
           [(eq? current #\*) (cons (TimesT) (lexer remain))]
	   [(eq? current #\.) (cons (DotT) (lexer remain))]
           [(eq? current #\space) (lexer remain)]
	   [(eq? current #\newline) (lexer remain)]	   	   
	   [(char-numeric? current) (num-state (char->digit current) remain)]
	   [(char-alphabetic? current) (ident-state (list current) remain)]
	   [else (display (string-append "unknown symbol "
	                         (list->string (list current)) "\n"))]
	))))

(define (num-state seen chars)
   (if (and (pair? chars) (char-numeric? (first chars)))
      (num-state (+ (* 10 seen) (char->digit (first chars))) (rest chars))
      (cons (NumT seen) (lexer chars))
    ))

(define (ident-state seen chars)
   (if (and (pair? chars) 
          (or (char-alphabetic? (first chars))
              (char-numeric? (first chars))))
      (ident-state (append seen (list (first chars))) (rest chars))
      (cons (mk-alpha-token (list->string seen)) (lexer chars))
   ))

(define (mk-alpha-token seen)
   (cond
      [(equal? seen "lam") (LambdaT)]
      [(equal? seen "if") (IfT)]
      [(equal? seen "begin") (BeginT)]      
      [(equal? seen "let") (LetT)]      
      [(equal? seen "new") (NewT)]      
      [(equal? seen "get") (GetT)]      
      [(equal? seen "set") (SetT)]      
      [else (IdentT seen)]
     ))

(define (run-lexer x) (lexer (string->list x)))

; === parsing

; --- syntax trees

(struct IdentExp (id) #:transparent)
(struct NumExp (num) #:transparent)
(struct LambdaExp (formal body) #:transparent)
(struct ApplyExp (fun arg) #:transparent)
(struct IfExp (test exp1 exp2) #:transparent)
(struct PlusExp (exp1 exp2) #:transparent)
(struct MinusExp (exp1 exp2) #:transparent)
(struct TimesExp (exp1 exp2) #:transparent)
(struct BeginExp (exp1 exp2) #:transparent)
(struct LetExp (id exp1 body) #:transparent)
(struct NewExp (id1 id2) #:transparent)
(struct GetExp (obj id) #:transparent)
(struct SetExp (obj id exp2) #:transparent)

(define (parExpectIdent error-msg tks)
   (if (and (pair? tks) (IdentT? (first tks)))
      (values (IdentT-string (first tks)) (rest tks))
      (display error-msg)
   ))

(define (parExpect what? error-msg tks)
   (if (and (pair? tks) (what? (first tks)))
      (values "dummy" (rest tks))
      (display error-msg)
   ))

(define (parExp tks)
   (if (pair? tks)
      (let ([tk (first tks)] [tks0 (rest tks)])
         (cond
            [(IdentT? tk)
               (values (IdentExp (IdentT-string tk)) tks0)]
            [(NumT? tk)
               (values (NumExp (NumT-num tk)) tks0)]
 	    [(LambdaT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'lambda'\n" tks0)]
		  [(e tks2) (parExp tks1)])
   		 (values (LambdaExp id e) tks2))]
 	    [(ApplyT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
  		  [(e2 tks2) (parExp tks1)])
 		 (values (ApplyExp e1 e2) tks2))]
	    [(IfT? tk)
	       (let*-values (
	          [(e0 tks1) (parExp tks0)]
		  [(e1 tks2) (parExp tks1)]
		  [(e2 tks3) (parExp tks2)])
		 (values (IfExp e0 e1 e2) tks3))]
 	    [(PlusT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
  		  [(e2 tks2) (parExp tks1)])
 		 (values (PlusExp e1 e2) tks2))]
 	    [(MinusT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
  		  [(e2 tks2) (parExp tks1)])
 		 (values (MinusExp e1 e2) tks2))]
 	    [(TimesT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
  		  [(e2 tks2) (parExp tks1)])
 		 (values (TimesExp e1 e2) tks2))]
 	    [(BeginT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
  		  [(e2 tks2) (parExp tks1)])
 		 (values (BeginExp e1 e2) tks2))]
 	    [(LetT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'let'\n" tks0)]
  		  [(e1 tks2) (parExp tks1)]
  		  [(e0 tks3) (parExp tks2)])
   		 (values (LetExp id e1 e0) tks3))]
 	    [(NewT? tk)
 	       (let*-values (
 	          [(id1 tks1) (parExpectIdent
 		                 "field name expected after 'new'\n" tks0)]
	          [(id2 tks2) (parExpectIdent
 		                 "two field names expected after 'new'\n" tks1)])
                 (values (NewExp id1 id2) tks2))]
 	    [(GetT? tk)
 	       (let*-values (
 	          [(obj tks1) (parExp tks0)]
                  [(_  tks2) (parExpect DotT? "'.' expected in 'get'\n" tks1)]
		  [(id tks3) (parExpectIdent 
                                "field name expected after '.'\n" tks2)])
   		 (values (GetExp obj id) tks3))]
 	    [(SetT? tk)
 	       (let*-values (
 	          [(obj tks1) (parExp tks0)]
                  [(_  tks2) (parExpect DotT? "'.' expected in 'set'\n" tks1)]
		  [(id tks3) (parExpectIdent 
                                 "field name expected after '.'\n" tks2)]
 		  [(e2 tks4) (parExp tks3)])
   		 (values (SetExp obj id e2) tks4))]
            [else (display "not proper start of expression\n")]
         ))
      (display "expression expected\n")
   ))
   
(define (parse tks)
   (let-values ([(main tks1) (parExp tks)])
      (if (null? tks1)
         main
	 (display "program read but more input given\n"))
    ))

(define (run-parser x) (parse (run-lexer x)))

; === evaluating (abstract) syntax

; --- Locations
;   represented as integers

(define locs (box 0))

(define (new-loc!)
   (let ([_ (set-box! locs (+ 1 (unbox locs)))])
       (unbox locs)))

; --- environments
;   * binds identifiers and/or fields to locations
;   * are represented as a list of pairs

(define (extend-env id loc env)
  (cons (cons id loc) env)
 )

(define (lookup-env error-msg id env)
  (cond
     [(null? env)
        (display (string-append error-msg " " id "\n"))]
     [(equal? id (car (first env)) )
        (cdr (first env))]
     [else (lookup-env error-msg id (rest env))]
  ))

; --- stores
;   * binds locations to values
;   * represented as a list of pairs

(define (extend-sto loc val sto)
  (cons (cons loc val) sto)
 )

(define (lookup-sto loc sto)
  (cond
     [(null? sto)
        (display "undefined memory location\n")]
     [(equal? loc (car (first sto)) )
        (cdr (first sto))]
     [else (lookup-sto loc (rest sto))]
  ))

; --- values

(struct NumVal (num))
(struct ClosureVal (formal body env))
(struct Object (env))  

(define (interp exp env sto)
   (cond
      [(IdentExp? exp)
          (let ([loc (lookup-env "undeclared identifier"
                                  (IdentExp-id exp) env)])
             (values (lookup-sto loc sto) sto)
            )]
      [(NumExp? exp) (values (NumVal (NumExp-num exp)) sto)]
      [(LambdaExp? exp)
          (values (ClosureVal (LambdaExp-formal exp)(LambdaExp-body exp) env) sto)
             ]
      [(ApplyExp? exp)
          (let*-values 
               ([(v1 sto1) (interp (ApplyExp-fun exp) env sto)]
	        [(v2 sto2) (interp (ApplyExp-arg exp) env sto1)])
            (if (ClosureVal? v1)
               (let ([loc (new-loc!)])
                   (interp 
                     (ClosureVal-body v1) (extend-env (ClosureVal-formal v1) loc  (ClosureVal-env v1)) (extend-sto loc v2 sto1)
                   ))
   	       (display "non-function applied\n")))]
      [(IfExp? exp)
          (let-values 
               ([(v0 sto0) (interp (IfExp-test exp) env sto)])
           (if (and (NumVal? v0) (not (equal? (NumVal-num v0) 0)))
             (interp (IfExp-exp1 exp) env sto0)
             (interp (IfExp-exp2 exp) env sto0)))]
      [(PlusExp? exp)
          (let*-values 
               ([(v1 sto1) (interp (PlusExp-exp1 exp) env sto)]
	        [(v2 sto2) (interp (PlusExp-exp2 exp) env sto1)])
           (if (and (NumVal? v1) (NumVal? v2))
              (values (NumVal (+ (NumVal-num v1) (NumVal-num v2))) sto2)
              (display "operands to '+' must be numbers\n")))]
      [(MinusExp? exp)
          (let*-values 
               ([(v1 sto1) (interp (MinusExp-exp1 exp) env sto)]
	        [(v2 sto2) (interp (MinusExp-exp2 exp) env sto1)])
           (if (and (NumVal? v1) (NumVal? v2))
              (values (NumVal (- (NumVal-num v1) (NumVal-num v2))) sto2)
              (display "operands to '-' must be numbers\n")))]
      [(TimesExp? exp)
          (let*-values 
               ([(v1 sto1) (interp (TimesExp-exp1 exp) env sto)]
	        [(v2 sto2) (interp (TimesExp-exp2 exp) env sto1)])
           (if (and (NumVal? v1) (NumVal? v2))
              (values (NumVal (* (NumVal-num v1) (NumVal-num v2))) sto2)
              (display "operands to '*' must be numbers\n")))]
      [(BeginExp? exp)
       (let-values 
               ([(v1 sto1) (interp (BeginExp-exp1 exp) env sto)])
                (interp (BeginExp-exp2 exp) env sto1)
         )
         ]
      [(LetExp? exp)
          (interp 
             (ApplyExp 
                (LambdaExp (LetExp-id exp) (LetExp-body exp)) 
                (LetExp-exp1 exp))
             env sto)]
      [(NewExp? exp) 
          (let*                        
              ([loc1 (new-loc!)]
               [loc2 (new-loc!)])
          (values (Object (extend-env (NewExp-id2 exp) loc1 (extend-env (NewExp-id1 exp) loc2 env))) sto)
               )]
      [(GetExp? exp)
          (let-values 
               ([(v0 sto0) (interp (GetExp-obj exp) env sto)])
            (if (Object? v0)
             (values (lookup-sto (lookup-env "Error while getting the expression" (GetExp-id exp)(Object-env v0)) sto0) sto)
            (display "This is not an object")
            )
                 )]
      [(SetExp? exp)
          (let*-values 
               ([(v0 sto0) (interp (SetExp-obj exp) env sto)]
	        [(v2 sto1) (interp (SetExp-exp2 exp) env sto0)])
            (if (Object? v0)
             (values v0(extend-sto (lookup-env "Error while setting the expression " (SetExp-id exp)(Object-env v0)) v2 sto1))
             (display "This is not an object")
             )
                )]
  ))

(define (run x)
   (let ([main (run-parser x)])
     (let-values ([(v sto) (interp main null null)])
       (cond
         [(NumVal? v) (NumVal-num v)]
	 [else (display "program must return a number\n")]
    ))))

