#lang racket

; === Parser and Interpreter,

; --- what is visible to the outside

(provide run-lexer)
(provide run-parser)
(provide run)

; --- syntax

; exp ::= id
;      |  num
;      |  "lam" id exp
;      |  "@" exp1 exp2
;      |  "let" id exp1 exp2
;      |  "if" exp1 exp2 exp3
;      |  op exp1 exp2 
;
;  op ::= "+"
;      |  "-"
;      |  "*"
;      |  ":"
;
; === lexical analysis

; --- tokens

(struct IdentT (string))
(struct NumT (num))
(struct LamT ())
(struct AppT ())
(struct LetT ())
(struct IfT ())
(struct PlusT ())
(struct MinusT ())
(struct TimesT ())
(struct ColonT ())

(define (char->digit ch)
  (- (char->integer ch) (char->integer #\0)))
  ;lexer is the whole line and it's being read accordingly
(define (lexer chars)
   (if (null? chars)
      null
      (let ([current (first chars)] [remain (rest chars)])
         (cond
	   [(eq? current #\+) (cons (PlusT) (lexer remain))]
	   [(eq? current #\-) (cons (MinusT) (lexer remain))]
           [(eq? current #\*) (cons (TimesT) (lexer remain))]
           [(eq? current #\:) (cons (ColonT) (lexer remain))]
           [(eq? current #\@) (cons (AppT) (lexer remain))]
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
      [(equal? seen "lam") (LamT)]
      [(equal? seen "let") (LetT)]
      [(equal? seen "if") (IfT)]
      [else (IdentT seen)]
     ))

(define (run-lexer x) (lexer (string->list x)))

; === parsing

; --- syntax trees

(struct IdentExp (string) #:transparent)
(struct NumExp (num) #:transparent)
(struct LamExp (formal body) #:transparent)
(struct AppExp (fun arg) #:transparent)
(struct LetExp (id exp1 exp2) #:transparent)
(struct IfExp (test exp1 exp2) #:transparent)
(struct PlusExp (exp1 exp2) #:transparent)
(struct MinusExp (exp1 exp2) #:transparent)
(struct TimesExp (exp1 exp2) #:transparent)
(struct ColonExp (key val) #:transparent)

(define (parExpectIdent error-msg tks)
   (if (and (pair? tks) (IdentT? (first tks)))
      (values (IdentT-string (first tks)) (rest tks))
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
 	    [(LamT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'lam'\n" tks0)]
 		  [(e tks2) (parExp tks1)])
 		 (values (LamExp id e) tks2))]
 	    [(AppT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
 		  [(e2 tks2) (parExp tks1)])
 		 (values (AppExp e1 e2) tks2))]
 	    [(LetT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'let'\n" tks0)]
 	          [(e1 tks2) (parExp tks1)]
 		  [(e2 tks3) (parExp tks2)])
 		 (values (LetExp id e1 e2) tks3))]
	    [(IfT? tk)
	       (let*-values (
                  [(test tks1) (parExp tks0)]
	          [(e1 tks2) (parExp tks1)]
		  [(e2 tks3) (parExp tks2)]) 
		 (values (IfExp test e1 e2) tks3))] ;;; CHANGE #7
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
 	    [(ColonT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
 		  [(e2 tks2) (parExp tks1)])
 		 (values (ColonExp e1 e2) tks2))]
             [else (display "not proper start of expression\n")
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

; --- values

(struct NumVal (num))
(struct ClosureVal (formal body env))
(struct DictVal (dict))
; (struct DelayedVal (exp env)) *** USE FOR CBN ONLY

(define initial-env
  (list
    (cons "empty" (DictVal null))
  ))

(define (extend-env id val env)
  (cons (cons id val) env)
 )

(define (lookup-env env id)
  (cond
     [(null? env)
        (display (string-append "the identifier used is not in the current scope, id:" id "\n"))]
     [(equal? id (car (first env)) )
        (cdr (first env))]
     [else (lookup-env (rest env) id)]
  ))

(define (lookup-dict dict key)
  (cond
     [(null? dict)  
         0 ]
     [(equal? key (car (first dict)) )
        (cdr (first dict))]
     [else (lookup-dict (rest dict) key)]
 ))

(define (eval exp env)
   (cond
      [(IdentExp? exp)
           (lookup-env env (IdentExp-string exp))]
      [(NumExp? exp) 
           (NumVal (NumExp-num exp))]
      [(LamExp? exp)
          (ClosureVal (LamExp-formal exp) (LamExp-body exp) env)]
      [(AppExp? exp)
          (let ([v1 (eval (AppExp-fun exp) env)])
	     (cond
	        [(ClosureVal? v1)
		   (let ([v2 (eval (AppExp-arg exp) env)]) ;;; + CHANGE #3  
 	              (eval (ClosureVal-body v1) (extend-env (ClosureVal-formal v1) v2 (ClosureVal-env v1))))]
	        [(DictVal? v1)
		   (let ([v2 (eval (AppExp-arg exp) env)])  ;;; + CHANGE #4
                      (NumVal (lookup-dict (DictVal-dict v1) (NumVal-num v2))))] 
	        [else (display "the integer is applied as a function to argument\n")]))]        
      [(LetExp? exp)
          (eval (AppExp (LamExp (LetExp-id exp) (LetExp-exp2 exp))
                        (LetExp-exp1 exp))
                env)]
      [(IfExp? exp)
          (let ([v (eval (IfExp-test exp) env)])
             (if (> (NumVal-num v) 0) ;;; + CHANGE #8
	        (eval (IfExp-exp1 exp) env)
                (eval (IfExp-exp2 exp) env)))]
      [(PlusExp? exp)
          (let ([v1 (eval (PlusExp-exp1 exp) env)]
	        [v2 (eval (PlusExp-exp2 exp) env)])
            (cond
              [(and (NumVal? v1) (NumVal? v2))
                     (NumVal (+ (NumVal-num v1) (NumVal-num v2)))]
              [(and (DictVal? v1) (DictVal? v2))
                     (DictVal (append (DictVal-dict v1) (DictVal-dict v2) ))]
              [else (display "both operands to '+' must be numbers")])
            )]
     [(MinusExp? exp)
          (let ([v1 (eval (MinusExp-exp1 exp) env)]
	        [v2 (eval (MinusExp-exp2 exp) env)])
	    (cond
	       [(and (NumVal? v1) (NumVal? v2))
		        (NumVal (- (NumVal-num v1) (NumVal-num v2)))]
               [else (display "both operands to '-' must be numbers\n")]))]
     [(TimesExp? exp) 
          (let ([v1 (eval (TimesExp-exp1 exp) env)]
	        [v2 (eval (TimesExp-exp2 exp) env)])
            (cond
	       [(and (NumVal? v1) (NumVal? v2))
		        (NumVal (* (NumVal-num v1) (NumVal-num v2)))]
               [else (display "both operands to '*' must be numbers\n")]))]
     [(ColonExp? exp)
          (let ([k (eval (ColonExp-key exp) env)]
	        [v (eval (ColonExp-val exp) env)])
            (cond
	       [(and (NumVal? k) (NumVal? v))
                    (DictVal (list (cons (NumVal-num k) (NumVal-num v))))]
               [else (display "both operands to ':' must be numbers\n")]))]
     [else (display "the operand is a function")]
   ))

(define (run x)
   (let ([main (run-parser x)])
     (let ([v (eval main initial-env)])
       (cond
         [(NumVal? v) (NumVal-num v)]
	 [else (display "program must return a number\n")])
   )))



