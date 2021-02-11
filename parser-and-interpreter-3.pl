/*
=== Parser and Interpreter,
*/

/* inquire(Tokens)
   INPUT: Tokens is a list representing a condition with quantified variables
   OUTPUT: Any instantiation of the variables mentioned existentially
        (without a surrounding universal quantifier) 
      which satisfies the condition represented by Tokens
*/

inquire(Tokens) :- 
  parse(Tokens,Tree), solve(Tree).

/* parse(S,C)
   INPUT: S is a list of tokens
   OUTPUT: if S forms a boolean expression
           then C is instantiated to a condition tree representing that boolean expression
*/

parse(S,C) :- parseBE(S,[],C).

/* parseBE(S,R,C)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms a boolean expression
           then R is the remaining tokens
           and C is instantiated to a condition tree representing that boolean expression
*/
parseBE(S,R,C) :- parseBT(S,R,C).
parseBE(S,R,disj(E1,E2)) :- parseBT(S,[Disj | R1],E1), already(Disj,or), parseBE(R1,R,E2).

/* parseBT(S,R,C)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms a boolean term
           then R is the remaining tokens
           and C is instantiated to a condition tree representing that boolean term
*/
parseBT(S,R,C) :- parseBF(S,R,C).
parseBT(S,R,conj(E1,E2)) :- parseBF(S,[Conj | R1],E1), already(Conj,and), parseBT(R1,R,E2).

/* parseBF(S,R,C)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms a boolean factor
           then R is the remaining tokens
           and C is instantiated to a condition tree representing that boolean factor
*/
parseBF(S,R,less(E1,E2)) :- parseE(S,[Less | R1],E1), already(Less,<), parseE(R1,R,E2).
parseBF(S,R,equal(E1,E2)) :- parseE(S,[Eq | R1],E1), already(Eq,=), parseE(R1,R,E2).
parseBF([Q | S],R,exists(V,H,C)) :- already(Q, some(V,H)), parseBF(S,R,C).
parseBF([Q | S],R,forall(V,H,C)) :- already(Q, all(V,H)), parseBF(S,R,C).
parseBF([S | R], R, C) :- compound(S), parseBE(S, [], C).

/* parseE(S,R,T)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms an expression
           then R is the remaining tokens
           and T is instantiated to an expression tree representing that expression
*/
parseE(S,R,E) :- parseT(S,R,E).
parseE(S,R,plus(E1,E2)) :- parseT(S,[Plus | R1],E1), already(Plus,+), parseE(R1,R,E2).

/* parseT(S,R,T)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms a term
           then R is the remaining tokens
           and T is instantiated to an expression tree representing that term
*/
parseT(S,R,E) :- parseF(S,R,E).
parseT(S,R,times(E1,E2)) :- parseF(S,[Mult | R1],E1), already(Mult,*), parseT(R1,R,E2).

/* parseF(S,R,T)
   INPUT: S is a list of tokens
   OUTPUT: if a prefix of S forms a factor
           then R is the remaining tokens
           and T is instantiated to an expression tree representing that factor
*/
parseF([C | S], S, const(C)) :- number(C).
parseF([S | R], R, E) :- compound(S), parseE(S, [], E).
parseF([X | S], S, variable(X)) :- var(X).

/* already(X,C)
   INPUT: C is instantiated to a non-variable
   OUTPUT: is true if X is already instantiated to something 
      that matches that non-variable
*/
already(X,C) :- not(var(X)), X = C. 

/* evaluate(E,V)
   INPUT: E is a fully instantiated expression tree
   OUTPUT: V is instantiated to the value of evaluating E
*/
evaluate(const(N),N).
evaluate(variable(N),N) .

evaluate(plus(E1,E2),S) :-evaluate(E1,V1), evaluate(E2,V2), S is V1 + V2. 

evaluate(times(E1,E2),P) :-evaluate(E1,V1), evaluate(E2,V2), P is V1 * V2.

/* solve(C)
   INPUT: C is a condition tree without free variables
   OUTPUT: succeeds (perhaps several times) iff C evaluates to true,
         together with the corresponding instantiations of the 
         existentially quantified variables 
               (that are not surrounded by a universal quantifier)
*/
solve(less(E1,E2)) :- evaluate(E1,V1), evaluate(E2,V2), V1 < V2.
solve(equal(E1,E2)) :- evaluate(E1,V1), evaluate(E2,V2), V1 =:= V2.

solve(conj(C1,C2)) :- (solve(C1), solve(C2)).
solve(disj(C1,C2)) :- (solve(C1); solve(C2)).

solve(exists(V,H,C)) :- gen_instances(V,1,H), solve(C).

solve(forall(V,H,C)) :- not((gen_instances(V,1,H), not(solve(C)))).
/* gen_instances(V,L,H)
    INPUT: L,H are integers; V a variable
    OUTPUT: V is instantiated to 
         all values in the interval [L..H]
*/

gen_instances(L,L,H) :- L =< H.
gen_instances(V,L,H) :- Temp is L+1, Temp =< H, gen_instances(V, Temp, H).


