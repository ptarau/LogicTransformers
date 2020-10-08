% helpers

:-op(800,fx,ppp).
ppp(X):-portray_clause(X).

do(X):-X,fail;true.

% directed terms constructor
:-op(100,xfy,('=>')).

%% turns a term of the form H:-[B1,B2..] into binary =>/2 tree
fromBinTree(H,R):-(var(H),var(R)),!,R=H.
fromBinTree(H,R):-(atomic(H);atomic(R)),!,R=H.
fromBinTree((A=>B),(H:-Bs)):-!,fromBinTrees((A=>B),Bs,H).

fromBinTrees(H,[],R):-(var(H),var(R)),!,R=H.
fromBinTrees(H,[],R):-(atomic(H);atomic(R)),!,R=H.
fromBinTrees((A=>B),[HA|Bs],H):-!,fromBinTree(A,HA),fromBinTrees(B,Bs,H).

%% reverses from a =>/2 binary tree to the original term
toBinTree(A,B):-fromBinTree(B,A).

%% turns a term like f(a,b,...) into f:-[a,b,...]
listify(T,H):-var(T),!,H=T.
listify(T,H):-atomic(T),!,H=T.
listify(T,(F:-Ys)):-T=..[F|Xs],
  maplist(listify,Xs,Ys).

%% turns a term like   f:-[a,b,...] into f(a,b,...)
functorize(H,T):-var(H),!,T=H.
functorize(H,T):-atomic(H),!,T=H.
functorize((F:-Ys),T):-
  maplist(functorize,Ys,Xs),
  T=..[F|Xs].  
 
%%  form =/2 tree to term
toTerm-->fromBinTree,functorize.

%% from term to =/2 tree
fromTerm-->listify,toBinTree.

%% turn a =>/2 tree into an equational form
%% by introdicing new variables 
%% somewhat similar to the Tseitin transform
to_eqs(A, T,Eqs):-toEq(T=A,Eqs,[]).

toEq(T=A)-->{atomic(A)},!,{T=A}.
toEq(T=A)-->{var(A)},!,{T=A}.
toEq(T=(A=>B))-->toEq(X=A),toEq(Y=B),to_triplet(X,Y,T).

%to_triplet(X,Y,T)-->[(X=>Y)=T].

to_triplet(X,Y,T)-->[u(X,Y,T)].

%% the single "built-in" unification operation
%% can be also written out to compiled file
u(B,H,(B=>H)).



% turns a term into an equational form
term2eqs(T,V,Eqs):-fromTerm(T,Imps),to_eqs(Imps,V,Eqs).

%% turns a conjunction (like in a clause body) 
%% to standard list format

conj2list(A,[PA]):-var(A),!,to_pred(A,PA).
conj2list((A,B),[PA|Bs]):-!,lift_to_pred(A,PA),conj2list(B,Bs).
conj2list(A,[]):-A=true,!.
conj2list(A,[A]).

lift_to_pred(A,R):-var(A),!,to_pred(A,R).
lift_to_pred(A,A).


%% turns from  list into a conjunction
list2conj([],true).
list2conj([A|As],Cs):-list2conjs(A,As,Cs).

%list2conjs(p(A),[],R):-!,R=A.
list2conjs(A,[],A).
list2conjs(A,[B|Bs],(A,Cs)):-list2conjs(B,Bs,Cs).


%% turns a clause (with its body a list) into a
%% triplet normal form (wrapping equations into u/3 facts)
%% assumes Bs is a list
to_tnf((H:-Bs),[V,B],Ts:Us):-
  to_bin((H:-Bs),(HC:-BC)),
  term2eqs(HC,V,Ts),
  term2eqs(BC,B,Us).

%% binarization : a continuation passing form
to_bin((H:-Bs),(HC:-BC)):-
  add_continuation(H,C,HC),
  conj2list(Bs,Cs),
  bin_body(Cs,C,BC).
  
add_continuation(H,C,HC):-
  H=..[F|Xs],
  append(Xs,[C],Ys),
  HC=..[F|Ys].
  
bin_body([],C,C).
bin_body([B|Bs],C,BC):-
  bin_body(Bs,C,T),
  add_continuation(B,T,BC).
 
%% converts a clause to triplet normal form
%% two predicates only: p/1 (user code) and u/3 (a builtin)
cls2tnf(Cls,(P:-Ys)):-
  clausify(Cls,(H:-Bs)),
  to_tnf((H:-Bs),[V,B],Ts:Us),
  maplist(to_pred,[V,B],[P,Q]),
  append([Ts,Us,[Q]],Xs),
  %ppp((P:-Xs)),abort,
  list2conj(Xs,Ys).
  
% normalizes clauses to H:-B form
clausify((A:-B),R):-!,R=(A:-B).
clausify(A,(A:-true)).

%% marks X as a user predicate p/1
to_pred(X,p(X)).

%% returns clauses in file, one at a time
file2clause(F,C):-
  seeing(S),
  see(F),
  repeat,
    read(X),
    ( X=end_of_file,!,see(F),seen,see(S),fail
    ; C=X
    ).

%% compile Horn clause file to triplet normal form
tcompile(F,CF):- 
  tell(CF),
  %ppp((p(X):-numbervars(X,0,_),writeln(X),fail)),
  ppp(':-'(op(100,xfy,('=>')))),
  ppp((p(V):-var(V),!,V=true)),
  do((
    file2clause(F,C),
    cls2tnf(C,TNF),
    %numbervars(TNF,0,_N),
    ppp(TNF)
  )),
  told.
   
%% to "assembeler"
to_tasm(F,CF):- 
  tell(CF),
  do((
    file2clause(F,C),
    cls2tnf(C,TNF),
    TNF=(Head:-Body),
    numbervars(TNF,0,_),
    Head=..[_P,X],
    write(d),write(' '),writeln(X),
    conj2list(Body,Bs),
    do((
      member(B,Bs),
      B=..[D|As],
        write(D),
        do((
          member(A,As),
          write(' '),write(A)
        )),
        nl
    ))
  )),
  told.
  
call_tnf(Goal):-
  term_variables(Goal,Vars),
  copy_term(Goal:Vars,G:Xs),
  cls2tnf((query(Xs):-G),(p(_V):-Body)),
  portray_clause('CALLING':Body),
  call(Body),
  maplist(toTerm,Xs,Vars).

%quick_call(X):-

%% runs atest
%% proving that all the transformations form a chanin that
%% commutes with SLD resolution steps, by returning the same
%% result as the "comiled" probram running in Prolog form

run(F):-pgo(F),go(F).

go:-go('progs/queens.pro').
go1:-go('progs/puzzle.pro').
go2:-go('progs/su4.pro').
go3:-go('progs/tarith.pro').

go(F):-
  tcompile(F,'out/tnf_asm.pro'),
  consult('out/tnf_asm.pro'),
  C=c(0),
  do((
     call_tnf(goal(X)),
     ppp(X),
     arg(1,C,K),succ(K,SK),
     nb_setarg(1,C,SK)
  )),
  arg(1,C,Count),
  writeln('PROLOG ANSWERS'=Count).

pgo:-pgo('progs/queens.pro').
pgo1:-pgo('progs/puzzle.pro').

pgo(F):-to_tasm(F,'out/tnf_asm.txt').
        
bm:-
  compile('out/tnf_asm.pro'),
  time(
    do(
      call_tnf(goal(_))
  )).
  
nv(X):-numbervars(X,0,_).

term_ex(f(X,g(X,Y),Y)).

pred_ex((a(f(X)):-b(c,X),d(g(X)))).
/*
?- term_ex(T),fromTerm(T,BT),nv(T).
T = f(A, g(A, B), B),
BT = A=>(A=>B=>g)=>B=>f.


?- term_ex(T),term2eqs(T,H,Bs),nv(Bs).
T = f(C, g(C, A), A),
H = G,
Bs = [u(A, g, B), u(C, B, D), u(A, f, E), u(D, E, F), u(C, F, G)].
*/
/*
call_tnf1(X):-
  cls2tnf((query(X):-goal(X)),(p(_V):-Body)),
  %ppp(just=V),
  call(Body),
  %toTerm(V,A),
  %ppp(term=A),
  true.
  
%for bp
go2:-
  qcompile(queens_tnf),  
  do((
  call_tnf1(X)
  %,toTerm(X,T),ppp(T)
  )).
  
append(Xss,Xs):-appendN(Xss,Xs).

% for yap

:-ensure_loaded(library(lists)).
:-ensure_loaded(library(apply)).
go3:-
  consult(queens_tnf),  
  time(
  do((
  call_tnf1(_)
  %,toTerm(X,T),ppp(T)
  ))).
*/

/*
% some tests

?- toBinTree((a:-[b,c]),V).
V =  (b=>c=>a).

?- 

T = g(a, f(b, c)),
I =  (a=>(b=>c=>f)=>g).


?- term2eqs((g(a,b(d),c)),V,E).
E = [p(d, b, _796), p(c, g, _828), p(_796, _828, _790), p(a, _790, V)].

?- to_tnf((a(f(X)):-b(X,Y),c(Y)),R,S),numbervars(R+S,0,_).
X = D,
Y = F,
R = [A:[B, C]],
S = [u(D, f, E), u(E, a, A)]:[[u(F, b, G), u(D, G, B)], [u(F, c, C)]].

?- 

p(D) :-
    u(b, f, B),
    u(c, g, A),
    u(A, a, C),
    u(B, C, D).


?- cls2tnf(a(f(b),f(b)),R),ppp(R),fail.
p(D) :-
    u(b, f, B),
    u(b, f, A),
    u(A, a, C),
    u(B, C, D).


?- cls2tnf((a(f(X)):-b(X,Y),c(Y)),R),ppp(R),fail.
p(B) :-
    u(C, f, A),
    u(A, a, B),
    u(E, b, D),
    u(C, D, F),
    u(E, c, G),
    p(F),
    p(G).
  

?- to_bin((a:-[b,c,d]),R).
R =  (a(_4274):-b(c(d(_4274)))).

?- to_bin((a:-[]),R).
R =  (a(_3492):-_3492).

  
?- T=(a(Cont):-call(Cont)),cls2tnf(T,R),ppp(R),fail.

p(A) :-
    u(B, a, A),
    u(B, d, C),
    u(C, c, D),
    u(D, b, E),
    p(E).
    
    
?- T=(a(B):-call(B)),cls2tnf(T,R),ppp(R),fail.

p(A) :-
    u(B, a, A),
    u(B, call, C),
    p(C).
    
    
u(B,call,C),p(C)

B=>call=C

p(B=>call)

||
\/

p(A) :-
    u(B, a, A), % B=>a = A
    p(B).


cls2tnf((a(X):-X,b(X),X),R),ppp(R),fail.

su4.pro
ANSWER: (((1=>((2=>((3=>((4=>([]=>.))=>.))=>.))=>.))=>
        (((3=>((4=>((1=>((2=>([]=>.))=>.))=>.))=>.))=>
        (((2=>((3=>((4=>((1=>([]=>.))=>.))=>.))=>.))=>
        (((4=>((1=>((2=>((3=>([]=>.))=>.))=>.))=>.))=>
        ([]=>.))=>.))=>.))=>.))=>(Cont=>goal))

*/


/* NOTES

the u/3 triplets can be turned from tree to DAG representation
by unifying the 3-rd var arguments when their arg 1 = arg 2

the triplets can be collected in 3 vectors
left,mid,right and unification can proceed in
parallel on those

much longer vectors can be created by unfolding p/1 clauses, 1 or 2 levels down

triplets can be sorted - e.g. those with more ground vars first

u can be specialized to types:

u00(A,B,C)
u01(A,b,C)
u10(a,B,C)
u11(a,b,C)

as well as read/write mode (read for head, write for body)

p(X) can be extended with indexing info e.g. pred+fst arg e.g.,

p(f,a,X)


all vars occuring in a clause can be collected to a vector
pushed to the heap at once

all constants occuring in the head (and possibly also in the body)
used for indexing or ML-based clause-fetching

applying binarization makes longer vectors!

:-nb_setval(ctr,5).
step:-nb_getval(ctr,SK),succ(K,SK),nb_setval(ctr,K).


%p(L):-toTerm(L,T),ppp(T),(step->fail;abort).

p(L):-var(L),!.


example of Ds in Python or any language with GC

var  : [Val] , possibly self ref or alt. None
A=>B : (A,B)
const : int, string etc.

def u(A,B,C):-
  if isinstance(C,tuple) : % should be always true !!!
     l=len(C)
     if l==1 :
       unify((A,B),C) # bind C to A,B
     else:
        X,Y=C
        unify(X,A) &&
        unify(Y,B)
  else fail
  
trail
choice-point stack or just the yield mechanism

list types: vars, possibly with other attributes, besides val
pair types : pairs,immutable

LCO : restore ACC on baktracking

code stired into array of vectors or, better, dict with
ndexing info as key

*/
