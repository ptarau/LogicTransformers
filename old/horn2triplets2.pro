% helpers

:-op(800,fx,ppp).
ppp(X):-portray_clause(X).

do(X):-X,fail;true.

:-op(100,xfy,(=>)).


%% turns a term into binary tree with =>/2 as constructor
toHorn(H,R):-(var(H),var(R)),!,R=H.
toHorn(H,R):-(atomic(H);atomic(R)),!,R=H.
toHorn((A=>B),(H:-Bs)):-!,toHorns((A=>B),Bs,H).


toHorns(H,[],R):-(var(H),var(R)),!,R=H.
toHorns(H,[],R):-(atomic(H);atomic(R)),!,R=H.
toHorns((A=>B),[HA|Bs],H):-!,toHorn(A,HA),toHorns(B,Bs,H).

%% reverses from a =>/2 binary tree to the original term
fromHorn(A,B):-toHorn(B,A).

term2horn(T,H):-var(T),!,H=T.
term2horn(T,H):-atomic(T),!,H=T.
term2horn(T,(F:-Ys)):-T=..[F|Xs],
  maplist(term2horn,Xs,Ys).
  
horn2term(H,T):-var(H),!,T=H.
horn2term(H,T):-atomic(H),!,T=H.
horn2term((F:-Ys),T):-
  maplist(horn2term,Ys,Xs),
  T=..[F|Xs].  
 
%%  form =/2 tree to term
toTerm-->toHorn,horn2term.

%% from term to =/2 tree
fromTerm-->term2horn,fromHorn.

%% turn a =>/2 tree into and equational form
%% by introdicing new variables 
%% somewhat similar to the Tseitin transform
to_eqs(A, T,Eqs):-toEq(T=A,Eqs,[]).

toEq(T=A)-->{atomic(A)},!,{T=A}.
toEq(T=A)-->{var(A)},!,{T=A}.
toEq(T=(A=>B))-->toEq(X=A),toEq(Y=B),[u(X,Y,T)].


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
  conj2list(Bs,Cs),
  to_bin((H:-Cs),(HC:-BC)),
  term2eqs(HC,V,Ts),
  term2eqs(BC,B,Us).

%% binarization : a continuation passing form
to_bin((H:-Bs),(HC:-BC)):-
  add_cont(H,C,HC),
  bin_body(Bs,C,BC).
  
add_cont(H,C,HC):-
  H=..[F|Xs],
  append(Xs,[C],Ys),
  HC=..[F|Ys].
  
bin_body([],C,C).
bin_body([B|Bs],C,BC):-
  bin_body(Bs,C,T),
  add_cont(B,T,BC).

  
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

%% the single "built-in" unification operation
u(B,H,(B=>H)).


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
  ppp((p(V):-var(V),!)),
  do((
    file2clause(F,C),
    cls2tnf(C,TNF),
    ppp(TNF)
  )),
  told.
 
call_tnf(X):-
  cls2tnf((goal(X):-goal(X)),(p(_A):-Body)),
  call(Body).

%% runs atest
%% proving that all the transformations form a chanin that
%% commutes with SLD resolution steps, by returning the same
%% result as the "comiled" probram running in Prolog form
go:-
  tcompile('queens.pro','queens_tnf.pl'),
  consult('queens_tnf.pl'),
  
  do((
     call_tnf(X),
     toTerm(X,T),
     %ppp(T),
     true
  )).

  


/*
% some tests

?- fromHorn((a:-[b,c]),V).
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

applying binarization amkes longer vectors!

:-nb_setval(ctr,5).
step:-nb_getval(ctr,SK),succ(K,SK),nb_setval(ctr,K).


%p(L):-toTerm(L,T),ppp(T),(step->fail;abort).

p(L):-var(L),!.
*/