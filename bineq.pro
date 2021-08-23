% helpers

c:-make.

:-op(800,fx,ppp).

ppp(X):-portray_clause(X).

do(X):-X,fail;true.


%% binarization : a continuation passing form


add_true((H:-B),R):-!,R=(H:-B).
add_true(H,(H:-true)).

to_bin(C,B):-
  add_true(C,CT),
  to_bin0(CT,B).

to_bin0((H:-Bs),(HC:-BC)):-
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

conj2list(A,[PA]):-var(A),!,to_pred(A,PA).
conj2list((A,B),[PA|Bs]):-!,lift_to_pred(A,PA),conj2list(B,Bs).
conj2list(A,[]):-A=true,!.
conj2list(A,[A]).

%% turns from  list into a conjunction
list2conj([],true).
list2conj([A|As],Cs):-list2conjs(A,As,Cs).

%list2conjs(p(A),[],R):-!,R=A.
list2conjs(A,[],A).
list2conjs(A,[B|Bs],(A,Cs)):-list2conjs(B,Bs,Cs).


lift_to_pred(A,R):-var(A),!,to_pred(A,R).
lift_to_pred(A,A).

%% marks X as a user predicate p/1
to_pred(X,p(X)).

% terms to equations

term2eqs(X,T,[X=T]):-var(T),!.
term2eqs(X,T,[X=T]):-atomic(T),!.
term2eqs(X,T,Es):-compound(T),term2eqs(X,T,Es,[]).

term2eqs(X,T)-->{var(T)},!,{X=T}.
term2eqs(X,T)-->{atomic(T)},!,{X=T}.
%erm2eqs(X,Xs)-->{is_list(Xs)},!,{T=..[lists|Xs]},term2eqs(X,T).
term2eqs(X,T)-->{compound(T),functor(T,F,N),functor(TT,F,N)},
  [X=TT],
  term2arg_eqs(0,N,TT,T).

term2arg_eqs(N,N,_,_)-->!,[].
term2arg_eqs(I,N,X,T)-->
  {I1 is I+1},
  {arg(I1,X,V)},
  {arg(I1,T,A)},
  term2eqs(V,A),
  term2arg_eqs(I1,N,X,T).

eqs2trips([])-->[].
eqs2trips([(X=T)|Es])-->
  eq2trips(X,T),
  eqs2trips(Es).

eq2trips(X,T)-->{compound(T)},!,
  {functor(T,F,N)},
  [f(N,X,F)],
  args2trips(X,T,1,N).
eq2trips(X,X)-->[].


args2trips(_X,_T,I,N)-->{I>N},!.
args2trips(X,T,I,N)-->{I>0},
  {arg(I,T,A)},
  [a(I,X,A)],
  {J is I+1},
  args2trips(X,T,J,N).


term2chain(T,H,Bs):-
  term2eqs(H,T,Es),
  eqs2trips(Es,Bs,[]).


clause2chain(C,Is):-
  to_bin(C,(X:-Y)),
  term2chain(X,H,Xs),
  term2chain(Y,B,Ys),
  append([[d(H)],Xs,Ys,[p(B)]],Is).


%% returns clauses in file, one at a time
file2clause(F,C):-
  seeing(S),
  see(F),
  repeat,
    read(X),
    ( X=end_of_file,!,seen,see(S),fail
    ; C=X
    ).

file2chain-->
  file2clause,
  clause2chain.


p(true):-!.
p(T):-
  %ppp('!!!'+T),nl,
  d(T).

f(N,T,F):-functor(T,F,N).

a(I,T,A):-arg(I,T,A).

:-dynamic(d/1).

file2db(F):-
  abolish(d/1),
  do((
    file2chain(F,[H|Is]),
    list2conj(Is,Bs),
    assertz((H:-Bs))
  )).

go1:-
  F='progs/plain.pro',
  do((
    file2chain(F,[I|Is]),
    ppp((I:-Is))
  )).


comp(F):-
  file2db(F),
  listing(d/1).

run:-
  T=goal(X,true),
  do((
    d(T),
    %ppp(X),
    true
  )).


go:-
  F='progs/queens.pro',
  comp(F),
  time(run).


/*

?- to_bin((a:-[b,c,d]),R).
R =  (a(_4274):-b(c(d(_4274)))).

?- to_bin((a:-[]),R).
R =  (a(_3492):-_3492).

*/
