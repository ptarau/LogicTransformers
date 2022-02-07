% Representing Directed Graphs as Prolog Cyclic Terms

graph([
  0-[1,2],
  1-[0,3],
  2-[4],
  3-[4],
  4-[0,1]
]).


graph1([
  4-[1,2],
  1-[4,3],
  2-[0],
  3-[0],
  0-[4,1]
]).



/*
% a picture of the graph

>  0 <> 1 < --\
|  v    v      \
|  2    3      |
|  |  /        |
|   v          |
|< 4---------->
*/

do(X):-X,fail;true.

:-dynamic n/2.
:-table n/2.

graph2prog(_,(
  n(T,_R,Xs):-memberchk(T,Xs),!,fail
)).
graph2prog(_,n(T,T,_)).
graph2prog(G,C):-
  call(G,AList),
  member(F-Ns,AList),
  member(T,Ns),
  C=(
    n(T,R,Xs) :- n(F,R,[T|Xs]
  )).

graph2bin(_,(n(X,X))).
graph2bin(G,C):-
  call(G,AList),
  member(F-Ns,AList),
  member(T,Ns),
  C=
  ( n(T,R):-n(F,R)
  ).

graph2bc(G):-
  retractall(n(_,_)),
  do((
    graph2bin(G,C),
    assert(C)
  )).



graph2code(G):-
  retractall(n(_,_,_)),
  do((
    graph2prog(G,C),
    assert(C)
  )).


bgo:-
  graph2bc(graph),
  do((
    n(0,X),
    ppp(X)
  )).


cgo:-
  graph2code(graph1),
  do((
    n(3,X,[]),
    ppp(X)
  )).


graph2cyclic(Xss,T):-
   graph2vars(T,Xss,Vss),
   vars2term(Vss).

graph2vars(T,Xss,Vss):-
  length(Xss,N),
  functor(T,'g',N),
  g2vars(T,Xss,Vss).

g2vars(_,[],[]).
g2vars(T,[X-Xs|Xss],[V*A-Vs|Vss]):-
  arg1(X,T,V*A),
  g2var_list(T,Xs,Vs),
  g2vars(T,Xss,Vss).

g2var_list(_,[],[]).
g2var_list(T,[X|Xs],[V|Vs]):-
  arg1(X,T,V),
  g2var_list(T,Xs,Vs).

vars2term([]).
vars2term([_X*A-Xs|Xss]):-
  A=Xs,
  vars2term(Xss).

arg1(I,T,X):-succ(I,I1),arg(I1,T,X).

mapfun(F,T):-
  T=..[_|Xs],
  maplist(F,Xs).

% tests

ppp(X):-portray_clause(X).


%% turns from  list into a conjunction
list2conj([],true).
list2conj([A|As],Cs):-list2conjs(A,As,Cs).

%list2conjs(p(A),[],R):-!,R=A.
list2conjs(A,[],A).
list2conjs(A,[B|Bs],(A,Cs)):-list2conjs(B,Bs,Cs).

go:-
  graph(Xss),
  ppp('GRAPH AS ADJACENCY LISTS'),
  maplist(ppp,Xss),
  graph2vars(T,Xss,Vss),
  ppp('SAME, WITH FRESH VARIABLES REPLACING VERTICES'),
  ppp(T:-Vss),
  graph2cyclic(Xss,T),
  T=..[_,V|Vs],
  list2conj(Vs,Cs),
  ppp('GRAPH AS SEEN FROM EACH VERTEX'),
  ppp(V:-Cs).

c:-make.
