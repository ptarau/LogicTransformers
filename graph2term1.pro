% Representing Directed Graphs as Prolog Cyclic Terms

graph([
  0-[1,2],
  1-[0,3],
  2-[4],
  3-[4],
  4-[0,1]
]).


/*
% a picture of the graph

>  0 <> 1 < --\
|  v    v      \
|  2    3      |
|  v  /        |
|   v          |
|< 4---------->
*/

graph2cyclic(Xss,T):-
   graph2vars(T,Xss,Vss),
   vars2term(Vss).

graph2vars(T,Xss,Vss):-
  length(Xss,N),
  functor(T,'g',N),
  g2vars(T,Xss,Vss).

g2vars(_,[],[]).
g2vars(T,[X-Xs|Xss],[V-Vs|Vss]):-
  arg1(X,T,V),
  g2var_list(T,Xs,Vs),
  g2vars(T,Xss,Vss).

g2var_list(_,[],[]).
g2var_list(T,[X|Xs],[V|Vs]):-
  arg1(X,T,V),
  g2var_list(T,Xs,Vs).

vars2term([]).
vars2term([X-Xs|Xss]):-
  X=Xs,
  vars2term(Xss).

arg1(I,T,X):-succ(I,I1),arg(I1,T,X).

% tests

ppp(X):-portray_clause(X).

go:-
  graph(Xss),
  ppp('GRAPH AS ADJACENCY LISTS'),
  maplist(ppp,Xss),
  graph2vars(T,Xss,Vss),
  ppp('SAME, WITH FRESH VARIABLES REPLACING VERTICES'),
  ppp(T:-Vss),
  graph2cyclic(Xss,T),
  T=..[_|Vs],
  ppp('GRAPH AS SEEN FROM EACH VERTEX'),
  maplist(ppp,Vs).

c:-make.
