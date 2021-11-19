c:-make.

term2paths(T,Pss):-
   findall(Ps,term2path(T,Ps),Pss).


term2path(T,Ps):-term2path(T,[],Ps).

term2path(T,Ps,[I|NewPs]):-
   compound(T),
   !,
   argx(I,T,X),
   term2path(X,Ps,NewPs).
term2path(A,Ps,[A|Ps]).

argx(0,T,F):-functor(T,F,_).
argx(I,T,F):-arg(I,T,F).


etest:-
  T=f(a,g(b,h(c),d),e),
  writeln(T),
  term2paths(T,Pss),
  writeln(Pss),
  fail.


term2mat(T,Tss):-
  t2m(T,0, 0,_, Xss,[]),
  sort(Xss,Yss),
  transpose3(Yss,Tss).

t2m(T,Xss):-t2m(T,0, 0,_, Xss,[]).

t2m(A,R,I,J)-->{atomic(A);var(A)},!,{succ(I,J)},[[R,I,A]].
t2m(T,R,I,K)-->
   {T=..[F|Xs]},
   [[R,I,F]],
   {succ(I,J)},
   t2ms(Xs,I,J,K).

t2ms([],_,I,I)-->[].
t2ms([X|Xs],R,I,K)-->
  t2m(X,R,I,J),
  t2ms(Xs,R,J,K).

transpose3(Xss,[As,Bs,Cs]):-
  maplist(split,Xss,As,Bs,Cs).

split([X,Y,Z],X,Y,Z).

as_pairs([X,Y,Z],X-[Y,Z]).

mat2term(Xss,As_BCss):-
  transpose3(ABCs,Xss),
  maplist(as_pairs,ABCs,A_BCs),
  group_pairs_by_key(A_BCs,As_BCss).

pq(T):-
  term2mat(T,Pss),
  portray_clause((T:-Pss)),
  mat2term(Pss,Xss),
  portray_clause(Xss).

ppp(T):-portray_clause(('!!!':-T)).

mtest:-
  T=f(a,g(b,X,h(c,X,Y),d),e,Y),
  TT=f(_,g(b,X,_,d),e,_),
  pq(T),
  fail,
  pq(TT),
  T=TT,
  pq(T),
  fail.
