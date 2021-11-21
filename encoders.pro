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
  % assumes ground terms
  T=f(a,g(b,h(c),d),e),
  writeln(T),
  term2paths(T,Pss),
  writeln(Pss),
  fail.


%%%%%%%%%%

term2vects(T,[As,Cs]):-
  t2m(T,0, 0,_, Xss,[]),
  transpose3(Xss,[As,_,Cs]).

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

mat2term(Xss,T):-
  transpose3(ABCs,Xss),
  maplist(as_pairs,ABCs,A_BCs),
  group_pairs_by_key(A_BCs,As_BCss),
  build_term(As_BCss,[0-Xs|_]),
  T=..Xs.



build_term([],[]).
build_term([N-Xs|Xss],[N-Ys|Yss]):-
  scan_term(Xs,Ys,Xss,NVs,[]),
  build_term(Xss,Yss),
  fill_out(NVs,Yss).

fill_out([],_).
fill_out([N-(F:V)|NVs],Yss):-
  selectchk(N-Ys,Yss,Zss),
  V=..[F|Ys],
  fill_out(NVs,Zss).

scan_term([],[],_)-->[].
scan_term([[N,F]|Xs],[NewVar|Ys],Xss)-->
   {memberchk(N-_,Xss)},
   !,
   [N-(F:NewVar)],
   scan_term(Xs,Ys,Xss).
scan_term([[_N,A]|Xs],[A|Ys],Xss)-->
    scan_term(Xs,Ys,Xss).



pq(T):-
  term2mat(T,Pss),
  portray_clause((T:-Pss)),
  mat2term(Pss,TT),
  writeln('operation reversed:'),
  portray_clause(TT),
  nl.

ppp(T):-portray_clause(('!!!':-T)).

mtest:-
  T=f(a,g(b,X,h(c,X,Y),d),e,Y),
  %TT=f(_,g(b,X,_,d),e,_),
  pq(T),
  %pq(TT),
  %T=TT,
  pq(T),
  fail.
