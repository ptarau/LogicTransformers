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


% term to unifiable set of paths

t2p(T,Pss):-t2p(T,[],Pss,[]).

t2p(X,Ps)-->{atomic(X);var(X)},!,{reverse(Ps,Qs),append(Qs,X,Rs)},[Rs].
t2p(T,Ps)-->{T=..Xs},t2ps(Xs,0,Ps).

t2ps([],_,_)-->[].
t2ps([X|Xs],N,Ps)-->{succ(N,SN)},t2p(X,[N|Ps]),t2ps(Xs,SN,Ps).


c2ps((H:-Cs),cls(Head,Tail)):-
   conj2list(Cs,Bs),
   maplist(t2p,[H|Bs],Xsss),
   append(Xsss,Tail,Head).



conj2list(true,[]):-!.
conj2list((X,Xs),[X|Ys]):-!,conj2list(Xs,Ys).
conj2list(Last,[Last]).

%% returns clauses in file, one at a time
file2clause(F,C):-
  seeing(S),
  see(F),
  repeat,
    read(X),
    ( X=end_of_file,!,see(F),seen,see(S),fail
    ; C=X
    ).

file2ps(F):-
   abolish(cls/2),
   file2clause(F,Cs),
   c2ps(Cs,Cls),
   assertz(Cls),
   fail
 ; true.


metaint(X):-write('>>>>'),portray_clause(X),fail.
metaint([]).        % no more goals left, succeed
metaint([G|Gs]):-   % unify the first goal with the head of a clause
   %ppp(here=G),
   cls([H|Bs],Gs),  % build a new list of goals from the body of the
                    % clause extended with the remaining goals as tail
   match_with_head(G,H),
   metaint(Bs).     % interpret the extended body

match_with_head(G,H):-

  maplist(match_path(H),G),
    write('#####'),ppp(G).

match_path([H|_],G):-copy_term(H,HH),copy_term(HH,G),!.
match_path([_|Hs],G):-match_path(Hs,G).

meta(G):-
  t2p(goal(G),Pss),
  metaint([Pss]).

tp2:-
  file2ps('lamgen.pro'),
  listing(cls/2),
  writeln('---------'),
  meta(G),
  ppp(answer=G),
  fail.

tp1:-
  T=f(a,[b,g(X,15,c)],X),
  t2p(T,Pss),ppp(Pss),
  ppp(T),
  ppp(Pss).

etest:-
  % assumes ground terms
  T=f(a,g(b,h(c),d),e),
  writeln(T),
  term2paths(T,Pss),
  writeln(Pss),
  fail.


%%%%


term2tab(T,Tabs):-
  term2paths(T,Pss),
  maplist(split_path,Pss,Tabs).


split_path(Ps,Label-Val):-
  Sep='v',
  append(Qs,[Val],Ps),!,
  join_with_(Sep,Qs,Rs),
  atomic_list_concat(Rs,Label).

join_with(Sep,[X|Xs],[X|Rs]):-join_with_(Sep,Xs,Rs).

join_with_(_,[],[]).
join_with_(Sep,[X|Xs],[Sep,X|Ys]):-join_with_(Sep,Xs,Ys).

ttest:-
  % assumes ground terms
  T=f(a,g(b,h(c),d),e),
  writeln(T),
  term2tab(T,Tabs),
  writeln(Tabs),
  fail.

terms2table(Tss,Rows-Cols,Triplets):-
  maplist(term2tab,Tss,Lss),
  findall(t(I,L,V),(nth0(I,Lss,Ls),member(L-V,Ls)),Triplets),
  findall(L,member(t(_,L,_),Triplets),Ls),
  sort(Ls,Cs),
  length(Tss,Rows),
  length(Cs,Cols).


file2triplets(FN):-
  ( file2triplets(FN,T),
    assertz(T),
    fail
  ;
    dims(D),
    writeln('dims':D),
    assertz(D),
    tell('data/triplets.pro'),
    listing(counts/3),
    listing(t/3),
    told
  ).

file2triplets(FN,t(I,L,V)):-
   abolish(at/11),
   abolish(t/3),
   abolish(counts/3),
   consult(FN),
   at(I,_,_,F,_),
   term2tab(F,LVs),
   member(L-V,LVs).


dims(counts(IC,IL,IV)):-
  aggregate_all(count,distinct(I,t(I,_,_)),IC),
  aggregate_all(count,distinct(L,t(_,L,_)),IL),
  aggregate_all(count,distinct(V,t(_,_,V)),IV).



file2tsv(FN):-
   consult(FN),
   tell('data/triplets.tsv'),
   (
     at(I,_,_,F,_),
     term2path(F,Ps),
     once(append(Ks,[V],Ps)),
     join_with('v',Ks,Rs),
     atomic_list_concat(Rs,Label),
     join_with('\t',[I,Label,V],Ls),
     atomic_list_concat(Ls,Line),
     write(Line),nl,
     fail
  ; true
  ),
  told.


tsv:-
  file2tsv('data/facts.pro').

big_tsv:-
  file2tsv('data/big_facts.pro').


tt:-file2triplets('data/big_facts.pro').

tt1:-file2triplets('../TEXT_CRAFTS/StanzaGraphs/logic/OUTPUT_DIRECTORY/arxiv_all.pro').



ttt(FN):-
  abolish(at/11),
  abolish(t/3),
  abolish(counts/3),
  consult(FN),
  findall(F,at(_,_,_,F,_),Fs),
  terms2table(Fs,Dim,_Table),
  %ppp(Table),
  ppp(Dim).


ttt:-ttt('data/facts.pro').

ttt1:-ttt('../TEXT_CRAFTS/StanzaGraphs/logic/OUTPUT_DIRECTORY/arxiv_all.pro').


%%%%%%%%%%

% term to vectors: DF positions + symbols reached
term2vect(T,[As,Cs]):-
  t2m(T,0, 0,_, Xss,[]),
  transpose3(Xss,[As,_,Cs]).

% term to 3,n matrix: 2 edge vectors + symbols
term2mat(T,Tss):-
  t2m(T,0, 0,_, Xss,[]),
  sort(Xss,Yss),
  transpose3(Yss,Tss).

% shared transformer
t2m(T,Xss):-t2m(T,0, 0,_, Xss,[]).

% do DF visit while extracting edges and atoms_vars
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


% reversed transformations

% rebuilds term from DF codes + syms
vect2term([Is,Xs],T):-
  length(Is,L),L1 is L-1,
  numlist(0,L1,Js), % adds ID permuation, before sort
  transpose3(ABCsUnsorted,[Is,Js,Xs]),
  sort(ABCsUnsorted,ABCs),
  from_transposed(ABCs,T).

% rebuilds term from 3 row matrix: 2 for edges ine for syms
mat2term(Xss,T):-
  transpose3(ABCs,Xss),
  from_transposed(ABCs,T).

from_transposed(ABCs,T):-
  maplist(as_pairs,ABCs,A_BCs),
  group_pairs_by_key(A_BCs,As_BCss),
  build_term(As_BCss,[0-Xs|_]),
  T=..Xs.


build_term([],[]).
build_term([N-Xs|Xss],[N-Ys|Yss]):-
  scan_term(Xs,Ys,Xss,NVs,[]),
  build_term(Xss,Yss),
  fill_out(NVs,Yss).

% figures out which codes indicate compound terms
scan_term([],[],_)-->[].
scan_term([[N,F]|Xs],[NewVar|Ys],Xss)-->
   {memberchk(N-_,Xss)},
   !,
   [N-(F:NewVar)],
   scan_term(Xs,Ys,Xss).
scan_term([[_N,A]|Xs],[A|Ys],Xss)-->
    scan_term(Xs,Ys,Xss).

% once variables stand as placeholders
% fill them out with corresponding terms
fill_out([],_).
fill_out([N-(F:V)|NVs],Yss):-
  selectchk(N-Ys,Yss,Zss),
  V=..[F|Ys],
  fill_out(NVs,Zss).



%%

t2s(T,[As,Ps]):-t2s(T,As,[],Ps,[]).

t2s(A,[A|As],As)-->{atomic(A);var(A)},!,[0,0].
t2s(T,[F|As],Bs)-->{T=..[F|Xs]},[1],t2ss(Xs,As,Bs).

t2ss([],As,As)-->[2].
t2ss([X|Xs],As,Cs)-->t2s(X,As,Bs),t2ss(Xs,Bs,Cs).

simple(X):-atomic(X),!.
simple(X):-var(X).

listify(X,R):-simple(X),!,R=s(X).
listify(T,Rs):-T=..Xs,maplist(listify,Xs,Rs).


l2m([],Rs,Rs)-->[].
l2m(s(X),[X|Rs],Rs)-->[].
l2m([X|Xs],Rs1,Rs3)-->[0],l2m(X,Rs1,Rs2),[1],l2m(Xs,Rs2,Rs3).


l2m(T,[Xs,Ys]):-
   l2m(T,Xs,[],Ys,[]).

ltest:-
   T=f(a,g(b,X,h(c,X,Y),d),e,Y),
   listify(T,Xs),
   l2m(Xs,[Ls,Rs]),
   length(Ls,L1),length(Rs,L2),
   portray_clause((T:-Ls,Rs)),
   writeln(L1+L2).

% tests

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
  TT=f(_,g(b,X,_,d),e,_),
  pq(T),
  pq(TT),
  T=TT,
  pq(T),
  fail.


vq(T):-
  term2vect(T,Pss),
  portray_clause((T:-Pss)),
  vect2term(Pss,TT),
  writeln('operation reversed:'),
  portray_clause(TT),
  nl.

vtest:-
  T=f(a,g(b,X,h(c,X,Y),d),e,Y),
  TT=f(_,g(b,X,_,d),e,_),
  vq(T),
  vq(TT),
  T=TT,
  vq(T),
  fail.


sq(T):-
  t2s(T,Pss),
  portray_clause((T:-Pss)),
  %t2s(Pss,TT),
  %writeln('operation reversed:'),
  %portray_clause(TT),
  nl.

stest:-
  T=f(a,g(b,X,h(c,X,Y),d),e,Y),
  TT=f(_,g(b,X,_,d),e,_),
  sq(T),
  sq(TT),
  T=TT,
  sq(T),
  fail.

/*

TODO: single pass vect2term
TODO: right,down,up,end encoding
?- etest.
f(a,g(b,h(c),d),e)
[[0,f],[1,a],[2,0,g],[2,1,b],[2,2,0,h],[2,2,1,c],[2,3,d],[3,e]]


?- mtest.
f(a, g(b, A, h(c, A, B), d), e, B) :-

    [ [0, 0, 0, 0, 0, 2, 2, 2, 2, 5, 5, 5],
      [0, 1, 2, 10, 11, 3, 4, 5, 9, 6, 7, 8],
      [f, a, g, e, B, b, A, h, d, c, A, B]
    ].
operation reversed:
f(a, g(b, A, h(c, A, B), d), e, B).

f(A, g(b, C, D, d), e, B) :-

    [ [0, 0, 0, 0, 0, 2, 2, 2, 2],
      [0, 1, 2, 7, 8, 3, 4, 5, 6],
      [f, A, g, e, B, b, C, D, d]
    ].
operation reversed:
f(_, g(b, _, _, d), e, _).

f(a, g(b, A, h(c, A, B), d), e, B) :-

    [ [0, 0, 0, 0, 0, 2, 2, 2, 2, 5, 5, 5],
      [0, 1, 2, 10, 11, 3, 4, 5, 9, 6, 7, 8],
      [f, a, g, e, B, b, A, h, d, c, A, B]
    ].
operation reversed:
f(a, g(b, A, h(c, A, B), d), e, B).

false.

?- vtest.
f(a, g(b, A, h(c, A, B), d), e, B) :-

    [ [0, 0, 0, 2, 2, 2, 5, 5, 5, 2, 0, 0],
      [f, a, g, b, A, h, c, A, B, d, e, B]
    ].
operation reversed:
f(a, g(b, A, h(c, A, B), d), e, B).

f(A, g(b, C, D, d), e, B) :-

    [ [0, 0, 0, 0, 0, 2, 2, 2, 2],
      [0, 1, 2, 7, 8, 3, 4, 5, 6],
      [f, A, g, e, B, b, C, D, d]
    ].
operation reversed:
f(_, g(b, _, _, d), e, _).

f(a, g(b, A, h(c, A, B), d), e, B) :-

    [ [0, 0, 0, 2, 2, 2, 5, 5, 5, 2, 0, 0],
      [f, a, g, b, A, h, c, A, B, d, e, B]
    ].
operation reversed:
f(a, g(b, A, h(c, A, B), d), e, B).

false.

*/
