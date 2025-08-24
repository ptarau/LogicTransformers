% tentativer - not yet working
% possible as an indexing mechanism but unlcear otherwise

:-include('comp.pl').

term2soup(X,PXs):-term2soup(X,[],PXs,[]).

term2soup(X,Ps)-->{var(X)},!,{append(Ps,_,Qs)},[X-Qs].
term2soup(X,Ps)-->{atomic(X)},!,[X-Ps].
term2soup(A=>B,Ps)-->
   term2soup(A,[0|Ps]),
   term2soup(B,[1|Ps]).


file2soup(F,S):-
  file2clause(F,C),
  clause2soup(C,S).

clause2soup(C,(SH:-SB)):-
   cls2bnf(C,(H:-B)),
   term2soup(H,SH),
   term2soup(B,SB).
   
 unify_soup([],_).
 unify_soup([P-G|Gs],Xs):-
    select(P-H,Xs,Ys),
    G=H,
    !,
    unify_soup(Gs,Ys).


to_soup(F,OutF):-
  open(OutF,write,CF),
  run((
    file2soup(F,(H:-B)),
    portray_clause(CF,cls(H,B))
  )),
  close(CF).

    
 soup:-
   to_soup('progs/arith.pro','out/soup.pl'),
   abolish(cls/2),
   consult('out/soup.pl').

goal2soup(G,S):-
   clause2soup((none:-G),(_:-S)).

 interp_soup([V-P|Xs]):-var(V),Xs==[],!,writeln(here=P-V).
 interp_soup(G):-
    goal2soup(G,SG),
    %portray_clause(SG),
    soup_steps(SG).

 soup_steps(SG):- 
    cls(H,B),
    soup_case(H,SG,B).

%soup_case(SG,H,[_|Cont]):-var(Cont),!,Cont=[].
soup_case(SG,H,B):- 
    %portray_clause(SG+H),
  
    unify_soup(SG,H),
    %assertion(H==SG),
    portray_clause(('UNIFIED'-->H)),
   
    soup_steps(B).


show_ts(C):-
   cls2bnf(C,(H:-B)),
   show_clause((H:-B)),nl,
   term2soup(H,SH),
   term2soup(B,SB),
   show_clause((SH:-SB)).

t0:-show_ts(a(42)).

t1:-show_ts((a:-b,c,d)).

t2:-show_ts((a(X,f(Y)):-b(X,Y),c(g(Y)),d(X))).

t3:-
   C=(a(X,f(Y)):-b(X,Y),c(g(Y)),d(X)),
   clause2soup(C,S),
   show_clause(C),nl,
   show_clause(S).
