% helpers

c:-make.

:-op(800,fx,ppp).
ppp(X):-portray_clause(X).

do(X):-X,fail;true.

% directed terms constructor
:-op(100,xfy,('=>')).


lift_funs(H,R):-var(H),!,R=H.
lift_funs(H,R):-atomic(H),!,R=H.
lift_funs(H,R):-H=..[F|Xs],
  maplist(lift_funs,Xs,Ys),
  R=..['$',F|Ys].

drop_funs(R,H):-var(R),!,H=R.
drop_funs(R,H):-atomic(R),!,H=R.
drop_funs(R,H):-
  R=..['$',F|Ys],
  maplist(drop_funs,Ys,Xs),
  H=..[F|Xs].

%% turns a term of the form H:-[B1,B2..] into binary =>/2 tree
fromBinTree(H,R):-(var(H),var(R)),!,R=H.
fromBinTree(H,R):-(atomic(H);atomic(R)),!,R=H.
fromBinTree((A=>B),(H:-Bs)):-fromBinTrees((A=>B),Bs,H).

fromBinTrees(H,[],R):-(var(H),var(R)),!,R=H.
fromBinTrees(H,[],R):-(atomic(H);atomic(R)),!,R=H.
fromBinTrees((A=>B),[HA|Bs],H):-fromBinTree(A,HA),fromBinTrees(B,Bs,H).

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
to_eqs(HOrB,A, T,Eqs):-toEq(HOrB,T=A,Eqs,[]).

toEq(_HOrB,T=A)-->{atomic(A)},!,{T=A}.
toEq(_HOrB,T=A)-->{var(A)},!,{T=A}.
toEq(HOrB,T=(A=>B))-->toEq(HOrB,X=A),toEq(HOrB,Y=B),to_triplet(HOrB,X,Y,T).

%to_triplet(_,X,Y,T)-->[(X=>Y)=T].


%to_triplet(_,X,Y,T)-->[l(T,X),r(T,X)].
%T=(X=>_). l(X=>_,X).
%r(T,X):-T=(_=>Y). r(_=>Y,Y).
% l(P,X):-var(P),!,functor(P,=>,2),arg(1,P,X).
% l(P,X):-arg(1,P,X).

to_triplet(head,X,Y,T)-->[u(X,Y,T)].
to_triplet(body,X,Y,T)-->[b(X,Y,T)].

%% the single "built-in" unification operation
%% can be also written out to compiled file
%u(B,H,(B=>H)).
%b(B,H,(B=>H)).


% turns a term into an equational form
term2eqs(HorB,T,V,Eqs):-fromTerm(T,Imps),to_eqs(HorB,Imps,V,Eqs).

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
to_tnf((H:-Bs),[V,B],Ts:Us):-
  to_bnf((H:-Bs),(HI:-BI)),
  to_eqs(head,HI,V,Ts),
  to_eqs(body,BI,B,Us).

% TODO
to_tnf0((H0:-Bs0),[V,B],Ts:Us):-
  lift_funs1(H0,H),lift_funs(Bs0,Bs),
  to_bnf((H:-Bs),(HI:-BI)),
  to_eqs(head,HI,V,Ts),
  to_eqs(body,BI,B,Us).

lift_funs1(goal(X),goal(X)):-!.
lift_funs1(A,B):-lift_funs(A,B).

to_tnf1((H:-Bs),Code):-
  to_bnf((H:-Bs),(HI:-BI)),
  to_eqs(head,HI,V,Ts),
  to_eqs(body,BI,B,Us),
  append([[d(V,B,_C)],Ts,Us,[p(B)]],Code),
  tnf2(Code,0),
  tnf3(Code,0).

tnf2([],_).
tnf2([p(_)|Xs],N):-tnf2(Xs,N).
tnf2([d(_A,_B,X)|Xs],N):-M is N+2,pvar(X,N),
  tnf2(Xs,M).
tnf2([u(_A,_B,X)|Xs],N):-M is N+2,pvar(X,N),
  tnf2(Xs,M).
tnf2([b(_A,_B,X)|Xs],N):-M is N+2,pvar(X,N),
  tnf2(Xs,M).


%tnf3(Xs,N):-writeln(trace=Xs+N),fail.
tnf3([],_).
tnf3([p(_)|Xs],N):-tnf3(Xs,N).
tnf3([d(A,B,_)|Xs],N):-M is N+2,N1 is N+1,
  lvar(A,N),rvar(B,N1),
  tnf3(Xs,M).
tnf3([u(A,B,_)|Xs],N):-M is N+2,N1 is N+1,
  lvar(A,N),rvar(B,N1),
  tnf3(Xs,M).
tnf3([b(A,B,_)|Xs],N):-M is N+2,N1 is N+1,
  lvar(A,N),rvar(B,N1),
  tnf3(Xs,M).

/*
lvar(X,N):-var(X)->X=(var:N);true.

rvar(X,N):-var(X)->X=(var:N);true.
*/

pvar(X,N):-var(X)->atom_concat('^',N,X);true.

lvar(X,N):-var(X)->atom_concat('_',N,X);true.

rvar(X,N):-var(X)->atom_concat('_',N,X);true.

hasm(InF,OutF):-
  tell(OutF),
  do((
    file2clause(InF,Cls),
    clausify(Cls,(HBs)),
    to_tnf1(HBs,Is),
    member(I,Is),
    pp_line(I)
  )),
  told,
  true.

pp_line(T):-
  T=..[F|Xs],
  write(F),
  do((
    member(X,Xs),
    write(' '),
    write(X)
  )),
  nl.


hgo:-
  hasm('progs/plain.pro','out/hasm.txt').





%% binarized implicational normal form
to_bnf((H:-Bs),(HI:-BI) ):-
  to_bin((H:-Bs),(HC:-BC)),
  fromTerm(HC,HI),
  fromTerm(BC,BI).

to_rnf((H:-Bs),(HC:-BC) ):-
  fromTerm(H,HI),
  fromTerm(Bs,BI),
  to_bin((HI:-BI),(HC:-BC)).


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

% alternative binarization
% directly building arrow form
to_bc((H0:-Bs),(HC:-BC)):-
  fromTerm(H0,H),
  add_cont(H,C,HC),
  conj2list(Bs,Cs),
  bc_body(Cs,C,BC).

add_cont(C,A,A=>C).

bc_body([],C,C).
bc_body([B0|Bs],C,BC):-
  fromTerm(B0,B),
  bc_body(Bs,C,T),
  add_cont(B,T,BC).




%% converts a clause to triplet normal form
%% two predicates only: p/1 (user code) and u/3 (a builtin)
%% u/3 can be specialized as b/3 when it only builds terms
cls2tnf(Cls,(P:-Ys)):-
  clausify(Cls,(H:-Bs)),
  to_tnf((H:-Bs),[V,B],Ts:Us),
  maplist(to_pred,[V,B],[P,Q]),
  append([Ts,Us,[Q]],Xs),
  %ppp((P:-Xs)),abort,
  list2conj(Xs,Ys).

cls2bnf(Cls,BNF):-
  clausify(Cls,(H:-Bs)),
  to_bnf((H:-Bs),BNF).

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


tgo:-
  do((
    member(F,[allperms,arith,leaf,memb,mpart,nrev,perm,puzzle,queens,small,su4,tarith]),
     atomic_list_concat(['progs/',F,'.pro'],InF),
    atomic_list_concat(['out/',F,'_asm.pro'],OutF),
    tcompile(InF,OutF)
  )).

xgo(F):-
  atomic_list_concat(['progs/',F,'.pro'],InF),
  atomic_list_concat(['out/',F,'_asm.pro'],OutF),
  go(InF,OutF).


%% compile Horn clause file to triplet normal form
tcompile(F,CF):- 
  tell(CF),
  %ppp((p(X):-numbervars(X,0,_),writeln(X),fail)),

  ppp(':-'(op(100,xfy,('=>')))),
  Mes='% QUERY THIS WITH: ?- p(Answer => _ => goal).',
  writeln(Mes),nl,

  ppp(u(A,B,'=>'(A,B))),
  ppp(b(A,B,'=>'(A,B))),
  ppp((p(V):-var(V),!,V=true)),
  do((
    file2clause(F,C),
    cls2tnf(C,TNF),
    %numbervars(TNF,0,_N),
    ppp(TNF)
  )),
  told.

%% compile Horn clause file implicational binarized normal form
bcompile(F,CF):-
  tell(CF),
  do((
    file2clause(F,C),
    cls2bnf(C,((H:-B))),
    ppp(cls(H,B))
  )),
  told.


run_bnf(Answer):-run_bnf_file('out/bnf_asm.pro',Answer).

run_bnf_file(F,Answer):-
 consult(F),
 run_bnf_from_goal(BinAnswer=>_=>goal),
 toTerm(BinAnswer,Answer).

run_bnf_from_goal(H):-
  cls(H,B),
  ( var(B)->true
  ; run_bnf_from_goal(B)
  ).


bgo:-
  InF='queens',
  OutF='out/bnf_asm.pro',
  bgo(InF,OutF).

bgo(InF,OutF):-
  atomic_list_concat(['progs/',InF,'.pro'],Source),
  bcompile(Source,OutF),
  do((run_bnf_file(OutF,Answer),
  ppp('ANSWER':Answer)
  )).

basm:-
  InF='queens',
  OutF='out/bnf_asm.txt',
  basm(InF,OutF).

basm(InF):-
 OutF='out/bnf_asm.txt',
 basm(InF,OutF).

basm(InF,OutF):-
  atomic_list_concat(['progs/',InF,'.pro'],Source),
  to_basm(Source,OutF).


%% to "assembler"
to_basm(F,CF):-
  tell(CF),
  do((
    file2clause(F,C),
    cls2bnf(C,(H:-B)),
    to_postfix(H,PostFixsH),
    to_postfix(B,PostFixsB),
    append([PostFixsH,[(:-)|PostFixsB],['$']],PostFixs),
    %to_postfix((H=>B),PostFixs),
    numbervars(PostFixs,0,_),
    [First|Xs]=PostFixs,
    write(First),
    do((
       member(X,Xs),
       write(' '),
       write(X)
    )),
    nl
  )),
  told.


/*
to_prefix(Tree,R:Pfs):-K=ctr(0),to_prefix(Tree,R,K,Pfs,[]).

to_prefix(A,A)-->{var(A);atomic(A)},!.
to_prefix(A=>B,Z)-->[X=>Y],to_prefix(A,X),to_prefix(B,Y).
*/


/*
to_prefix(Tree,Pfs):-to_prefix(Tree,Pfs,[]).

to_prefix(A)-->{var(A);atomic(A)},!,[A].
to_prefix(A=>B)-->['=>'],to_prefix(A),to_prefix(B).
*/



to_postfix(Tree,Pfs):-to_postfix(Tree,Pfs,[]).

to_postfix(A)-->{var(A);atomic(A)},!,[A].
to_postfix(A=>B)-->to_postfix(A),to_postfix(B),['$'].


%% to "assembeler"
to_tasm1(F,CF):-
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

get_preds(C,FN,GM):-
  ( C=(H:-Bs)->
     functor(H,F,N),
     get_body_pred(Bs,G/M),
     atomic_list_concat([G,'/',M],GM)
  ; functor(C,F,N),GM=nil
  ),
  atomic_list_concat([F,'/',N],FN).

get_body_pred(Bs,F/N):-
  (
    Bs=(B,_)->functor(B,F,N)
  ; functor(Bs,F,N)
  ).

%% to "assembeler"
to_tasm(F,CF):-
  tell(CF),
  do((
    file2clause(F,C),
    get_preds(C,HP,BP),
    cls2tnf(C,TNF),
    TNF=(Head:-Body),
    numbervars(TNF,0,_),
    Head=..[_P,X],
    write(d),write(' '),write(X),
    write(' '),write(HP),write(' '),writeln(nil),
    conj2list(Body,Bs),
    do((
      member(B,Bs),
      B=..[D|As0],
      (D='p'->append(As0,[BP,nil],As);As=As0),
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
  %portray_clause('CALLING':Body),
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

run_orig(F):-
  consult(F),
  do((goal(X),fail,writeln(X))).



to_out_fname(F,OutF):-
  split_string(F, ['.'], [],[Pref,Suf]),
  atomic_list_concat([Pref,'_asm.',Suf],OutF).


go(F):-go(F,'out/tnf_asm.pro').

go(F,OutF):-
  tcompile(F,OutF),
  consult(OutF),
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
