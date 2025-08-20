:-op(100,xfy,('=>')).


go:-
   Inp=('progs/arith.pro',
   Outp='out/arith_bnf_asm.txt',
   to_basm(Inp,Outp),
   shell('python3 bnf.py arith_bnf_asm.txt').
   
show:-
  show_bnf('progs/queens.pro').

%% to "assembler"
to_basm(F,CF):-
  tell(CF),
  run((
    file2clause(F,C),
    cls2bnf(C,(H:-B)),
    to_postfix(H,PostFixsH),
    to_postfix(B,PostFixsB),
    append([PostFixsH,[(:-)|PostFixsB],['$']],PostFixs),
    %to_postfix((H=>B),PostFixs),
    numbervars(PostFixs,0,_),
    [First|Xs]=PostFixs,
    write(First),
    run((
       member(X,Xs),
       write(' '),
       write(X)
    )),
    nl
  )),
  told.


show_bnf(F):-
   run((
     file2clause(F,C),
     cls2bnf(C,BNF),
     portray_clause(BNF),
     nl
   )).

%% returns clauses in file, one at a time
file2clause(F,C):-
  seeing(S),
  see(F),
  repeat,
    read(X),
    ( X=end_of_file,!,see(F),seen,see(S),fail
    ; C=X
    ).
    
cls2bnf(Cls,BNF):-
  clausify(Cls,(H:-Bs)),
  to_bnf((H:-Bs),BNF).
  
% normalizes clauses to H:-B form
clausify((A:-B),R):-!,R=(A:-B).
clausify(A,(A:-true)).

%% binarized implicational normal form
to_bnf((H:-Bs),(HI:-BI) ):-
  to_bin((H:-Bs),(HC:-BC)),
  fromTerm(HC,HI),
  fromTerm(BC,BI).
  
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
  
conj2list(A,[PA]):-var(A),!,to_pred(A,PA).
conj2list((A,B),[PA|Bs]):-!,lift_to_pred(A,PA),conj2list(B,Bs).
conj2list(A,[]):-A=true,!.
conj2list(A,[A]).

lift_to_pred(A,R):-var(A),!,to_pred(A,R).
lift_to_pred(A,A).

%% marks X as a user predicate p/1
to_pred(X,p(X)).
  
  
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
 
%% from term to =/2 tree
fromTerm-->listify,toBinTree.

to_postfix(Tree,Pfs):-to_postfix(Tree,Pfs,[]).

to_postfix(A)-->{var(A);atomic(A)},!,[A].
to_postfix(A=>B)-->to_postfix(A),to_postfix(B),['$'].

run(X):-X,fail;true.


