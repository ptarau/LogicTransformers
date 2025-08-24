:-op(100,xfy,('=>')).

co:-
   Inp='progs/allperms.pro',
   Outp='out/bnf_asm.txt',
   to_basm(Inp,Outp).

go:-
   co,
   shell('time python3 bnf.py out/bnf_asm.txt').

bgo:-
   co,
   shell('time C/bnf/bnf/bnf out/bnf_asm.txt').

cgo:-
   co,
   shell('time C/gpt/bnf out/bnf_asm.txt').


show:-
  show_bnf('progs/arith.pro').

%% to "assembler"
to_basm(F,OutF):-
  open(OutF,write,CF),
  run((
    file2clause(F,C),
    cls2bnf(C,(H:-B)),
    to_postfix(H,PostFixsH),
    to_postfix(B,PostFixsB),
    app2([PostFixsH,[(:-)|PostFixsB],['$']],PostFixs),
    %to_postfix((H=>B),PostFixs),
    numbervars(PostFixs,0,_),
    [First|Xs]=PostFixs,
    write(CF,First),
    run((
       member(X,Xs),
       write(CF,' '),
       write(CF,X)
    )),
    nl(CF)
  )),
  close(CF).

app2([],[]).
app2([Xs|Xss],Ys):-
    app2(Xss,Zs),
    append(Xs,Zs,Ys).

show_bnf(F):-
   run((
     file2clause(F,C),
     show_clause(C),
     cls2bnf(C,BNF),
     write('\\  /'),nl,
     write(' \\/'),nl,
     clausify(C,CC),
     to_bin(CC,B),
     show_clause(B),
      write('\\  /'),nl,
     write(' \\/'),nl,
     show_clause(BNF),
     write('-------------'),nl,nl,
     nl
   )).

show_clause(C):-numbervars(C),write(C),write('.'),nl,fail;true.

%% file2clause(+File, -Clause)
%% True on backtracking for each term read from File, then fails at EOF.
file2clause(F,C):-file2clause(F,C,_).

file2clause(File, Clause,Vs) :- 
      open(File, read, In),
      read_terms_(In, Clause,[variable_names(Vs)]).

% Internal generator that reads successive terms from a stream.
read_terms_(In, Clause, Opts) :-
    read_term(In, T, Opts),
    ( T == end_of_file ->
        !, close(In), fail                      % stop the generator at EOF
    ; Clause = T                     % yield the current term
    ).
read_terms_(In, Clause,Opts) :-
    read_terms_(In, Clause,Opts).         % on backtracking, read the next term


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

to_bp(F,OutF):-
  open(OutF,write,CF),
  BC1=(bcall(X):-var(X),!),
  BC2=(bcall(X):-call(X)),
  portray_clause(CF,BC1),
  portray_clause(CF,BC2),
  run((
    file2clause(F,C,Vs),
    annotate(C,CC),
    to_bin(CC,HB),
    
    writeln(HB+Vs),
    show_clause(CF,HB,Vs)
    
  )),
  close(CF).

annotate((H:-B),R):-!,R=(H:-B).
annotate(H,(H:-bcall)).

show_clause(Stream,C,Vs):-
  run((
    maplist(call,Vs),
    arg(1,C,H),functor(H,_,N),arg(N,H,'Cont_'),
    write(Stream,C),write(Stream,'.'),nl(Stream)
  )).

b1:-
   to_bp('progs/arith.pro','out/bp.pl').