bcall(A) :-
    var(A),
    !.
bcall(A) :-
    call(A).
eq(X,X,Cont_):-bcall(Cont_).
add(0,X,X,Cont_):-bcall(Cont_).
add(s(X),Y,s(Z),Cont_):-add(X,Y,Z,Cont_).
mul(0,_14738,0,Cont_):-bcall(Cont_).
mul(s(X),Y,Z,Cont_):-mul(X,Y,T,add(Y,T,Z,Cont_)).
goal(R,Cont_):-eq(X,s(s(s(0))),mul(X,X,Y,add(A,B,Y,eq(R,sum(A,B),Cont_)))).
