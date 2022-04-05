% closed lambda term generator
genClosed(L,T):-genClosed(T,0,L,0).

genClosed(0,s(0),s(N),N).
genClosed(s(X),s(X),N1,N2):- sub(N1,s(X),s(N2)).
genClosed(l(A),V,s(N1),N2):-
  genClosed(A,s(V),N1,N2).
genClosed(a(A,B),V,s(N1),N3):-
  genClosed(A,V,N1,N2),
  genClosed(B,V,N2,N3).

sub(X,0,X).
sub(s(X),s(Y),Z):-sub(X,Y,Z).

goal(T):-genClosed(s(s(s(s(s(0))))),T).
