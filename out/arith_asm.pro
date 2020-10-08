:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(D) :-
    u(E, eq, A),
    u(B, A, C),
    u(B, C, D),
    p(E).
p(E) :-
    u(F, add, A),
    u(B, A, C),
    u(B, C, D),
    u(0, D, E),
    p(F).
p(F) :-
    u(L, s, D),
    u(H, s, A),
    u(G, add, B),
    u(A, B, C),
    u(J, C, E),
    u(D, E, F),
    b(G, add, I),
    b(H, I, K),
    b(J, K, M),
    b(L, M, N),
    p(N).
p(D) :-
    u(E, mul, A),
    u(0, A, B),
    u(_, B, C),
    u(0, C, D),
    p(E).
p(E) :-
    u(P, s, C),
    u(F, mul, A),
    u(G, A, B),
    u(J, B, D),
    u(C, D, E),
    b(F, add, H),
    b(G, H, I),
    b(M, I, K),
    b(J, K, L),
    b(L, mul, N),
    b(M, N, O),
    b(J, O, Q),
    b(P, Q, R),
    p(R).
p(B) :-
    u(F, goal, A),
    u(I, A, B),
    b(0, s, C),
    b(C, s, D),
    b(D, s, X),
    b(M, sum, E),
    b(O, E, G),
    b(F, eq, H),
    b(G, H, J),
    b(I, J, K),
    b(K, add, L),
    b(R, L, N),
    b(M, N, P),
    b(O, P, Q),
    b(Q, mul, S),
    b(R, S, T),
    b(U, T, V),
    b(U, V, W),
    b(W, eq, Y),
    b(X, Y, Z),
    b(U, Z, A1),
    p(A1).
