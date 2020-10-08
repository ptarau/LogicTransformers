:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(B) :-
    u(F1, goal, A),
    u(G1, A, B),
    b([], '[|]', C),
    b(15, C, D),
    b(D, '[|]', E),
    b(14, E, F),
    b(F, '[|]', G),
    b(13, G, H),
    b(H, '[|]', I),
    b(12, I, J),
    b(J, '[|]', K),
    b(11, K, L),
    b(L, '[|]', M),
    b(10, M, N),
    b(N, '[|]', O),
    b(9, O, P),
    b(P, '[|]', Q),
    b(8, Q, R),
    b(R, '[|]', S),
    b(7, S, T),
    b(T, '[|]', U),
    b(6, U, V),
    b(V, '[|]', W),
    b(5, W, X),
    b(X, '[|]', Y),
    b(4, Y, Z),
    b(Z, '[|]', A1),
    b(3, A1, B1),
    b(B1, '[|]', C1),
    b(2, C1, D1),
    b(D1, '[|]', E1),
    b(1, E1, I1),
    b(F1, nrev, H1),
    b(G1, H1, J1),
    b(I1, J1, K1),
    p(K1).
p(C) :-
    u(D, nrev, A),
    u([], A, B),
    u([], B, C),
    p(D).
p(E) :-
    u(Q, '[|]', A),
    u(F, A, C),
    u(H, nrev, B),
    u(I, B, D),
    u(C, D, E),
    b([], '[|]', G),
    b(F, G, K),
    b(H, app, J),
    b(I, J, L),
    b(K, L, M),
    b(O, M, N),
    b(N, nrev, P),
    b(O, P, R),
    b(Q, R, S),
    p(S).
p(E) :-
    u(F, app, A),
    u(B, A, C),
    u(B, C, D),
    u([], D, E),
    p(F).
p(I) :-
    u(O, '[|]', A),
    u(B, A, G),
    u(K, '[|]', C),
    u(B, C, D),
    u(J, app, E),
    u(D, E, F),
    u(M, F, H),
    u(G, H, I),
    b(J, app, L),
    b(K, L, N),
    b(M, N, P),
    b(O, P, Q),
    p(Q).
