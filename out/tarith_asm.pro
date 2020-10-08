:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(B) :-
    u(C, goal, A),
    u(D, A, B),
    b(C, add, E),
    b(D, E, F),
    b(G, F, H),
    b(G, H, I),
    b(I, mul, J),
    b(G, J, K),
    b(L, K, M),
    b(L, M, N),
    b(N, four, O),
    b(L, O, P),
    p(P).
p(D) :-
    u(E, eq, A),
    u(B, A, C),
    u(B, C, D),
    p(E).
p(E) :-
    u(F, add, A),
    u(B, A, C),
    u(B, C, D),
    u(e, D, E),
    p(F).
p(D) :-
    u(E, add, A),
    u(F, A, B),
    u(L, B, C),
    u(R, C, D),
    b(E, s, G),
    b(F, G, H),
    b(J, H, I),
    b(I, add, K),
    b(J, K, M),
    b(L, M, N),
    b(P, N, O),
    b(O, p, Q),
    b(P, Q, S),
    b(R, S, T),
    p(T).
p(D) :-
    u(E, mul, A),
    u(e, A, B),
    u(_, B, C),
    u(e, C, D),
    p(E).
p(D) :-
    u(E, mul, A),
    u(F, A, B),
    u(I, B, C),
    u(S, C, D),
    b(E, add, G),
    b(F, G, H),
    b(L, H, J),
    b(I, J, K),
    b(K, mul, M),
    b(L, M, N),
    b(I, N, O),
    b(Q, O, P),
    b(P, p, R),
    b(Q, R, T),
    b(S, T, U),
    p(U).
p(B) :-
    u(C, four, A),
    u(D, A, B),
    b(C, s, E),
    b(D, E, F),
    b(H, F, G),
    b(G, s, I),
    b(H, I, J),
    b(L, J, K),
    b(K, s, M),
    b(L, M, N),
    b(P, N, O),
    b(O, s, Q),
    b(P, Q, R),
    b(e, R, S),
    p(S).
p(E) :-
    u(e, c, A),
    u(e, A, B),
    u(F, s, C),
    u(B, C, D),
    u(e, D, E),
    p(F).
p(E) :-
    u(M, c, A),
    u(e, A, C),
    u(F, s, B),
    u(G, B, D),
    u(C, D, E),
    b(F, q, H),
    b(G, H, I),
    b(K, I, J),
    b(J, s, L),
    b(K, L, N),
    b(M, N, O),
    p(O).
p(E) :-
    u(G, c, A),
    u(e, A, B),
    u(F, s, C),
    u(B, C, D),
    u(I, D, E),
    b(F, r, H),
    b(G, H, J),
    b(I, J, K),
    p(K).
p(H) :-
    u(B, c, A),
    u(L, A, F),
    u(B, c, C),
    u(J, C, D),
    u(I, q, E),
    u(D, E, G),
    u(F, G, H),
    b(I, s, K),
    b(J, K, M),
    b(L, M, N),
    p(N).
p(H) :-
    u(B, c, A),
    u(L, A, F),
    u(B, c, C),
    u(J, C, D),
    u(I, r, E),
    u(D, E, G),
    u(F, G, H),
    b(I, p, K),
    b(J, K, M),
    b(L, M, N),
    p(N).
p(E) :-
    u(e, c, A),
    u(e, A, C),
    u(F, p, B),
    u(e, B, D),
    u(C, D, E),
    p(F).
p(E) :-
    u(I, c, A),
    u(e, A, C),
    u(F, p, B),
    u(G, B, D),
    u(C, D, E),
    b(F, q, H),
    b(G, H, J),
    b(I, J, K),
    p(K).
p(E) :-
    u(G, c, A),
    u(e, A, B),
    u(F, p, C),
    u(B, C, D),
    u(M, D, E),
    b(F, p, H),
    b(G, H, I),
    b(K, I, J),
    b(J, r, L),
    b(K, L, N),
    b(M, N, O),
    p(O).
