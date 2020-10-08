:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(B) :-
    u(J, goal, A),
    u(K, A, B),
    b([], '[|]', C),
    b(dd, C, D),
    b(D, '[|]', E),
    b(cc, E, F),
    b(F, '[|]', G),
    b(bb, G, H),
    b(H, '[|]', I),
    b(aa, I, M),
    b(J, perm, L),
    b(K, L, N),
    b(M, N, O),
    p(O).
p(C) :-
    u(D, perm, A),
    u([], A, B),
    u([], B, C),
    p(D).
p(E) :-
    u(O, '[|]', A),
    u(J, A, C),
    u(F, perm, B),
    u(G, B, D),
    u(C, D, E),
    b(F, ins, H),
    b(G, H, I),
    b(M, I, K),
    b(J, K, L),
    b(L, perm, N),
    b(M, N, P),
    b(O, P, Q),
    p(Q).
p(H) :-
    u(D, '[|]', A),
    u(F, A, B),
    u(I, ins, C),
    u(B, C, E),
    u(D, E, G),
    u(F, G, H),
    p(I).
p(I) :-
    u(M, '[|]', A),
    u(B, A, F),
    u(K, '[|]', C),
    u(B, C, D),
    u(J, ins, E),
    u(D, E, G),
    u(F, G, H),
    u(O, H, I),
    b(J, ins, L),
    b(K, L, N),
    b(M, N, P),
    b(O, P, Q),
    p(Q).
