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
p(F) :-
    u(_, '[|]', A),
    u(D, A, B),
    u(G, memb, C),
    u(B, C, E),
    u(D, E, F),
    p(G).
p(E) :-
    u(G, '[|]', A),
    u(_, A, B),
    u(F, memb, C),
    u(B, C, D),
    u(I, D, E),
    b(F, memb, H),
    b(G, H, J),
    b(I, J, K),
    p(K).
p(B) :-
    u(H, goal, A),
    u(J, A, B),
    b([], '[|]', C),
    b(cc, C, D),
    b(D, '[|]', E),
    b(bb, E, F),
    b(F, '[|]', G),
    b(aa, G, M),
    b(H, eq, I),
    b(O, I, K),
    b(J, K, L),
    b(L, memb, N),
    b(M, N, P),
    b(O, P, Q),
    p(Q).
