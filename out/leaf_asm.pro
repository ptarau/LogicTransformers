:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(E) :-
    u(A, v, C),
    u(F, collect_leaf, B),
    u(A, B, D),
    u(C, D, E),
    p(F).
p(E) :-
    u(_, '[|]', A),
    u(I, A, C),
    u(F, collect_leaf, B),
    u(G, B, D),
    u(C, D, E),
    b(F, collect_leaf, H),
    b(G, H, J),
    b(I, J, K),
    p(K).
p(E) :-
    u(I, '[|]', A),
    u(_, A, C),
    u(F, collect_leaf, B),
    u(G, B, D),
    u(C, D, E),
    b(F, collect_leaf, H),
    b(G, H, J),
    b(I, J, K),
    p(K).
p(B) :-
    u(Z, goal, A),
    u(A1, A, B),
    b(a, v, K),
    b(b, v, C),
    b([], '[|]', D),
    b(C, D, H),
    b(M, v, E),
    b([], '[|]', F),
    b(E, F, G),
    b(G, '[|]', I),
    b(H, I, J),
    b(J, '[|]', L),
    b(K, L, X),
    b(M, v, S),
    b(e, v, P),
    b([], '[|]', N),
    b([], N, O),
    b(O, '[|]', Q),
    b(P, Q, R),
    b(R, '[|]', T),
    b(S, T, U),
    b([], '[|]', V),
    b(U, V, W),
    b(W, '[|]', Y),
    b(X, Y, C1),
    b(Z, collect_leaf, B1),
    b(A1, B1, D1),
    b(C1, D1, E1),
    p(E1).
