:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(C) :-
    u(D, mpart_of, A),
    u([], A, B),
    u([], B, C),
    p(D).
p(H) :-
    u(P, '[|]', A),
    u(B, A, F),
    u(J, '[|]', C),
    u(B, C, D),
    u(I, mpart_of, E),
    u(D, E, G),
    u(F, G, H),
    b(I, mpart_of, K),
    b(J, K, L),
    b(N, L, M),
    b(M, mcomplement_of, O),
    b(N, O, Q),
    b(P, Q, R),
    b(B, R, S),
    p(S).
p(D) :-
    u(E, mcomplement_of, A),
    u([], A, B),
    u([], B, C),
    u(_, C, D),
    p(E).
p(F) :-
    u(R, '[|]', A),
    u(K, A, C),
    u(G, mcomplement_of, B),
    u(H, B, D),
    u(C, D, E),
    u(M, E, F),
    b(G, mplace_element, I),
    b(H, I, J),
    b(P, J, L),
    b(K, L, N),
    b(M, N, O),
    b(O, mcomplement_of, Q),
    b(P, Q, S),
    b(R, S, T),
    b(M, T, U),
    p(U).
p(G) :-
    u(H, mplace_element, A),
    u(B, A, C),
    u(B, C, D),
    u(E, D, F),
    u(E, F, G),
    p(H).
p(I) :-
    u(D, '[|]', A),
    u(F, A, B),
    u(J, mplace_element, C),
    u(B, C, E),
    u(D, E, G),
    u(F, G, H),
    u(_, H, I),
    p(J).
p(D) :-
    u(E, eq, A),
    u(B, A, C),
    u(B, C, D),
    p(E).
p(B) :-
    u(H, goal, A),
    u(J, A, B),
    b([], '[|]', C),
    b(_, C, D),
    b(D, '[|]', E),
    b(_, E, F),
    b(F, '[|]', G),
    b(_, G, M),
    b(H, mpart_of, I),
    b(_, I, K),
    b(J, K, L),
    b(L, eq, N),
    b(M, N, O),
    b(J, O, P),
    p(P).
