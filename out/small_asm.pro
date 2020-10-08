:- op(100, xfy, =>).
% QUERY THIS WITH: ?- Answer => _ => goal.

u(A, B, A=>B).
b(A, B, A=>B).
p(A) :-
    var(A),
    !,
    A=true.
p(B) :-
    u(C, try, A),
    u(bbb, A, B),
    p(C).
p(B) :-
    u(C, try, A),
    u(ccc, A, B),
    p(C).
p(B) :-
    u(C, goal, A),
    u(D, A, B),
    b(C, try, E),
    b(D, E, F),
    p(F).
