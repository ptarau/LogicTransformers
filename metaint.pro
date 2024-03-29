metaint([]).        % no more goals left, succeed
metaint([G|Gs]):-   % unify the first goal with the head of a clause
   cls([G|Bs],Gs),  % build a new list of goals from the body of the  
                    % clause extended with the remaining goals as tail
   metaint(Bs).     % interpret the extended body 


cls([  add(0,X,X)                         |Tail],Tail).                   
cls([  add(s(X),Y,s(Z)), add(X,Y,Z)       |Tail],Tail). 
cls([  goal(R), add(s(s(0)),s(s(0)),R)    |Tail],Tail). 


mti:-
  metaint([goal(R)]),
  write(R),nl,
  fail.
  