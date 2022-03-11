verify(InputFileName) :- see(InputFileName),
read(Prems), read(Goal), read(Proof),
seen,
valid_proof(Prems, Goal, Proof), write("yes").


%Om sista elementet i Proof är Goal så itererar den igenom Proof och kollar validity. 
valid_proof(Prems, Goal, Proof) :-
    check_goal(Proof, Goal),
    check_rule(Prems, Proof, []), !.

%om listan att valididate är tom lista så är vi klara. Dvs då har vi gått igenom alla rader. 
check_rule(_,[],_).

%kollar om den givna beviset är valid
check_rule(Prems, [ToProcess|ToBeProcessed], Checked):-
    valid_rule(Prems, ToProcess, Checked),
    append(Checked, [ToProcess], Concat),
    check_rule(Prems, ToBeProcessed, Concat). %rekursivt till listan av rader att gå igenom är tom
    
%CHECK BOXES
check_box(FLine, LLine, Checked):-
    member([FLine|T], Checked),
    last(T, LLine).

check_box(Line, Line, Checked):-
    member([Line], Checked).

%premiss
valid_rule(Prems, [_, Logic, premise], _):-
    member(Logic, Prems).

%antagande /assumptions
valid_rule(Prems, [[_, _, assumption]|BoxTail], Checked):-
    append(Checked, [[_, _, assumtion]], Concat),
    check_rule(Prems, BoxTail, Concat).

%imp 1
valid_rule(_, [_, Q, impel(X,Y)], Checked):- 
    member([X, P, _], Checked),
    member([Y, imp(P,Q), _], Checked).

%andel1(p,q)
valid_rule(_,[_, P, andel1(X)], Checked):-
    member([X, and(P,_), _], Checked).

%andel2(p,q)
valid_rule(_,[_, Q, andel2(X)], Checked):-
    member([X, and(_,Q), _], Checked).

%copy
valid_rule(_,[_, P, copy(X)], Checked):-
    member([X, P, _], Checked).

%andintroduction
valid_rule(_, [_, and(P,Q), andint(X,Y)], Checked):-
    member([X, P, _], Checked),
    member([Y, Q, _), Checked).

%orint1(x)
valid_rule(_, [_, or(P,_), orint1(X)], Checked):-
    member([X, P, _], Checked).

%orint2(X)
valid_rule(_, [_, or(_,Q), orint2(X)], Checked):-
    member([X, Q, _], Checked).

%Orel(X, Y, U, V, W)
valid_rule(_, [_, P, orel(X, Y, U, V, W)], Checked):-
    member([X, or(Q, D), _], Checked),
   % checkbox???
    
%impel(X,Y)
valid_rule(_, [_, Q, impel(X,Y)], Checked):-
    member([X, P, _], Checked),
    member([Y, imp(P,Q),_], Checked).

%negint(X,Y)
valid_rule(_, [_, neg(Z), negint(X, Y)], Checked) :-
    check_box([X, Z, assumption], [Y, cont, _], Checked).

%negel(X,Y)
valid_rule(_, [_, cont, negel(X,Y)], Checked):-
    member([X, P, _], Checked),
    member([Y, neg(P), _], Checked).

%contel(X) |_
valid_rule(_, [_, _, contel(X)], Checked) :-
    member([X, cont, _], Checked).

%negnegint(X)
valid_rule(_, [_, neg(neg(Logic)), negnegint(X)], Checked):-
    member([X, Logic, _], Checked).

%negnegel(X)
valid_rule(_, [_, Logic, negnegel(X)], Checked):-
    member([X, neg(neg(Logic)), _], Checked).

%MT
valid_rule(_, [_, _, mt(X,Y)], Checked):-
    member([X, imp(_, Q), _], Checked),
    member([Y, neg(Q), _], Checked).

%PBC(X,Y)
valid_rule(_, [_, P, pbc(X, Y)], Checked) :-
    check_box([X, neg(P), assumption], [Y, cont, _], Checked).
    
%Impint
valid_rule(_, [_, imp(R,S), impint(X,Y)], Checked):-
    check_box([X, R, assumption], [Y, S, _], Checked).

%LEM
valid_rule(_, [_, or(P, neg(P)), lem], _).

%kollar om goal är i sista raden
check_goal(Proof, Goal) :-
    last(Proof, [_, Goal,_]).