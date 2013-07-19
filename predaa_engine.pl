%Compliler Directives.
:- set_global_compiler_options(+optimize).
:- table transitionATA0/5, alphNodRes/7, alphNodRes1/6, alphNodRes1/4, alphULT0/6, transitionNLT0/3, search/6.	
:- dynamic hash/2.
	
%Useful In-built Predicates.
:- import member/2, memberchk/2 from basics.
:- import subset/2 from basics.
:- import absmerge/3 from listutil.
:- import tsetof/3, setof/3 from setof.
:- import profile_call/1 from xsb_profiling.

%consult useful Packages
%:- consult(hashTable).

%New Operators Definitions.
:- op(100, fy, ~). %Defining the negation operator.
:- op(600, yfx, \). %Defining the list difference operator.

				% -------------- Useful Predicates----------
%Length of the input list.
count([], 0).
count([_ | T], C):- count(T, C1), C is C1 + 1.

%Delete element X from the list and return resulting list.
del(X,[X|Tail],Tail).
del(X,[Y|Tail],[Y|Tail1]) :- del(X,Tail,Tail1).

%append 
mappend([], Ys, Ys).
mappend([H | T], L2, [H| Sol]):- mappend(T, L2, Sol).
	
%flatten(Xs, Ys) as difference lists.
flatten(Xs, Ys):- flatten_dl(Xs, Ys\[]).
flatten_dl([X|Xs], Ys\Zs):- flatten_dl(X, Ys\Ys1), flatten_dl(Xs, Ys1\Zs).
flatten_dl(X, [X|Xs]\Xs):- atom(X), X \= [].
flatten_dl([], Xs\Xs).

%Removing duplicates
set([], []).
set([H| T], R) :- memberchk(H, T), !, set(T, R).
set([H | T], [H | R]) :- set(T, R).

% Taking difference of two lists 
diff([X|Y], Z, W) :-  memberchk(X,Z), !, diff(Y,Z,W).
diff([X|Y],Z,[X|W]):- diff(Y,Z,W).
diff([],_,[]).

% Union of two list.
union([X|Y],Z,W) :- memberchk(X,Z), !, union(Y,Z,W).
union([X|Y],Z,[X|W]) :- union(Y,Z,W).
union([],Z,Z).

% representing empty set
emptyset([]).

notemptyset(X) :- member(_, X).

% Power Set of a given List
power([], [[]]).
power([Head | Tail], Power) :- power( Tail, PowerTail),
                               add_head( Head, PowerTail, HeadPowerTail), 
                               mappend(HeadPowerTail, PowerTail, Power).

add_head( _, [], []).
add_head( Head, [List1 | Lists], [[Head | List1] | HeadLists]) :- add_head(Head, Lists, HeadLists). 


% Implementing Stack 
empty([]).
pop(Item, [Item | NewStack], NewStack).
push(Item, OldStack, [Item | OldStack]).

%Hash Table for check/3
%Add an entry to Hash Table

putHash(Hash, Value):- assert(hash(Hash, Value)).

%Retrive an entry

getHash(Hash, Value):- hash(Hash, Value).

%delete table or entry
removeT:- retractall(hash(_,_)).
removeE(Entry):- retract(hash(Entry, _)).

%Retriving a transition from the AlphULT predicate respone
getTrans([], _, []).
getTrans([(X,Y)| _], X, Y).
getTrans([_|T], A, Sol):- getTrans(T, A, Sol).


			   %---------Negation Normal Form---- %

nnf(~ ~X, X1):- nnf(X, X1).

nnf(~forall(X, Y), exist(X, Y1)):- nnf(~Y, Y1).
nnf(forall(X, Y), forall(X, Y1)):- nnf(Y, Y1).

nnf(~exist(X, Y), forall(X, Y1)):- nnf(~Y, Y1).
nnf(exist(X, Y), exist(X, Y1)):- nnf(Y, Y1).

nnf(~and(X,Y), or(X1,Y1)):- nnf(~X, X1), nnf(~Y, Y1). 
nnf(and(X, Y), and(X1, Y1)):- nnf(X, X1), nnf(Y, Y1).

nnf(~or(X,Y), and(X1,Y1)):- nnf(~X, X1), nnf(~Y, Y1). 
nnf(or(X, Y), or(X1, Y1)):- nnf(X, X1), nnf(Y, Y1).

nnf(~X, ~X):- atom(X).
nnf(X, X):- atom(X).


                           %---Constructing Alternating Automata of Input.----


%%Identifying Concepts and Roles.

con(~A, RAcc, A1):- con(A, RAcc, A1).
con(forall(X, Y), [X| R], Y1):- con(Y, R, Y1).
con(exist(X, Y),  [X| R], Y1):- con(Y, R, Y1).
con(and(X, Y), R, Sol):- con(X, R1, X1), con(Y, R2, Y1), mappend(X1, Y1, Sol), mappend(R1, R2, R).
con(or(X, Y), R, Sol):- con(X, R1, X1), con(Y, R2, Y1), mappend(X1, Y1, Sol), mappend(R1, R2, R).
con(X, [], [X]):- atom(X).

negRole1([], []).
negRole1(Nr, NRol):- member(X, Nr), NRol = ~X.
negRole(RList, NNr):- setof(NRol, negRole1(RList, NRol), NNr).

%% Subconcepts of an input concept

sub(~A, [~A | R]):- sub(A, R).
sub(forall(X, Y), [forall(X, Y)| R]):- sub(Y, R).
sub(exist(X, Y), [exist(X, Y) | R]):- sub(Y, R).
sub(and(X, Y),  [and(X, Y)| R]):- sub(X, R1), sub(Y, R2), mappend(R1, R2, R). 
sub(or(X, Y), [or(X, Y) | R]):- sub(X, R1), sub(Y, R2), mappend(R1, R2, R).
sub(X, [X]):- atom(X).


%% Counting the number of existential restriction
nExist(~A, Nex):- nExist(A, Nex).
nExist(forall(_, Y), Nex):- nExist(Y, Nex).
nExist(exist(_, Y),  Nex):- nExist(Y, Nex1), Nex is Nex1+1.
nExist(and(X, Y), Nex):- nExist(X, Nex1), nExist(Y, Nex2), Nex is Nex1+Nex2.
nExist(or(X, Y),  Nex):- nExist(X, Nex1), nExist(Y, Nex2), Nex is Nex1+Nex2.
nExist(X, 0):- atom(X).
	
% Set of States.
nodeATA0(C, Q):- sub(C, Sc), con(C, Nr, _), union(Nr, Sc, CR),
	         (Nr \= [] -> negRole(Nr, NNr)), union(NNr, CR, CNR),
		 union([true, false, start, #], CNR, Q), !. 

nodeATA0(C, Q):- sub(C, Sc), union([true, start, #], Sc, Q). 

% Alphabet
alphATA0(C, A):- con(C, Rol, Con), set(Rol, Nr), set(Con, Nc), union(Nc, Nr, U),
	         power(U, AList), union(AList,[[#]], A).

% Start Node

startATA0(start).

%Transition Rules

transforAll(0, forall(X, Y), [R]):- (R = (0, ~X)); (R = (0, Y)).
transforAll(K, forall(X, Y), [R1|R2]):- K > 0, (R1 = (K, ~X); R1 = (K, Y); R1 = (K, #)),
	                          K1 is K-1, transforAll(K1, forall(X, Y), R2).
				  %mappend(R2, R1, R).

transExist(1, exist(X, Y), [(1, X), (1, Y)]).
transExist(K, exist(X, Y), R):- K > 1, ((R = [(K, X),(K, Y)]); (K1 is K-1, transExist(K1, exist(X, Y), R))).

transitionATA0(C, start, _, _, [(0,C)]):- !.

transitionATA0(_, true, _, _, [(0, true)]):- !.
transitionATA0(_, false, _, _, [(0, false)]):- !.

transitionATA0(_, ~Q, A, _, [R]):- atom(Q), Q \= gci, Q \= #, A \= [#],not(memberchk(Q,A)), R = (0, true).
transitionATA0(_, ~Q, A, _, [R]):- atom(Q), Q \= gci, Q \= #, A \= [#],memberchk(Q, A), R = (0, false).
transitionATA0(_, Q, A, _, [R]):- atom(Q), Q \= gci,  Q \= #, A \= [#],memberchk(Q, A),R = (0, true).
transitionATA0(_, Q, A, _, [R]):- atom(Q), Q \= gci,  Q \= #, A \= [#],not(memberchk(Q, A)), R = (0, false).

transitionATA0(_, and(X, Y), _, _, [(0, X),(0, Y)]).
transitionATA0(_, or(X, Y), _, _, [R]):- (R = (0, X)); (R = (0, Y)).

transitionATA0(_, exist(X, Y), _, K, R):-   transExist(K, exist(X, Y), R).	

transitionATA0(_, forall(X, Y), _, K, R):-  transforAll(K, forall(X,Y), R).	

transitionATA0(_, #, A, _, [R]):-  A == [#], R = (0, true), !.
transitionATA0(_, #, A, _, [R]):- A \= [#], R = (0, false), !.

transitionATA0(_, #, [#], _, [(0, true)]).
%transitionATA0(_, Q, [#], _, [R]):- Q \= gci,  Q \= #, R = (0, false), !.


				%-----Step 1: ALT to ULT---

%Computing restrictions
                                            				     
relevantA0(C, (Q, R), K, A):-   transitionATA0(C, Q, A, K, R). %more than one transition in case of 'or'.

/* Predicate is applicable only if the alphabet is present in InAlph and only new transitions are added.*/
alphNodRes1(C, K, NListPrev, NList, A, (N,R)):- nodeATA0(C, NList),
	                                     diff(NList, NListPrev, NListRes),
	                                     member(N, NListRes),relevantA0(C, (N, R), K, A).

alphNodRes(C, K, NListPrev, NList,  InAlph, A, R):-  alphATA0(C, AList),  member(A, AList),
	                        A \= [], memberchk((A, _), InAlph),
				tsetof((Nod, Res), alphNodRes1(C, K, NListPrev, NList, A, (Nod,Res)), TeR),
	                        delTrans(InAlph, A, InAlphMod), union(TeR, InAlphMod, UR), set(UR, R).

%% If alphbet is introduced new.
alphNodRes1(C, K, A, (N,R)):- nodeATA0(C, NList), member(N, NList), relevantA0(C, (N,R), K, A).
alphNodRes(C, K, _, NList, InAlph, A, R):-  nodeATA0(C, NList), alphATA0(C, AList),
	                        member(A, AList),  A \= [], not(memberchk((A, _), InAlph)),
	                        tsetof((Nod, Res), alphNodRes1(C, K, A, (Nod,Res)), R).

delTrans([], _, []).
delTrans([(X, Y)| _], X, T):- del((start,_), Y, T), !. 
delTrans([_|T], A, Sol):- delTrans(T, A, Sol).

%testAlph(C):- alph(C, A), alphULT0(a, [], _, [], Alph), memberchk((A, _), Alph).


				%----- Starting construction of ULT-----

%%alphULT0(C, A) :-  tsetof((Alph, Res), alphNodRes(C, Alph, Res), A). 

alphULT0(C, K, NListPrev, NList, InAlph, A):- tsetof((Alph, Res), alphNodRes(C, K, NListPrev, NList, InAlph, Alph, Res), A).
	                                    

nodeULT0(C, Q) :-  nodeATA0(C, Q).

startULT0(0, Q) :- startATA0(Q).

% Transitions of ULT 
temp2trULT0(Q, (A, R), X1):-  member((Q, X1), R).
transitionULT0(Q, A, T) :-  temp2trULT0(Q, A, T).

%testULT(C, Alph, Trans):- alphULT0(C, Alist), member(Alph, Alist), transitionULT0(C, Alph, Trans).


                          %---------- Step 2: ULT to NLT ------------

%%alphNLT0(C, A):- alphULT0(C, A).

alphNLT0(C, K, NListPrev, NList, InAlph, A):- alphULT0(C, K, NListPrev, NList, InAlph, A).

nodeNLT0(C, NList, Qn):- nodeATA0(C, NList), power(NList, Qn).

startNLT0([Q1]) :- startULT0(0, Q1).

% definitions for the transition relation of NLT

sat3(Q, Count, Nod):- member((Count, Nod), Q).
sat3(Q, Count, #):- not(member((Count, _), Q)).

sat2(Q, Count, Count, [Nod]):- setof(N, sat3(Q, Count, N), Nod).
sat2(Q, Count, K, Nod):- Count < K, setof(N, sat3(Q, Count, N), Sat2),
	                 Count1 is Count+1, sat2(Q, Count1, K, N1), 
			 mappend([Sat2], N1, Nod).

sat(S, A, K,Q):-  transitionULT0(S, A, R), sat2(R, 0, K, Q).

transitionNLT0(S, A, T):- nExist(S, K), sat(S, A, K, T).

%%testNLT(C, Alph, Trans):- nnf(C, N), alphNLT0(C, Alist), member(Alph, Alist), transitionNLT0(N, Alph, Trans).


				%--------------Emptiness Test----------------

% Transitive Closure
path(A, X, Y, P):- path(A, X, Y, [X], P).

path(_, X, X, Path, Path):- !.
path(A, X, Y, Pin, Pout):- transitionNLT0(X, A, Trans), member(Z, Trans),
	                   count(Z, 1), 
	                   member(Z1, Z), not(memberchk(Z1, Pin)),
	                   path(A, Z1, Y, [Z1|Pin], Pout).

path(A, X, Y, Pin, Pout):- transitionNLT0(X, A, Trans), member(Z, Trans),
	                   not(count(Z, 1)), 
	                   allpath(A, Z, Y, Pin, Pout).


allpath(_, [], _, Path, Path).
allpath(A, [H|T], Y, Pin, Pout):-  path(A, H, Y, Pin, PTemp), union([PTemp], Pin, Pin1), !, allpath(A, T, Y, Pin1, Pout).

% Second emptiness test (a bit more efficient)

checkHash([H | T], Acc, Sol) :-  getHash(H, _), !, checkHash(T, Acc, Sol).
checkHash([H | T], Acc, Sol) :- checkHash(T, [H | Acc], Sol).
checkHash([], Sol, Sol).

head(H, [H | _]).

%echk([], _, 'No').
echk([true|_], _, 'Yes'):- !.
echk([H|T],A, Sol):- transitionNLT0(H, A, Trans), member(X, Trans), 
	          checkHash(X, [], TransList), TransList \= [],!,  
		  (count(X, 1) -> (head(Y, TransList),
		  (Y \= true -> (putHash(Y, 1),push(Y, [H|T], S1)); push(Y, [H|T], S1)),
                  echk(S1, A, Sol));  echkAnd(X, A, Sol)).

/*echk([H|_],A, Sol):- transitionNLT0(H, A, Trans), member(X, Trans), not(count(X, 1)), 
	          checkHash(Trans, [], TransList), TransList \= [],!,
		  echkAnd(X, A, Sol).*/

echk([_|T], A, Sol):- echk(T, A, Sol).

echkAnd([], _, []).
echkAnd([H |T], A, [Sol1 | Sol]):- echk([H], A, Sol1), !,echkAnd(T, A, Sol). 

check(C, A, Res):- removeT, push(C, [], S1), echk(S1, A, Res). 



% Search Initialization

alph(C, K, NListPrev, NList, InAlph, A, AList):- alphNLT0(C, K, NListPrev, NList, InAlph, AList), member(A, AList).

search(C, NListPrev, NList, InAlph, OutAlph, (Alph, Sol)):- startNLT0([N]), nExist(C, K),
	                     alph(C, K, NListPrev, NList, InAlph, (Alph, Res), OutAlph),
	                     Alph \=[#], check(N, (Alph, Res), Sol), /*path((Alph, Res), N, true, Sol),*/ !.

%testCheck(C, A, Sol):- nExist(C, K), alph(C, K, [], _, [], A, _),  check(C, A, Sol).


/* ISA */

isa(List, Sol):- isa1(List,[], [], Sol).

isa1([],_,  _, []).
isa1([C| Tail], NList, InAlph, [R | Sol]):- 
	                     write('\t Concept Tested:'), write(C), 
			     search(C, NList, NListNew, InAlph, NowAlph, R),
			     write('\t Concept Satisfiable:'), write(C),nl,
			     mappend(InAlph, NowAlph, OutAlph),
			     del(start, NListNew, NListNew1),
			     union(NList, NListNew1, NListOut),
			     isa1(Tail, NListOut,OutAlph, Sol).



/**  Construct Goal **/

check(subsum(A, B), Sol):- not(isa(and(A, ~B), Sol)).


