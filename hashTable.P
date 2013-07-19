%Add an entry to Hash Table

putHash(Hash, Value):- assert(hash(Hash, Value)).

%Retrive an entry

getHash(Hash, Value):- hash(Hash, Value).

%dete table or entry

removeT:- retractall(hash(_,_)).

removeE(Entry):- retract(hash(Entry, _)).