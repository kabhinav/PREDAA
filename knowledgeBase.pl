
                            %-----------Knowledge Base------%

tbox(equiv(a, exist(r, a))).
tbox(equiv(b, exist(r, a))).
tbox(equiv(c, exist(r, a))).
tbox(equiv(man, and(person, male))).
tbox(equiv(woman, and(person, ~man))).
tbox(equiv(mother, and(woman, exist(hasChild, person)))).
tbox(equiv(father, and(man, exist(hasChild, person)))).
