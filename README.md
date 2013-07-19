PREDAA
======

[Practical Reasoning in Expressive Description Logic using Alternating Automata](http://pro.unibz.it/library/thesis/00006468S\_14424.pdf)

<p align="justify">
Description Logic (DL) languages have become a de-facto standard for Knowledge Representation
in recent times. They helps us in capturing the terminological knowledge of
the targeted domain in a precise manner. By using DLs, the knowledge of the application
domain can be represented in a formal way enabling the Knowledge Representation Systems
based on DLs to perform various kinds of inference tasks like satisfiability checking,
instance checking, subsumption etc. These reasoning capabilities allow us to find implicit
consequences of the explicitly represented knowledge and thereby facilitating the development
of smart applications. The traditional way of reasoning in Description Logics is based
on the tableau algorithms. Though the tableau algorithms have performed well for reasoning
in DLs, they do not have the optimal worst-case complexity for a given DL. Due to
this the worst-case complexity bounds for a logic are usually proven by the theoretically
optimal automata-based algorithms. Thus, the researchers often end up in creating two
algorithms for a new logic, one automata-based for proving the exact complexity bounds of
the logic and another a tableau-based for a practical implementation. The problem with
the automata-based algorithms is that in spite of having nice theoretical properties they
have best-case exponential behavior. Due to this, to the best of our knowledge, there was
no attempt made for developing an automata-based reasoning tool for DLs.
</p>

<p align="justify">
In this work we investigate the novel possibility of developing automata-based reasoning
tool for DL ALC. We obtain our results by an innovative approach of dividing the input
concept into smaller sub-concepts and then checking the satisability of these sub-concepts
in an incremental fashion, inspired by the recent work on checking the satifiability of u-
calculus formulas using the automata-based algorithms. This involves handling of technical
challenges like deciding subsumption in the presence of a cyclic TBox. We introduce the
definitions of alternating looping tree automata (ALT), universal looping tree automata
(ULT), non-deterministic looping tree automata (NLT) and investigate the decomposition
of ALT to ULT and ULT to NLT transformations. Then we provide an incremental satisfaction
algorithm for deciding satisability using automata-based technique. When combined
together, they provide a decision procedure for DL ALC. We also present a prototype implementation
of the proposed algorithm in programming language Prolog. This preliminary
implementation is then compared with an optimized tableau algorithm implementation for
characterizing the strengths and weaknesses of the proposed approach.
</p>

[Full Text](http://pro.unibz.it/library/thesis/00006468S\_14424.pdf)