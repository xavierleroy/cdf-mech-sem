# Mechanized semantics: the Coq development

This repository contains the Coq sources for the course
["Mechanized semantics"](https://www.college-de-france.fr/site/xavier-leroy/course-2019-2020.htm)
given by Xavier Leroy at Collège de France in 2019-2020.  

This is the English version of the Coq sources.  La version commentée en français est disponible [ici](https://github.com/xavierleroy/cdf-sem-meca).

An HTML pretty-printing of the commented sources is also available:

1. The semantics of an imperative language
   * Module [IMP](https://xavierleroy.org/cdf-mech-sem/CDF.IMP.html): the imperative language IMP and its various semantics.
   * Library [Sequences](https://xavierleroy.org/cdf-mech-sem/CDF.Sequences.html): definitions and properties of reduction sequences.

2. Formal verification of a compiler
   * Module [Compil](https://xavierleroy.org/cdf-mech-sem/CDF.Compil.html): compiling IMP to a virtual machine.
   * Library [Simulation](https://xavierleroy.org/cdf-mech-sem/CDF.Simulation.html): simulation diagrams between two transition systems.

3. Optimizations, static analyses, and their verification
   * Module [Optim](https://xavierleroy.org/cdf-mech-sem/CDF.Optim.html): optimizations based on liveness analysis.
   * Library [Fixpoints](https://xavierleroy.org/cdf-mech-sem/CDF.Fixpoints.html): computing fixed points by Knaster-Tarski iteration.

4. Logics to reason about programs
   * Module [HoareLogic](https://xavierleroy.org/cdf-mech-sem/CDF.HoareLogic.html): Hoare logics for IMP
   * Module [SepLogic](https://xavierleroy.org/cdf-mech-sem/CDF.SepLogic.html): a separation logic for IMP plus pointers and dynamic allocation.

5. Static analysis by abstract interpretation
   * Module [AbstrInterp](https://xavierleroy.org/cdf-mech-sem/CDF.AbstrInterp.html): a static analyzer based on abstract interpretation.
   * Module [AbstrInterp2](https://xavierleroy.org/cdf-mech-sem/CDF.AbstrInterp2.html): improvements to the previous static analyzer.

6. Semantics of divergence
   * Module [Divergence](https://xavierleroy.org/cdf-mech-sem/CDF.Divergence.html): classical denotational semantics; coinductive natural semantics.
   * Module [Partiality](https://xavierleroy.org/cdf-mech-sem/CDF.Partiality.html): the partiality monad, with application to constructive denotational semantics.

7. Semantics and typing of a functional language
   * Module [FUN](https://xavierleroy.org/cdf-mech-sem/CDF.FUN.html): the functional language FUN and its type system.

