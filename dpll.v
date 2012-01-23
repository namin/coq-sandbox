(**

Last exercise from http://adam.chlipala.net/cpdt/html/Subset.html
Also see older more detailed version of similar homework at http://adam.chlipala.net/itp/hw/HW6.html

Implement the DPLL satisfiability decision procedure for boolean formulas in conjunctive normal form, with a dependent type that guarantees its correctness.  An example of a reasonable type for this function would be [forall f : formula, {truth : tvals | formulaTrue truth f} + {][forall truth, ~ formulaTrue truth f}].  Implement at least %``%#"#the basic backtracking algorithm#"#%''% as defined here:
  %\begin{center}\url{http://en.wikipedia.org/wiki/DPLL_algorithm}\end{center}%
  #<blockquote><a href="http://en.wikipedia.org/wiki/DPLL_algorithm">http://en.wikipedia.org/wiki/DPLL_algorithm</a></blockquote>#
It might also be instructive to implement the unit propagation and pure literal elimination optimizations described there or some other optimizations that have been used in modern SAT solvers.

*)

(* TODO *)