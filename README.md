# SAT-solver-toolbox

This is a collection of the implementation of the proof systems of Analytic-Tableaux, Hilbert, Natural-Deduction, First-Order-Resolution, and Reducted-Order-Binary-Decision-Diagrams (ROBDD) in Ocaml. An important purpose of this project was to have a standard Ocaml implementation of different methods for efficiently solving the SAT-problem using proof systems. Note that, the systems of Hilbert and Natural-Deduction are not used for solving SAT.

A basic propositional language is implemented on top of which these different systems are built. This can be found in the directory **Basic-Toolbox**. Note that the proof system of Resolution is implemented for first order logic (the implementation for Propositional logic will be very trivial as compared to that), and a similar toy language for first order logic is implemented there. 

These different proof systems have been explained and documented thoroughly in their respective directories.
