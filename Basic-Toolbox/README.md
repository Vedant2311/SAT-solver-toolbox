# Basic-Propositional-Logic-Toolbox

Considered the representation of propositions in OCaml as a data type:

     type prop =  T | F | L of string 
                  | Not of prop
                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop;;

Defined the following syntax-directed functions:

    1. ht: prop -> int, which returns the height of a proposition (considered a syntax tree). A leaf is at height 0
    2. size: prop -> int, which returns the number of nodes in a proposition (considered a syntax tree)
    3. letters: prop -> string set, which returns the set of propositional letters
    4. subprop_at: prop -> prop -> path set which yields the set of paths in the tree of p2 leading from its root to a position which is the root of an occurrence of p1, assuming p1 is a sub-proposition of p2, and raising an exception NotSubProp otherwise. A path is coded as a bit-string (0=left, 1=right)

Defined the semantic function, using the standard truth tables for the connectives.

    truth: prop -> (string -> bool) -> bool

I also implemented the conversion of an input proposition into the different forms (which is very useful for the problems like Satisfiability):

* A proposition is in negation normal form (NNF)  if

         1. it does not contain the connectives Impl and Iff 
         2. it does not contain sub-propositions of the form "Not T" and "Not F"
         3. it does not contain any sub-proposition of the form "Not (Not p)"
         4. It does not contain any  path in which an occurrence of Not appears at a position closer to the root than occurrences of And or Or connectives on that path.

*  A proposition is in Disjunctive normal form (DNF) or Sum of Products Form if 

         1. it is in NNF
         2. It does not contain any  path in which an occurrence of the And connective appears at a position closer to the root than occurrences of Or connectives on that path.

* A proposition is in Conjunctive normal form (CNF) or Product of Sums form if 

         1. it is in NNF
         2. It does not contain any  path in which an occurrence of the Or connective appears at a position closer to the root than occurrences of And connectives on that path.

* The following functions were implemented for the same

          1. nnf: prop -> prop,  which converts any proposition into a logically equivalent one in  NNF.
          2. cnf: prop -> prop,  which converts any proposition into  a logically equivalent one in CNF.
          3. dnf: prop -> prop,  which converts any proposition into  a logically equivalent one in DNF.
