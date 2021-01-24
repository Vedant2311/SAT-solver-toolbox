# First-Order-Resolution-Proof-System

## Constructing the First Order logic 

The representation of "pre-terms" is given, using the following data type definition:

    type term = V of variable | Node of symbol * (term list);;

A signature is constructed consisting of symbols and their arities (>= 0) as a list of (symbol, arity) pairs. The first half of the ocaml code present here deals with constructing the First Order logic system and the second half uses that language in order to implement the First Order Resolution proof system.

The function **check_sig** checks that whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)

Given a valid signature (checked using check_sig), the function **wfterm** checks that a given preterm is well-formed according to the signature

The functions **ht**, **size** and **vars** take a well-formed term according to the signature and return its height, its size and the set of variables appearing in it respectively

The function **subst t s** takes the term **t** and the function **s** and gives out the substitution as per applying the Homomorphism. The function **compose** gives a composition of substitutions. 

The function **mgu** takes two terms t1 and t2, and returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.

These are the main functions implemented for the construction of a **Sigma Algebra** and the terms defined here and these functions are used for the **Resolution proof system**. 

It is advised to go through the code in order to understand the functioning of these functions and get the examples in orer to understand the usage and working of these.

## The Resolution Proof system

Now, treating an atomic proposition as a pseudo-term (where the root symbol is a predicate symbol rather than a function symbol), a sets of clauses is represented, where each clause is a set of literals, where a literal is an atomic proposition or the negation of an atomic proposition.

The function **findTwoClauses** is used to select two clauses where one has a positive literal and the other a negative literal, such that the positive forms can be unified

The function **oneStep** does the one step resolution of two given clauses. And the function **resolution c []** does the resolution of the set of Clauses **c** and returns whether the Set of clauses is satisfied or not. Also, the list which is passed to these functions corresponds to the Tuple of the previously resolved clauses, so that the function doesn't get stuck in an infinite recursion trying to solve the same clauses again and again. Also, note that this list is to be passed as **[]** only (i.e an empty list) for the **resolution** function.

### Selecting any two clauses and giving their one-step resolution
We make use of the first order logic language as creater earlier and create three different pre-terms that would be used as literals in the different clauses ahead.
```ocaml
let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
let term3 = Node("e",[Node("c",[]);V("x");Node("d",[Node("d",[Node("a",[]);Node("c",[])]);V("x")])]);;

let term1 = Term(term1);;
let term2 = Term(term2);;
let term3 = Term(term3);;
```

Now, we create five different clauses using these literals as:
```ocaml
let c1 = [term1;term2;term3];;
let c2 = [term1;term3];;
let c3 = [Not(term1);term2];;
let c4 = [Not(term2);term3];;
let c5 = [Not(term3);term1];;
let c = [c1;c2;c3;c4;c5];;
```

Now, we would first find two clauses which have the same literal with opposite polarities that would help in performing the resolution step.
```ocaml
let (a,b) = findTwoClauses c [];;
```

The above function call will return two clauses, c1 and c3 and the common literal (in the base form) is term1. Note that here, we pass an empty list as well to the function as no clauses in c have been resolved yet. Then, we will perform a one-step resolution. The unification will be unity here.
```ocaml
oneStep (a,b) [];;
- : prop list =
	[Term
	  (Node ("e",
		[Node ("c", []); V "x";
		 Node ("d", [Node ("d", [Node ("a", []); Node ("c", [])]); V "x"])]));
	 Term
	  (Node ("e",
		[Node ("c", []); Node ("c", []);
		 Node ("d", [Node ("d", [Node ("a", []); V "z"]); V "x"])]))]
```

After resolving c1 and c3 w.r.t term1, we can find other clauses to be resolved and so on. If we want to perform a second unit-step resolution, then we would need to instruct the program that the previous resolution has happened to the system. For that, we would add the tuple (c1, term1, c3, Not(term1)) to the list and perform the same steps.
```ocaml
let (a,b) = findTwoClauses c [(c1,term1,c3,Not(term1))];;

oneStep (a,b) [(c1,term1,c3,Not(term1))];;
- : prop list =
	[Term
	  (Node ("e",
	    [Node ("c", []); Node ("c", []);
	     Node ("d", [Node ("d", [Node ("a", []); V "z"]); Node ("c", [])])]));
	 Term
	  (Node ("e",
	    [Node ("c", []); Node ("c", []);
	     Node ("d",
	      [Node ("d", [Node ("a", []); Node ("c", [])]); Node ("c", [])])]))]
```

It can even happen that the program is unable to find any such clauses to be resolved. In that case, the function would throw an exception.
```ocaml
let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let term2 = Node("e",[Node("c1",[]);Node("c1",[]);Node("d1",[Node("d1",[Node("a1",[]);V("z1")]);V("x1")])]);;

let term1 = Term(term1);;
let term2 = Term(term2);;

let c1 = [Not(term1)];;
let c2 = [term2];;

let c = [c1;c2];;

findTwoClauses c [];;
- Exception: Myexp "Can't find any more!".
```

### Making use of the resolution function
We provide two different examples corresponding to the usage of the resolution function with the case of Horn clauses being present. The resolution function will terminate giving the corresponding final result. As stated earlier, the list to be passed to this function should always be empty as we assume the system to be such that no resolution has been done yet.
```ocaml
(* The First Example *)
let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
   	   
let term1 = Term(term1);;
let term2 = Term(term2);;

let c1 = [Not(term1);term2];;
let c2 = [term1; Not(term2)];;
let c3 = [Not(term1);Not(term2)];;
let c4 = [term2];;
let c = [c1;c2;c3;c4];;

resolution c [];;
- : string = "Successful"

(* The Second Example *)
let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
   	   
let term1 = Term(term1);;
let term2 = Term(term2);;

let c1 = [term1;Not(term1)];;
let c2 = [term2];;

let c = [c1;c2];;

resolution c [];;	-
- : string = "Unsuccesful"
```

Note that it is recommended to perform step-wise updates if you intend to use these functions, as for the **resolution** function there is a possibility that the code does not terminate in case a resolvent clause is empty. The following example kept running for more than 15 mins without terminating.
```ocaml
let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
let term3 = Node("e",[Node("c",[]);V("x");Node("d",[Node("d",[Node("a",[]);Node("c",[])]);V("x")])]);;

let term1 = Term(term1);;
let term2 = Term(term2);;
let term3 = Term(term3);;

let c1 = [term1;term2;term3];;
let c2 = [term1;term3];;
let c3 = [Not(term1);term2];;
let c4 = [Not(term2);term3];;
let c5 = [Not(term3);term1];;

let c = [c1;c2;c3;c4;c5];;
resolution c [];;
```
