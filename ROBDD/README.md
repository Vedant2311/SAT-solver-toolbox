# Reduced-Order-Binary-Decision-Diagrams

In this project, a complete [ROBDD](https://www.cs.utexas.edu/~isil/cs389L/bdd.pdf) proof system has been implemented. We break down this system into three parts, **Creation of the ROBDD**, **Using ROBDD to solve SAT**, and **Modifying the ROBDD**.

## Creation of the ROBDD
In the **robdd.ml** file, the first section deals with creating a toy propositional language in the same way as done in the implementation present in the **basic-toolbox** directory. 

For the creation of the ROBDD table, different global variables are declared and initialised suitably as instructed in the algorithm. These are also initialised in the **buildEx t** function that takes the input proposition and builds the ROBDD corresponding to it. It returns the "u" value for the root node of the ROBDD formed. The formed table will be present in the reference variable **tT**. 
```ocaml
(* Taking the input proposition as (x1 <=> x2) \/ x3 *)
let t = Or(Iff(L("x1"),L("x2")),L("x3"));;    
buildEx t;;
- : int = 5
!tT;;
- : (int * (int * int * int)) list =
[(5, (1, 3, 4)); (4, (2, 2, 1)); (3, (2, 1, 2)); (2, (3, 0, 1));
 (0, (4, -1, -1)); (1, (4, -1, -1))]

(* A simple test to see if the ROBDD construction is working or not *)
let t = (nnf t);;
buildEx t;;
- : int = 5
!tT;;
- : (int * (int * int * int)) list =
[(5, (1, 3, 4)); (4, (2, 2, 1)); (3, (2, 1, 2)); (2, (3, 0, 1));
 (0, (4, -1, -1)); (1, (4, -1, -1))]
```

As you can see above, both the formed Tables are the same which should be the case for logically equivalent propositions.

We can also take the root nodes for the to ROBDDs and a string opp (Eg. "Or", "And" etc) and forms a new ROBDD as per the "Apply" function for the ROBDDs. This would be done by the function **app u1 u2 opp**. The function outputs the integer "u" value for the root of the newly formed ROBDD. The table for the newly formed ROBDD will be in the reference variable **tT3**. Some corrections might be needed on the output of the Apply function and for that, I make use of a **corectApp** function, that corrects the ROBDD formed by apply function.

```ocaml
(* The taken propositions are: t1 = (x1 <=> x2) \/ x3, t2 = (x1 /\ (-x2)) => x3, t = t1 \/ t2 *)

(* First of all, I obtain the ROBDD for the expession t *)
let t = Or(Impl(And(L("x1"),Not(L("x2"))),L("x3")),Or (And (Or (Not (L "x1"), L "x2"), Or (Not (L "x2"), L "x1")), L "x3"));;
buildEx t;;
- : int = 4
!tT;;
- : (int * (int * int * int)) list =
[(4, (1, 3, 1)); (3, (2, 1, 2)); (2, (3, 0, 1)); (1, (4, -1, -1));
 (0, (4, -1, -1))]

(* Now, I combine the ROBDDs for the two propositions t1 and t2, and then Obtain it's ROBDD. This is the exact same as obtained above *)
app 4 5 "Or";;
- : int = 4
!tT3;;
- : (int * (int * int * int)) list =
[(4, (1, 1, 3)); (3, (2, 2, 1)); (2, (3, 0, 1)); (1, (4, -1, -1));
 (0, (4, -1, -1))]
correctApp (!tT3);;
- : (int * (int * int * int)) list =
[(4, (1, 3, 1)); (3, (2, 1, 2)); (2, (3, 0, 1)); (1, (4, -1, -1));
 (0, (4, -1, -1))]
```

## Using ROBDD to solve SAT
Coming to the main use of this system, three different functions were created with different purposes of those. Their usage is illustrated as follows:
```ocaml
(* Taking the Input proposition as: (x1 <=> x2) \/ x3 and building ROBDD *)
let t = Or(Iff(L("x1"),L("x2")),L("x3"));;    
buildEx t;;
- : int = 5
!tT;;
- : (int * (int * int * int)) list =
[(5, (1, 3, 4)); (4, (2, 2, 1)); (3, (2, 1, 2)); (2, (3, 0, 1));
 (0, (4, -1, -1)); (1, (4, -1, -1))]

(* 
1. Along with passing the ROBDD table, we also need to pass the integer "u" for  the tree root for the functions below
2. This would be the value returned by the build function. For example, here "u" will be 5.
*)


(* Getting the count of all the satisfiable arguement for the ROBDD *)
satCount 5 !tT;;
- : int = 6

(* Getting any one satisfiable argument to the above ROBDD *)
(* (1,0) means that the value of the variable with index 1 will be 'false'*)
(* This variable with the index one will be x1 as it is the first element*)
anySat 5 !tT;;
- : (int * int) list = [(1, 0); (2, 0)]

(* Getting all the satisfiable arguments to the above ROBDD*)
allSat 5 !tT;;
- : (int * int) list list =
[[(1, 0); (2, 0)]; [(1, 0); (2, 1); (3, 1)]; [(1, 1); (2, 0); (3, 1)];
 [(1, 1); (2, 1)]]
 
(* 
Note that even though the above list has only four elements, it is actually corresponding to six satisfiable arguements...
As for the first and fourth element in the list, x3 can take any values of 0 or 1.
*) 
```

## Modifying the ROBDD 
It is possible that we make the ROBDDs efficient as well for more efficient SAT estimation. For that, we define two more functions for our system. 

The function **restrict (u,j,b)** takes an Int "u" (For the root node of the ROBDD), Int "j" for the variable Id which is getting flipped, and the Int "b" (0 for 'false' and 1 for 'true') corrresponding to the value of the variable j which is set. The output is the Int corresponding to the Root Node of the ROBDD for the new proposition formed by setting the value of the Variable j to b

The function **Simplify d u** takes an Int "u" (For the root node of the ROBDD under consideration) and Int "d" (For the root Node of the Domain ROBDD) and gives an Int corresponding to the Root Node of the ROBDD for the new proposition formed as per the simplify function. (This proposition will be a simpler one as compared to the one under Consideration and so will be it's ROBDD. This is used to speed up the verification under the given domain)

Note that if you currently view the **robdd.ml** code, then you can see that the code section corresponding to **Modifying the ROBDD** is commented. And it is because of the current limitation of the variable names and logic regarding references involved here that would challenge the working of the previous sections. Sample usage examples for these functions are provided in this code section as well. Kindly go through them in order to get a better understanding of these.
