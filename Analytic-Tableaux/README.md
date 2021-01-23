# Analytic-Tableaux

Analytic Tableaux is Trees built according to some rules, in simple terms. A Node in a tableau is labelled with a proposition and the truth value we wish to give it, i.e., as prop * bool. 

During the development of a tableau, nodes are introduced and examined.  When a node is examined, it is marked as examined and its analysis may result in:

1. Closing the paths on which it occurs because a contradiction has been discovered
2. Adding nodes and/or branches to each path on which this node lies, depending on the kind of node. 

A tableau is developed by selecting some unexamined node on a path which is not already closed due to a contradiction, and then analysing it.  Let p be the proposition and b be the boolean value in the label of the node being analysed:

  1. if p is T and b is true, or if p is F and b is false, then the node is marked examined and no extensions are made to the paths on which this node occurs
  2. if p is T and b is false, or if p is F and b is true, then the node is marked examined, and the paths on which this node occurs are considered closed  since they contain a contradiction.
  3. if another node with p and the negation of b is already on the path leading to this node, the current node is marked examined and the path considered closed as it contains a contradiction. [You can create a back-pointer to that earlier contradicting node]
  4. if p is L(s), then the propositional letter s is assigned the truth value b
  5. if p is Not(p1) and b is true [respectively false], then the node is marked examined and each open (non-closed) path on which it lies is extended with a node marked (p1, false) [respectively  (p1, true)]
  6. if the node is an α-type node, then it is marked examined, and each open (non-closed) path on which it lies is extended with two nodes α_1 and α_2, one below the other. 
  7. if the node is an β-type node, then it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the node β_1 is placed, and on the second branch β_2 is placed.
  8. if p is of the form Iff(p1, p2) and b is false, then  it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the nodes (p1, false) and (p2, true) are placed one below the other, and on the second branch the nodes (p1, true) and (p2, false) are placed one below the other.  If p is of the form Iff(p1, p2) and b is true, then  it is marked examined, and each open (non-closed) path on which it lies is extended with two branches: on the first branch the nodes (p1, true) and (p2, true) are placed one below the other, and on the second branch the nodes (p1, false) and (p2, false) are placed one below the other.  

A tableau is called "fully developed" if it has no unexamined nodes on any open path. The tableaux is represented by the data structure of the type "tree" defined as: node * bool * bool * tree * tree. The first two bools are for the questions: "Whether the node has been examined?" And "Whether any contradiction has been found?" respectively. 

# Using the System for any desired proposition
Let there be two boolean variables *s* and *a* and we want to check Satisfiability for the proposition *(s⟶a)⟶(s⟶a)*. Then first of all, we would proceed to create the propositional variables as:
```ocaml
let p = Impl(L("s"),L("a"));;
let q = Impl(p,p);;
```

We would then create a node for the proposition *q* with the expected boolean value to be *true*. We also create an empty initial Variable assignment *gamma*. It has to be passed Empty to the further functions.
```ocaml
let n = (Node(q,true));;
let gamma = [];;
```

Now, we would create the full Tableaux for this Node. We can also check whether the formed tableaux is a valid one or not. (Should return *true* ideally)
```ocaml
let root1 = makeAna n gamma;;
valid_tableau root1 gamma;;
```

The variable *root1* (i.e the tableaux formed for the system) should be as follows:
```ocaml
Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), true), true, false,
  Root (Node (Impl (L "s", L "a"), false), true, false,
    Root (Node (L "s", true), true, false,
      Root (Node (L "a", false), true, false, E, E), E),
    E),
  Root (Node (Impl (L "s", L "a"), true), true, false,
    Root (Node (L "s", false), true, false, E, E),
      Root (Node (L "a", true), true, false, E, E)))
```

We can also check if the (valid) tableaux is complete or not by attempting to find any node in it which hasn't been examined yet.
```ocaml
select_node root1;;
```

We can find all the variable assignments that satisfy the *((s⟶a)⟶(s⟶a),true)* pair as:
```ocaml
find_assignments root1;;
```

We can also check whether the given proposition is a tautology or a contradiction as:
```ocaml
check_tautology q;;
check_contradiction q;;
```

# Using the system by providing a custom made tableaux.
We can also provide a custom-made tableaux (either completely built or incomplete) as per the specifications of the tree datastructure that the code possesses and then have the same functionality.
```ocaml
let gamma = [];;
let root2 =  Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), true), true, false,
              Root (Node (Impl (L "s", L "a"), false), false, false,E,E),
              Root (Node (Impl (L "s", L "a"), true), false, false,E,E));;
```

The previously stated functions would still work on this tree. As it can be seen, the above tree is incomplete. And we can complete this tree by selecting an unexplored node in it and then developing the entire path from that node. 
```ocaml
let node_left = select_node root2;;
step_develop node_left root2;;
```

Note that the output of the *step_develop* function above would be the fully completed subtree corresponding to the *node_left* as the root. We can also check for contradictory path within the given input tableaux (full or partial). The following command would get the contradictory node and mark it closed for further exploration.
```ocaml
contrad_path root2 gamma;;
```

