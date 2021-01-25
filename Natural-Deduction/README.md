# Natural-Deduction-Proof-System

The Natural Deduction Proof System consists of the following Axiom Schema and Inference Rules for Introduction and Elimination of Connectives. We write the proof system in terms of "judgments" of the form  Γ |- p, where Γ is a set of "assumption" propositions and p is a "conclusion" proposition. 
  
    (Hyp)   Γ |- p      if p is in  Γ 

    (T-I)   Γ |- T
    
    (->-I)  Γ, p  |-  q                          (->-E)   Γ |- p -> q     Γ |- p

          --------------                                  -------------------------

            Γ |- p -> q                                            Γ |- q                 
            


    (~-Int)   Γ |-  F                            (~-Class)     Γ, ~p |-  F 

            -----------                                        -------------

              Γ |-  p                                             Γ |-  p


                     
    (/\-I)   Γ |- p      Γ |- q                 (/\-EL)    Γ |- p /\ q           (/\-ER)    Γ |- p /\ q

          ----------------------                          --------------                    ---------------

            Γ |- p /\ q                                      Γ |- p                              Γ |- q



    (\/-IL)   Γ |- p            (\/-IR)      Γ |- q               (V-E)    Γ |- p \/ q      Γ, p  |- r      Γ, q  |- r 

            -----------                    -------------                   ------------------------------------------

            Γ |- p \/ q                     Γ |- p \/ q                                       Γ |- r


Each rule can be considered a proof-tree building constructor that takes the list of judgments in the "numerator" (antecedents)  and the judgment in the "denominator" (consequent).

A proof of a judgment Γ |- p  in the ND style is a tree with the root labelled with judgement  Γ |- p, and each leaf being labelled by an instance of one of the axiom schema, and each internal node being a valid instance of one of the inference rules for introduction or elimination of a main connective. 

We say that an "r-pair" occurs in a ND proof tree if an instance of a connective's introduction rule is immediately "followed by" (closer to the root) an instance of the same connectives's elimination rule, with the main proposition of the introduction rule coinciding with that of the elimination rule.  An "r-pair" can be eliminated by replacing the proof-trees with "simpler" proof trees (note that simpler does not mean smaller in size or shorter in height)

# Using the System

The code can be compiled and run on the Ocaml terminal. The input tree is of the format: 

    type tree = Root of prop * tree * tree * tree * gamma * typeString 
              | E   (For the root case)
              
Here, each node will be having at max three children and each Axiom is encoded as a string in the *typeString*. In the given example, we take a proposition *(p ⟶ (q ⟶ r)) ⟶ ((p ⟶ q) ⟶ (p ⟶ r))*, let's call it *z*. This is actually a standard type for the hilbert style proof system. Here *p* would be *s⟶a*, *q* would be *s /\ a* and *r* would be *s \/ a*; with *s* and *a* also being propositional variables. The Initial Γ is taken as an empty list.
```ocaml
let p = Impl(L("s"),L("a"));;
let q = And(L("s"),L("a"));;
let r = Or(L("s"),L("a"));;
let gamma = [];;
```
   
The ND proof tree for the Initial proposition is considered and it would be formed as:
```ocaml
let root = Root(Impl(Impl(p,Impl(q,r)),(Impl(Impl(p,q),Impl(p,r)))),Root((Impl(Impl(p,q),Impl(p,r))),E,E,(Root(Impl(p,r),E,(Root(r,E,(Root(Impl(q,r),E,(Root(p,E,E,E,[Impl(p,Impl(q,r));Impl(p,q);p],"Hyp")),(Root(Impl(p,Impl(q,r)),E,E,E,[Impl(p,Impl(q,r));Impl(p,q);p],"Hyp")),[Impl(p,Impl(q,r));Impl(p,q);p],"->-E")),(Root(q,E,(Root(p,E,E,E,[Impl(p,Impl(q,r));Impl(p,q);p],"Hyp")),(Root(Impl(p,q),E,E,E,[Impl(p,Impl(q,r));Impl(p,q);p],"Hyp")),[Impl(p,Impl(q,r));Impl(p,q);p],"->-E")),[Impl(p,Impl(q,r));Impl(p,q);p],"->-E")),E,[Impl(p,Impl(q,r));Impl(p,q)],"->-I")),[Impl(p,Impl(q,r))],"->-I"),E,E,[],"->-I");;
```
```ocaml
val root : nat =
  Root
   (Impl
     (Impl (Impl (L "s", L "a"),
       Impl (And (L "s", L "a"), Or (L "s", L "a"))),
     Impl (Impl (Impl (L "s", L "a"), And (L "s", L "a")),
      Impl (Impl (L "s", L "a"), Or (L "s", L "a")))),
   Root
    (Impl (Impl (Impl (L "s", L "a"), And (L "s", L "a")),
      Impl (Impl (L "s", L "a"), Or (L "s", L "a"))),
    E, E,
    Root (Impl (Impl (L "s", L "a"), Or (L "s", L "a")), E,
     Root (Or (L "s", L "a"), E,
      Root (Impl (And (L "s", L "a"), Or (L "s", L "a")), E,
       Root (Impl (L "s", L "a"), E, E, E,
        [Impl (Impl (L "s", L "a"),
          Impl (And (L "s", L "a"), Or (L "s", L "a")));
         Impl (Impl (L "s", L "a"), And (L "s", L "a")); Impl (L "s", L "a")],
        "Hyp"),
       Root
        (Impl (Impl (L "s", L "a"),
          Impl (And (L "s", L "a"), Or (L "s", L "a"))),
        E, E, E,
        [Impl (Impl (L "s", L "a"),
          Impl (And (L "s", L "a"), Or (L "s", L "a")));
         Impl (Impl (L "s", L "a"), And (L "s", L "a")); Impl (L "s", L "a")],
        "Hyp"),
       [Impl (Impl (L "s", L "a"),
         Impl (And (L "s", L "a"), Or (L "s", L "a")));
        Impl (Impl (L "s", L "a"), And (L "s", L "a")); Impl (L "s", L "a")],
       "->-E"),
      Root (And (L "s", L "a"), E,
       Root (Impl (L "s", L "a"), E, E, E,
        [Impl (Impl (L "s", L "a"),
          Impl (And (L "s", L "a"), Or (L "s", L "a")));
         Impl (Impl (L "s", L "a"), And (L "s", L "a")); Impl (L "s", L "a")],
        "Hyp"),
       Root (Impl (Impl (L "s", L "a"), And (L "s", L "a")), E, ...), ...),
      ...),
     ...),
    ...),
   ...)

```

Now, we can first try to see if the above proof tree that has been taken by us is valid or not (should return *true*). 
```ocaml
valid_ndprooftree root;;
```

After that, we can pad the previous Hilbert tree Γ (that was [] initially), with the propositional set Δ = [Impl(p,r)]. Now, that would give the proof tree for Γ U Δ |- z, which would basically be the root0 that we declared initially.
```ocaml 
let padded_root = pad root [Impl(p,r)];;
val padded_root : nat =
  Root
   (Impl
     (Impl (Impl (L "s", L "a"), Impl (And (L "s", L "a"), Or (L "s", L "a"))),
     Impl (Impl (Impl (L "s", L "a"), And (L "s", L "a")),
      Impl (Impl (L "s", L "a"), Or (L "s", L "a")))),
   Root
    (Impl (Impl (Impl (L "s", L "a"), And (L "s", L "a")),
      Impl (Impl (L "s", L "a"), Or (L "s", L "a"))),
    E, E,
    Root (Impl (Impl (L "s", L "a"), Or (L "s", L "a")), E, E, E,
     [Impl (Impl (L "s", L "a"), Impl (And (L "s", L "a"), Or (L "s", L "a")));
      Impl (Impl (L "s", L "a"), And (L "s", L "a"));
      Impl (Impl (L "s", L "a"), Or (L "s", L "a"))],
     "Hyp"),
    [Impl (Impl (L "s", L "a"), Impl (And (L "s", L "a"), Or (L "s", L "a")));
     Impl (Impl (L "s", L "a"), Or (L "s", L "a"))],
    "->-I"),
   E, E, [Impl (Impl (L "s", L "a"), Or (L "s", L "a"))], "->-I")

```

Similarly, we can also pad another proposition of *And(p,r)*, resulting in a new proof tree. Now, we can also perform pruning on the above formed Hilbert proof (that has the new padded Γ) and get the Hilbert proof for Δ |- z, where Δ is a finite subset of Γ. The result would be a valid proof tree as expected. 
```ocaml
let padded_root1 = pad padded_root [And(p,r)]
let pruned = prune padded_root1;;
```

We also define a graft function, which basically has the following functionality:
```
* Inputs: 
	* root: The (valid) input ND proof tree of judgment Δ |- p, where Δ = {q_1, ..., q_k}
	* l: A list of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k
* Outputs: A valid ND proof of judgment Γ |- p
```
 
This function can be tested in the same way as done in the case of the **Hilbert Style Proof system**. Kindly refer to it's README to get a better idea. Also note that because of the issues with the "->-I" case for *prune* and *graft* functions, the below simplify function needs to be called on the tree outputed by them in order to correct that.
```
simplify root gamma
    * Inputs: 
      * root: The input (invalid) ND proof tree
      * gamma: The propositional set with respect to which we need to correct the table transmission errors for the "->-I" instructions
    * Outputs: The corrected valid ND proof tree 
```

Different functions are also defined that would be dealing with the removal of r-pairs from the ND tree. The function usage is described in brief as below. In the *nd.ml* file, sample usage examples are given at the end of the file for the same. Kindly refer to that. 
```  
1. has_rpair root
    * Inputs: The input (valid) ND proof tree
    * Outputs: Whether it has a r-pair or not
    
2. find_rpair root
    * Inputs: The input (valid) ND proof tree
    * Outputs: The Node which has the rpair
    
3. simplify1 root
    * Inputs: The input ND proof tree with an r-pair at its root
    * Outputs: A valid but "simpler" ND proof tree of the same consequent judgment
        
4. normalise root
    * Inputs: The input ND proof tree
    * Outputs: A completely "simplified" ND proof tree, with no r-pairs

