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

## Using the coode

The code can be compiled and run on the Ocaml terminal

The input tree is of the format: 

    type tree = Root of prop * tree * tree * tree * gamma * typeString 
              | E   (For the root case)
              
The main functions of the package are as follows: (A sample test case is given at the end. Please go through it once)

1. valid_ndprooftree root

    * Inputs: The input ND proof tree
    * Outputs: Whether it is a valid proof tree as per the axioms
    
2. pad root delta

    * Inputs: 
        * root: The (valid) input ND proof tree of judgment  Γ |- p
        * delta: The propositional set to be padded Δ
    * Outputs: A valid ND proof of judgment Γ U Δ |- p
   
3. prune root

    * Inputs: The (valid) input ND proof tree of judgement Γ |- p
    * Outputs: A valid ND proof of judgement Δ |- p, where Δ is a finite subset of Γ

4. graft root l

    * Inputs: 
        * root: The (valid) input ND proof tree of judgment Δ |- p, where Δ = {q_1, ..., q_k}
        * l: A list of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k
    * Outputs: A valid ND proof of judgment Γ |- p
 
5. simplify root gamma    (To be called for the outputs of prune and graft because of their issues with the "->-I" case)

    * Inputs: 
      * root: The input (invalid) ND proof tree
      * gamma: The propositional set with respect to which we need to correct the table transmission errors for the "->-I" instructions
    * Outputs: The corrected valid ND proof tree 
  
6. has_rpair root

    * Inputs: The input (valid) ND proof tree
    * Outputs: Whether it has a r-pair or not
    
7. find_rpair root

    * Inputs: The input (valid) ND proof tree
    * Outputs: The Node which has the rpair
    
8. simplify1 root

    * Inputs: The input ND proof tree with an r-pair at its root
    * Outputs: A valid but "simpler" ND proof tree of the same consequent judgment
        
9. normalise root

    * Inputs: The input ND proof tree
    * Outputs: A completely "simplified" ND proof tree, with no r-pairs
