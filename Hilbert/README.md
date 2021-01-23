# Hilbert-Style-Proof-System

The Hilbert-style proof system consists of the following Axiom Schema, where Γ is a set of propositions, and p,q,r are propositions.

    (Ass)   Γ |- p     if p in Γ

    (K)     Γ |-  p -> (q -> p)

    (S)     Γ |- (p -> (q->r)) -> ((p -> q) -> (p-> r))

    (R)     Γ |- (~p -> ~q) -> ((~p -> q) -> p)

and one inference rule 


    (MP)   Γ |- p -> q      Γ |- p       

           -----------------------     

               Γ |- q     

A proof of a judgment Γ |- p  in the Hilbert style is a tree with the root labelled with judgement  Γ |- p, and each leaf being labelled by an instance of one of the axiom schema, and each internal node being a valid instance of the rule MP. 

# Using the system

The code can be compiled and run on the Ocaml terminal. The input tree is of the format: 

    type tree = Root of prop * tree * tree * typeString * gamma 
              | E   (For the root case)
              
In the given example, we take a proposition *p⟶p* (let us call it *q*), where *p* would be *s⟶a*, with *s* and *a* also being propositional variables. A standard proof for *|- p ⟶ p* is considered. 

Now, if Γ consisted of [q], then the proof tree for this would be: 
```ocaml
let root0 = (q,E,E,"Ass",[q]);;
``` 

Otherwise if the gamma were empty, then a proof tree would be:

```ocaml
let root1 = 
  Root (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")),
	Root
		(Impl (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))),
			Impl (Impl (L "s", L "a"), Impl (L "s", L "a"))),
		Root
		  	(Impl
		    	(Impl (Impl (L "s", L "a"),
		      		Impl (Impl (L "q", Impl (L "s", L "a")), Impl (L "s", L "a"))),
				Impl (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))),
					Impl (Impl (L "s", L "a"), Impl (L "s", L "a")))),
			E, E, "S", []),
		Root
		  	(Impl (Impl (L "s", L "a"),
					Impl (Impl (L "q", Impl (L "s", L "a")), Impl (L "s", L "a"))),
			E, E, "K", []),
		"MP", []),
	Root (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))), E, E,
		"K", []),
	"MP", []);;
```

Now, we can first try to see if the above proof tree that has been taken by us is valid or not (should return *true*). 
```ocaml
valid_hprooftree root1;;
```

After that, we can pad the previous Hilbert tree Γ (that was [] initially), with the propositional set Δ = [*q*]. Now, that would give the proof tree for Γ U Δ |- q, which would basically be the root0 that we declared initially.
```ocaml 
let padded_root1 = pad root1 [q]
```

Similarly, we can perform pruning on the above formed Hilbert proof (that has the new Γ as [*q*]) and get the Hilbert proof for Δ |- q, where Δ is a finite subset of Γ.
```ocaml
let pruned = prune padded_root1
```

We also define a graft function, which basically has the following functionality:
```
* Inputs: 
	* root: The (valid) input Hilbert proof tree of judgment Δ |- p, where Δ = {q_1, ..., q_k}
	* l: A list of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k
* Outputs: A valid Hilbert-style proof of judgment Γ |- p
```

For the tree of root1, as there are no "Ass" (i.e assumption) leaves, graft function won't make any difference. But that would work for the root0 tree. So the proof-tree list can be defined as:
```ocaml
let  l = [
  Root (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")),
	Root
		(Impl (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))),
			Impl (Impl (L "s", L "a"), Impl (L "s", L "a"))),
		Root
		  	(Impl
		    	(Impl (Impl (L "s", L "a"),
		      		Impl (Impl (L "q", Impl (L "s", L "a")), Impl (L "s", L "a"))),
				Impl (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))),
					Impl (Impl (L "s", L "a"), Impl (L "s", L "a")))),
			E, E, "S", []),
		Root
		  	(Impl (Impl (L "s", L "a"),
					Impl (Impl (L "q", Impl (L "s", L "a")), Impl (L "s", L "a"))),
			E, E, "K", []),
		"MP", []),
	Root (Impl (Impl (L "s", L "a"), Impl (L "q", Impl (L "s", L "a"))), E, E,
		"K", []),
	"MP", [])
];;
```

As it can be seen, the above list is basically consisting of only one element which is the proof system for [] |- q (that was our root1). And we have the proof system for [q] |- q. And so, the graft function would give the tree for [] |- q, which is the same as root1. And this can be easily verified as well.
```ocaml
let graft_root0 = graft root0 l;;
valid_hprooftree graft_root0;;
```

The final function in this toolbox is of dedthm which basically works as follows:
```
* Inputs:
	* root: The (valid) input Hilbert proof tree of judgement Γ U {p}  |- q
	* p: The proposition 'p' used in the above definition of root
* Outputs: A valid Hilbert-style proof of judgment Γ |- p -> q
```

Thus, calling this function on root0 with the 'p' in the definition above (different from the *p* that we declared) is the variable *q* defined by us. And, so we would get the Hilbert proof tree for [] |- q -> q from the below operation.
```ocaml
let dedthm_root0 = dedthm root0 q
valid_hprooftree dedthm_root0
```

