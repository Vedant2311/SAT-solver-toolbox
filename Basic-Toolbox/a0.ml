(*Required Type definition for the Propositional variables*)
type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop
exception Myexp of string

let rec member x l = match l with 

	[] -> false
  | y :: ys -> (if y=x then true else (member x ys))


let rec union l1 l2 = match l1 with 

	[] -> l2
  | x :: xs -> (

  	if (member x l2) then (union xs l2) else ([x] @ (union xs l2))

  )

let rec appendToAll s l = match l with 

	[] -> []
  | x:: xs -> (s ^ x) :: (appendToAll s xs)	

(* Mapping some custom variables with boolean values*)
let rho s = match s with 

	"A" -> false
  | "E" -> true
  | "C" -> true
  | "Z" -> false
  | "aa" -> false
  | "P" -> true
  (*| _ -> true*)


let rec inDomain s l = match l with 

	[] -> false
  | x  :: xs -> if (x=s) then true else (inDomain s xs)

let dom = ["A";"E";"C";"Z";"aa";"P"]

(* Finding Height of a proposition*)
let rec ht p = match p with

	T -> 0
  | F -> 0
  | L(s) -> 0
  | Not(q) -> 1 + (ht q)
  | And(q1,q2) -> 1 + (max (ht q1) (ht q2))
  | Or(q1, q2) -> 1 + (max (ht q1) (ht q2))
  | Impl(q1, q2) -> 1 + (max (ht q1) (ht q2))
  | Iff(q1, q2) -> 1 + (max (ht q1) (ht q2))

(*Finding size of a proposition*)
let rec size p = match p with 

	T -> 1
  | F -> 1
  | L(s) -> 1
  | Not(q) -> 1 + (size q)
  | And(q1,q2) -> 1 + (size q1) + (size q2)
  | Or(q1, q2) -> 1 + (size q1) + (size q2)
  | Impl(q1, q2) -> 1 + (size q1) + (size q2)
  | Iff(q1, q2) -> 1 + (size q1) + (size q2)

(*Getting the propositional letters*)
let rec letters p = match p with

	T -> []
  | F -> []
  | L(s) -> [s]
  | Not(q) -> (letters q)
  | And(q1,q2) -> (union (letters q1) (letters q2))
  | Or(q1, q2) -> (union (letters q1) (letters q2))
  | Impl(q1, q2) -> (union (letters q1) (letters q2))
  | Iff(q1, q2) -> (union (letters q1) (letters q2))

(* Getting the truth value of the proposition along with using the variable mapping*)
let rec truth p rho = match p with 

	T -> true
  | F -> false
  | L(s) -> if (inDomain s dom) then (rho s) else raise (Myexp "Not in domain")
  | Not(q) -> not (truth q rho)
  | And(q1,q2) -> if ((q1=F)||(q2=F)||(not(truth q1 rho))||(not(truth q2 rho))) then false else (truth q1 rho) && (truth q2 rho)
  | Or(q1, q2) -> if ((q1=T)||(q2=T)||((truth q1 rho))||((truth q2 rho))) then true else (truth q1 rho) || (truth q2 rho)
  | Impl(q1, q2) -> if (truth q1 rho) then (truth q2 rho) else true
  | Iff(q1, q2) -> if ((truth q1 rho)=(truth q2 rho)) then true else false

(* Check whether p1 is a sub-proposition of p2*)
let rec subprop p1 p2 = match p2 with 

	T -> (if p1=T then true else false)
  | F -> (if p1 = T then true else false)
  | L(s) -> (if p1=L(s) then true else false)
  | Not(q) -> (if ((p1=q)||(p1=p2)) then true else (subprop p1 q))
  | And(q1,q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Or(q1, q2) ->(if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Impl(q1, q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Iff(q1, q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))

(* Yields a string encoded path set that goes from the root of p2 and gets the occurence of p1 within itself*)
let rec subprop_at p1 p2 = if (subprop p1 p2) then (

	match p2 with

		T -> [""]
	  | F -> [""]
	  | L(s) -> [""]
	  | Not(q) -> if (p1=p2) then [""] else (appendToAll "0" (subprop_at p1 q))
	  | And(q1,q2) -> if (p1 = p2) then [""] else (

	  	if (subprop p1 q1) then (

	  		if(subprop p1 q2) then (

	  			(union ((appendToAll "0" (subprop_at p1 q1))) ((appendToAll "1" (subprop_at p1 q2))))

	  		) else (appendToAll "0" (subprop_at p1 q1))

	  	) else (appendToAll "1" (subprop_at p1 q2))

	  )

	  | Or(q1, q2) -> if (p1 = p2) then [""] else (

	  	if (subprop p1 q1) then (

	  		if(subprop p1 q2) then (

	  			(union ((appendToAll "0" (subprop_at p1 q1))) ((appendToAll "1" (subprop_at p1 q2))))

	  		) else (appendToAll "0" (subprop_at p1 q1))

	  	) else (appendToAll "1" (subprop_at p1 q2))

	  )

	  | Impl(q1, q2) -> if (p1 = p2) then [""] else (

	  	if (subprop p1 q1) then (

	  		if(subprop p1 q2) then (

	  			(union ((appendToAll "0" (subprop_at p1 q1))) ((appendToAll "1" (subprop_at p1 q2))))

	  		) else (appendToAll "0" (subprop_at p1 q1))

	  	) else (appendToAll "1" (subprop_at p1 q2))

	  )

	  | Iff(q1, q2) -> if (p1 = p2) then [""] else (

	  	if (subprop p1 q1) then (

	  		if(subprop p1 q2) then (

	  			(union ((appendToAll "0" (subprop_at p1 q1))) ((appendToAll "1" (subprop_at p1 q2))))

	  		) else (appendToAll "0" (subprop_at p1 q1))

	  	) else (appendToAll "1" (subprop_at p1 q2))

	  )


) else raise (Myexp "NotSubProp")

(*Negation Normal form*)
let rec nnf p = match p with 

	T -> T
  | F -> F
  | L(s) -> L(s)
  | Not(q) -> (

  	match q with 

    	T -> F
	  | F -> T
	  | L(s) -> Not(q)
	  | Not(q') -> (nnf q') 
	  | And(q1,q2) -> Or((nnf (Not(q1))),(nnf (Not(q2))))
	  | Or(q1, q2) -> And((nnf (Not(q1))),(nnf (Not(q2))))
	  | Impl(q1, q2) -> And((nnf q1),(nnf (Not(q2))))
	  | Iff(q1, q2) -> nnf (Not(And((nnf (Impl(q1,q2))),(nnf (Impl (q2,q1))))))

  )

  | And(q1,q2) -> And((nnf q1),(nnf q2))
  | Or(q1, q2) -> Or((nnf q1),(nnf q2))
  | Impl(q1, q2) -> Or((nnf (Not q1)),(nnf (q2)))
  | Iff(q1, q2) -> And((nnf (Impl(q1,q2))),(nnf (Impl (q2,q1))))

(* Conjunctive Normal form*)
let rec cnf p = let p1 = nnf p in (

	match p1 with

	 Or(q1,And(q2,q3)) -> (And((cnf (Or((cnf q1),(cnf q2)))),(cnf (Or((cnf q1),(cnf q3))))))
   | Or(And(q2,q3),q1) -> (And((cnf (Or((cnf q2),(cnf q1)))),(cnf (Or((cnf q3),(cnf q1))))))
   | And(q1,q2) -> And(cnf q1, cnf q2)
   | _  -> p1
)

(* Disjunctive Normal form*)
let rec dnf p = let p1 = nnf p in (

	match p1 with

	 And(q1,Or(q2,q3)) -> (Or((dnf (And((dnf q1),(dnf q2)))),(dnf (And((dnf q1),(dnf q3))))))
   | And(Or(q2,q3),q1) -> (Or((dnf (And((dnf q2),(dnf q1)))),(dnf (And((dnf q3),(dnf q1))))))
   | Or(q1,q2) -> Or(dnf q1, dnf q2)
   | _ -> p1



)

(*
-----------------------------TEST CASES USED--------------------------------------------

(Please go through the rho function in order to get the "Don't care" case)

=> For height, truth, size, letters:

1. let p1 = Or(And((Or(T,L("A"))),(Or(L("B"),T))),L("C")) -> A tautology
2. let p2 = Impl(Not(And(L("C"),T)),Not(Or(L("Pe"),T)))  -> A contingency
3. let p3 = Impl((And(L("Ca"),F)),Not(Or(L("Pe"),T)))  -> A tautology
4. let p4 = Impl(T,Not(Or(L("Q"),T))) -> A contradiction
5. let p5 = Iff(And(L("A"),L("E")),Or(T,F)) -> A contingency
6. let p6 = Iff(Not(And(L("A"),L("C"))),Not(Or(L("E"),L("C")))) -> A contingency


=> For sub-proposition: (I have considered Not to be having only a left child)

1. let p1 = And(L("A"),L("B"));;
   let p2 = Or(Or(And(L("A"),L("B")),And(L("A"),L("B"))),And(L("A"),L("B")));;

2. let p1 = And(L("A"),L("B"));;
   let p2 = Not(Or(Or(And(L("A"),L("B")),And(L("A"),L("B"))),And(L("A"),L("B"))));;

3. let p1 = And(L("B"),L("A"));;
   let p2 = Or(Or(And(L("A"),L("B")),And(L("A"),L("B"))),And(L("A"),L("B")));;


=> For NNF:

1. let p1 = Impl(T,Not(Or(T,L("Q"))));;
2. let p2 = Iff(Not(And(L("A"),L("C"))),Not(Or(L("E"),L("C"))));;
3. let p3 = Not(Not(Or(L("A"),Not(Or(T,F)))));;
4. let p4 = Not(Not(Or(L("A"),Not(Or(Not(T),Not(F))))));;


=> For CNF:

1. let p1 = Impl(T,Not(Or(T,L("Q"))));;
2. let p2 = Iff(Not(And(L("A"),L("C"))),Not(Or(L("E"),L("C"))));;
3. let p3 = Not(Not(Or(L("A"),Not(Or(T,F)))));;
4. let p4 = Not(Not(Or(L("A"),Not(Or(Not(T),Not(F))))));;


=> For DNF:

1. let p1 = Impl(T,Not(Or(T,L("Q"))));;
2. let p2 = Iff(Not(And(L("A"),L("C"))),Not(Or(L("E"),L("C"))));;
3. let p3 = Not(Not(Or(L("A"),Not(Or(T,F)))));;
4. let p4 = Not(Not(Or(L("A"),Not(Or(Not(T),Not(F))))));;

*)