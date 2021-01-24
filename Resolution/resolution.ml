(* Important Types definitions *)
type symbol = string
type variable = string
type term = V of variable | Node of symbol  * (term list)
type prop =  Term of term | Not of prop
exception Myexp of string

(* Basic Helper functions*)
let rec isPr s l = match l with 
 [] -> false
| (a,b) :: xs -> if (s=a) then true else (isPr s xs)

let rec findSig s l =  match l with 
 [] -> 0
| (a,b) :: xs -> if (s=a) then b else (findSig s xs)

let rec max_list l max = match l with
 [] -> max
| x :: xs -> if (x>max) then (max_list xs x) else (max_list xs max)

(* Checks whether the given signature is valid or not*)
let rec check_sig l = 
	(
	match l with 

		 [] -> true
		| (s,a) :: xs -> if (a<0) then false else (if (isPr s xs) then false else (check_sig xs))
	)

(* 
***************************Examples**********************************
let sign = [("a",0);("c",0);("c",3);("d",2)];;
check_sig sign;;	(returns false as repetitions)

let sign = [("a",0);("c",0);("e",3);("d",2)];;
check_sig sign;;	(returns true)
*)

(* Given a valid signature 's', checks whether the preterm 't' is well-formed according to 's'*)
let rec wfterm t s = 

	let rec wfterm_list l s = (


		match  l with
		 [] -> true
		| x :: xs -> if (wfterm x s) then (wfterm_list xs s) else false

	)

	in (match t with 

		  V(x) -> true
		| Node(sym,l) -> if (isPr sym s) then (

			if ((findSig sym s) = (List.length l)) then (wfterm_list l s)
			  else false

			) else false
)

(*
**************************Examples***********************************
let sign = [("a",0);("c",0);("e",3);("d",2)];;	(Note that this signature is well-formed as checked previously)

let term = Node("e",[Node("a",[V("x")]);Node("f",[]);Node("d",[V("x");V("y")])]);;
wfterm term sign;;	(should return false as term is not formed according to sign)

let term = Node("e",[Node("a",[]);Node("c",[]);Node("d",[V("x");V("y")])]);;
wfterm term sign;;	(should return true)

*)

(* Height of the well-formed term*)
let rec ht t = 

	let rec ht_list l = (

		match l with 

		[] -> []
	 | x :: xs -> [(ht x)] @ (ht_list xs)


	) in 

	(
		match t with 

	 	V(s) -> 0
	  | Node(s,l) -> (

	  	match l with 
	  	 [] -> 0
	  	| _ -> 	  1 + (max_list (ht_list l) 0)


	  )

	)

(* Set of variables occurring in the well-formed term*)
let rec vars t = 

	let rec vars_list l = (

		match l with 

		[] -> []
	  | x :: xs -> (vars x) @ (vars_list xs)

	)

	in
	(
		match t with 

  V(x) -> [x]
 | Node(s,l) -> (vars_list l)
	)

let rec add_list l = match l with
 [] -> 0
| x :: xs -> x + (add_list xs)

(* Size of the well-formed term*)
let rec size t = 

	let rec size_list l = (

		match l with 

		[] -> []
	  | x :: xs -> (size x) :: (size_list xs)
	)
	in

	(
		match t with 

		V(x) -> 1
	  | Node(s,l) -> (

	  	match l with 
	  	[] -> 1
	   | _ -> 1 + (add_list (size_list l))

	  )
	)

(*
*****************************Examples*************************************
let term = Node("e",[Node("a",[]);Node("c",[]);Node("d",[V("x");V("y")])]);;

ht term;;	(should return 2)
size term;;	(should return 6)
vars term;;	(should return ["x";"y"])
*)

let rec apply_homo rho term = 

	let rec apply_homo_list rho l = (match l with 

		[] -> []
	  | x :: xs -> (apply_homo rho x) :: (apply_homo_list rho xs)
	)
	
	in

	(
		match term with 

	 	V(s) -> (rho s)
	   | Node(p,l) -> (

		   	match l with 
		   	[] -> Node(p,[])
		  | _ -> Node(p,(apply_homo_list rho l))

	   )

	)

(* Gives out substitution by applying Homomorphism*)
let subst t s = (apply_homo s t)

(*
*************************Examples****************************
let term = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let s1 x = match x with 
   	 "x" -> Node("d",[Node("a",[]);V("x")])
   	|"y" -> Node("c",[])
	| p -> V(p)

subst term s1;;
(The expected output should be->
	Node ("e",
	 [Node ("d", [Node ("a", []); V "x"]); Node ("c", []);
	  Node ("d", [Node ("d", [Node ("a", []); V "z"]); Node ("c", [])])])
)
*)

(* Gives the composition of the substitutions*)
let compose s1 s2 x = let t = s1 x 	in subst t s2

(*
*************************Examples****************************
let term = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
let s1 x = match x with 
   	 "x" -> Node("d",[Node("a",[]);V("x")])
   	|"y" -> Node("c",[])
	| p -> V(p)

let s2 x =  match x with 
   	 "y" -> Node("d",[Node("a",[]);V("z")])
   	|"z" -> Node("c",[])
	| p -> V(p)

let s3 = compose s1 s2;;
(The expected output should be ->
	val s3 : variable -> term = <fun>
	# s3 "x";;
	- : term = Node ("d", [Node ("a", []); V "x"])
	# s3 "z";;
	- : term = Node ("c", [])
	# s3 "y";;
	- : term = Node ("c", [])
)
*)

(* Helper functions needed for getting the most general unifier*)
let rec occurs x l = match l with 
					[] -> false
				 | y :: ys -> if (x=y) then true else (occurs x ys)

let id x = V(x)

let rec notVar x p l sigma = let temp = (sigma p) in (

	match temp with 

	 V(s) -> (if (s=x) then x else (notVar x s l sigma)) 
	| _ -> p

)

let rec iden (t1,t2) sigma l = 

	let rec iden_list (l1,l2) sigma l = (

		match (l1,l2) with 

		([],[]) -> sigma
	  | (x1::xs1,x2::xs2) -> (

	  	match (x1,x2) with 

	  	  (V(a),V(b)) -> (iden_list (xs1,xs2) (iden (x1,x2) sigma l) (a :: b :: l))
	  	 | (V(a),Node(c,l')) -> (iden_list (xs1,xs2) (iden (x1,x2) sigma l) (a :: l))
	  	 | (Node(c,l'),V(a)) -> (iden_list (x2::xs2,x1::xs1) sigma l)
	  	 | (Node(c1,l1),Node(c2,l2)) -> (iden_list (xs1,xs2) (iden (x1,x2) sigma l) l)

	  )

	)

	in 
	(
		match (t1,t2) with 

		(V(x),V(y)) -> if (x=y) then sigma else (function z -> if z=x then V(y) else (sigma z))
	  | (V(x),Node(s,l1)) -> if (occurs x (vars t2)) then raise (Myexp "NOT_UNIFIABLE") else (

	  	 if (occurs x l) then (

	  	 	let temp = sigma x in (

	  	 		match temp with 

	  	 		V(p) -> let alpha = (notVar x p l sigma) in (

	  	 			if (alpha =x) then (function z -> if z=x then t2 else (sigma z))
	  	 			else (

	  	 				let temp1 = sigma alpha in (

	  	 					if (temp1 = t2) then (function z -> if z=x then t2 else (sigma z))
	  	 					else raise (Myexp "NOT_UNIFIABLE")
	  	 				  )

	  	 				)
	  	 			)

	  	 	  | q -> if (q=t2) then sigma else raise (Myexp "NOT_UNIFIABLE")
	  	 	)

	  	 )

	  	else function z -> if z=x then t2 else (sigma z)

	  )

	  | (Node(s,l1),V(x)) -> iden (t2,t1) sigma l
	  | (Node(s1,l1),Node(s2,l2)) -> if ((s1=s2) && ((List.length l1) = (List.length l2))) then (

	  	(iden_list (l1,l2) sigma l)

	  ) else raise (Myexp "NOT_UNIFIABLE")
	)

let rec can_iden (t1,t2) sigma l = 

	let rec can_iden_list (l1,l2) sigma l = (

		match (l1,l2) with 

		([],[]) -> true
	  | (x1::xs1,x2::xs2) -> (

	  	match (x1,x2) with 

	  	  (V(a),V(b)) -> if (can_iden (x1,x2) sigma l) then (can_iden_list (xs1,xs2) (iden (x1,x2) sigma l) (a :: b :: l)) else false
	  	 | (V(a),Node(c,l')) -> if (can_iden (x1,x2) sigma l) then (can_iden_list (xs1,xs2) (iden (x1,x2) sigma l) (a :: l)) else false
	  	 | (Node(c,l'),V(a)) -> (can_iden_list (x2::xs2,x1::xs1) sigma l)
	  	 | (Node(c1,l1),Node(c2,l2)) -> if (can_iden (x1,x2) sigma l) then (can_iden_list (xs1,xs2) (iden (x1,x2) sigma l) l) else false

	  )

	)

	in 
	(
		match (t1,t2) with 

		(V(x),V(y)) -> true
	  | (V(x),Node(s,l1)) -> if (occurs x (vars t2)) then false else (

	  	 if (occurs x l) then (

	  	 	let temp = sigma x in (

	  	 		match temp with 

	  	 		V(p) -> let alpha = (notVar x p l sigma) in (

	  	 			if (alpha =x) then true
	  	 			else (

	  	 				let temp1 = sigma alpha in (

	  	 					if (temp1 = t2) then true
	  	 					else false
	  	 				  )

	  	 				)
	  	 			)

	  	 	  | q -> if (q=t2) then true else false
	  	 	)

	  	 )

	  	else true

	  )

	  | (Node(s,l1),V(x)) -> can_iden (t2,t1) sigma l
	  | (Node(s1,l1),Node(s2,l2)) -> if ((s1=s2) && ((List.length l1) = (List.length l2))) then (

	  	(can_iden_list (l1,l2) sigma l)

	  ) else false
	)
	
(* Returns the most general unifier for the terms t1 and t2*)
let rec mgu t1 t2 = iden (t1,t2) id	[]			

(*
*************************Examples****************************
1. let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("y")])]);;
   let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
   let sigma_final = mgu term1 term2;;
	
   val sigma_final : variable -> term = <fun>
	# sigma_final "x";;
	- : term = V "y"
	# sigma_final "z";;
	- : term = V "y"
	# sigma_final "y";;
	- : term = V "x"
	# sigma_final "w";;
	- : term = V "y"	


2. let term1 = Node("e",[V("x");Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);Node("a",[])])]);;
   let term2 = Node("e",[Node("c",[]);Node("c",[]);Node("d",[Node("d",[Node("a",[]);V("z")]);V("x")])]);;
   let sigma_final = mgu term1 term2;;

	Exception: NOT_UNIFIABLE	


3. let term1 = Node("e",[V("x");V("y");Node("d",[Node("d",[Node("a",[]);V("z")]);Node("a",[])])]);;
   let term2 = Node("e",[V("y");V("z");Node("d",[Node("d",[Node("a",[]);Node("c",[])]);V("x")])]);;
   let sigma_final = mgu term1 term2;;

	Exception: NOT_UNIFIABLE	
*)

(********************************************************END OF FIRST ORDER LOGIC IMPLEMENTATION********************************************************************)
(*******************************************************************************************************************************************************************)

(*Matches the two propositions p and l*)
let match_props p l = match p with 

	Term(s) -> (

		match l with 

		Term(s1) -> (

			match s with 

			V(a) -> (

				match s1 with 

			 	V(x) -> true
		   | Node(c,l2) -> false

			)

		 | Node(b,l1) -> (

		 	match s1 with 

		 	V(x) -> false
		   | Node(c,l2) -> if (c=b) then true else false

		 )


		)

	  | _ -> false

	)
   
    | _ -> false

(* Checks if a negative clause, i.e a clause with a negative literal, is present or not*)
let rec isPresentNeg l c = match c with 

	[] -> false
  | x :: xs -> (

  	match x with 

  	 Not(q) -> (if (match_props q l) then true else (isPresentNeg l xs))
  	| r -> (

  		match l with 

  		Not(s) -> if (match_props s r) then true else (isPresentNeg l xs)

  	  | _ -> (isPresentNeg l xs)


  	)
  )

(* Returns a negative clause*)
let rec getPresentNeg l c = match c with 

	[] -> raise (Myexp "Improper inputs")
  | x :: xs -> (

  	match x with 

  	 Not(q) -> (if (match_props q l) then x else (getPresentNeg l xs))
  	| r -> (

  		match l with 

  		Not(s) -> if (match_props s r) then r else (getPresentNeg l xs)

  	  | _ -> (getPresentNeg l xs)


  	)
  )

let rec getPresentNegList l c_list = match c_list with 

	[] -> []
 |  x :: xs -> (

 	if (isPresentNeg l x) then (

 	match l with 

 	Not(Term(p)) -> (

 		let a = (getPresentNeg l x) in (

 			match a with 

 			Term(q) -> (

 				if (can_iden (p,q) id []) then (l,x,a) :: (getPresentNegList l xs)
 				else (getPresentNegList l xs)
 			)

 		  | _ -> (getPresentNegList l xs)

 		)

 	)

  | Term(p1) -> (

		let a1 = (getPresentNeg l x) in (

 			match a1 with 

 			Not(Term(q1)) -> (

 				if (can_iden (p1,q1) id []) then (l,x,a1) :: (getPresentNegList l xs)
 				else (getPresentNegList l xs)
 			)

 		  | _ -> (getPresentNegList l xs)

 		)

 	)



  )


	 else (getPresentNegList l xs)

 ) 

let rec present x p = match p with 

	[] -> false
 | (a,b,c,d) :: ys -> (

 	match x with 

 	(a1,b1,c1,d1) -> if (((a=a1) && (b=b1) && (c=c1) && (d=d1)) || ((a=c1) && (b=d1) && (c=a1) && (d=b1))) then true else (present x ys)


)

let rec removeOccurencesFrom p r = match r with 

	[] -> []
 | x :: xs -> if (present x p) then (removeOccurencesFrom p xs) else (x :: (removeOccurencesFrom p xs))


let rec makePairs c r = match r with 

	[] -> []
  | (l,c1,l1) :: xs -> (c,l,c1,l1) :: (makePairs c xs)

let rec removeFrom p l = match l with 

	[] -> []
  | x :: xs -> if (present x p) then (removeFrom p xs) else (x) :: (removeFrom p xs)

let rec getMatches c c_list p c' = match c with 

	[] -> []
 | x :: xs -> (let r = (getPresentNegList x c_list) in (

 		match r with 

 		[] -> []
 	  | _  -> (let q = (removeFrom p (makePairs c' r)) in (q) @ (getMatches xs c_list p c'))

	 )

)


let rec findAll setClause p = match setClause with 

	[] -> []
  | x :: xs -> (

  	match x with 

  	 [] -> raise (Myexp "NOT_RESOLVABLE")
  	| _ -> ((getMatches x xs p x) @ (findAll xs p))

  )

let findAnyTwo setClause p = let q = (findAll setClause p) in (

	match q with 

	[] -> raise (Myexp "Can't find any more!")
  | x :: xs -> x

)

(*Returns two clauses such tat one has a positive literal and the other has a negative one*)
let findTwoClauses setClause p = let r = findAnyTwo setClause p in 

	match r with 

	(c,l,c1,l1) -> (c,c1)

(* All the helper functions required to implement the resolution function*)
let rec findLiteral_list c1 c2 = match c1 with 

  x :: xs -> if (isPresentNeg x c2) then (x,(getPresentNeg x c2))::(findLiteral_list xs c2) else (findLiteral_list xs c2)
 | [] -> []

let unify_prop p1 p2 = match p1 with 

	Not(Term(a)) -> (

		match p2 with 

		Term(b) -> (mgu a b)

	)

  | Term(a) -> (

  		match p2 with 

  		Not(Term(b)) -> (mgu a b)

  )	

let applySubst p sigma = match p with 

	Term(a) -> (let b = (subst a sigma) in (Term(b)))
  | Not(Term(a)) -> (let b = (subst a sigma) in ((Not(Term(b)))))

let rec applyUnifList l1 sigma = match l1 with 

	[] -> []
  | x :: xs -> (applySubst x sigma) :: (applyUnifList xs sigma)

let rec member x l = match l with 

	[] -> false
  | y :: ys -> (if y=x then true else (member x ys))


let rec union l1 l2 = match l1 with 

	[] -> l2
  | x :: xs -> (

  	if (member x l2) then (union xs l2) else ([x] @ (union xs l2))

  )

let rec remove_rep l = match l with 

	[] -> []
  | x :: xs -> if (member x xs) then (remove_rep xs) else (x :: (remove_rep xs))

let make_Cres c1 c2 l1 l2 = let sigma = (unify_prop l1 l2) in (

	let rec remove_list a l = (
		match l with 

		x :: xs -> if (x=a) then (remove_list a xs) else x :: (remove_list a xs)
	 | [] -> []

	)

	in

	(
		let l1_list = (remove_list l1 c1) and l2_list = (remove_list l2 c2) in (

			(remove_rep (union (applyUnifList l1_list sigma) (applyUnifList l2_list sigma)))

		)

	)

)
	
let rec oneStepList c1 c2 l p = 
	match l with 

	[] -> []
  | (l1,l2) :: xs -> (

  	let a = (c1,l1,c2,l2) and b = (c2,l2,c1,l1) in (

  		if ((present a p) || (present b p)) then (

  			(oneStepList c1 c2 xs p)
  		)

	  	else (make_Cres c1 c2 l1 l2)

  	)

  )

(* Does the one-step of the two found clauses. Also takes the list of previously resolved clauses in order to prevent it from going in an infinite recursion*)
let oneStep (c1,c2) p = let l = (findLiteral_list c1 c2) in (oneStepList c1 c2 l p)

(* Does the resolution of the set of clauses with the given initial list of previously resolved clauses (should be empty initially)*)
let rec resolution setClause p = let r1 = (findAll setClause p) in 

	(
	
	let r = removeOccurencesFrom p r1 

		in

		(

			match r with 

			 [] -> setClause
		   | (c1,l1,c2,l2) :: xs -> (

				 let c_res = (make_Cres c1 c2 l1 l2) in (

				 	match c_res with 

				 	[] -> setClause
				  | _ -> (

				  	 if (member (c_res) setClause) then ((resolution (remove_rep setClause) (remove_rep ((c1,l1,c2,l2) :: p))))
				  		else((resolution (remove_rep ((setClause) @ [(c_res)])) (remove_rep ((c1,l1,c2,l2) :: p)))	)

				  ) 
				  
				  

				 )

		   )

		)

    )
    