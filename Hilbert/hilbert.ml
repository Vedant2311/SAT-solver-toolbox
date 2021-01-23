(* Defining the Recursive type for the different types of propositions*)
type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop

(*Defining the type for the Hilbert proof Data-structure*)
type proof = Root of prop * proof * proof * string * (prop list) | E

(* Custom Exceptions *)
exception Myexp of string

(* Basic Helper functions*)
let rec member x l = match l with 

  [] -> false
  | y :: ys -> (if y=x then true else (member x ys))


let rec union l1 l2 = match l1 with 

  [] -> l2
  | x :: xs -> (
    if (member x l2) then (union xs l2) else ([x] @ (union xs l2))
  )

let rec remove p delta = match delta with
	x::xs  -> if (x=p) then xs else x :: (remove p xs)
	| _ -> []

let rec sameTable l = match l with 

	[] -> true
  	| x::xs -> (

  		match xs with 

	  		[] -> true

	  		| y::ys -> (

	  			match x with 


	  				Root(p,p1,p2,s,gamma) -> (

	  					match y with 

	  						Root(q,q1,q2,s2,gamma1) -> (

	  							if (gamma=gamma1) then (sameTable xs)
	  						    else false

	  						)
	  				)

	  		)
	  		
  	)

let getTable l = match l with 

	[] -> raise (Myexp "Empty list error")
  | x :: xs -> (
  	match x with
  	 Root(p,p1,p2,s,gamma) -> gamma
 )

let rec getproof l p = match l with 

	[] -> raise (Myexp "Improper list error")
  | x:: xs -> (

  	match  x with
  	 	
  	 	Root(q,q1,q2,s,gamma) -> (
  	 		if(q=p) then x else (getproof xs p)
  	 	)
  )

(* Checks if the 'R' type schema is folllowed*)
let isR p = match p with 

	Impl(p1,p2) -> (match p1 with

		Impl(p3,p4) -> (

			match p2 with 

				Impl(p5,p6) -> (

					match p5 with 

					 Impl(p7,p8) -> (

					 	if ((p7=p3)&&((p3=Not(p6))||(p6=Not(p3)))&((p4=Not(p8))||(p8=Not(p4)))) then true 
					 		else false

					 )

					| _ -> false

				)

			  |	_ ->  false
		)

	  |	_ -> false

	)

	| _ -> false

(* Checks if the 'S' type schema is folllowed*)
let isS p = match p with 

	Impl(p1,p2) -> (

		match p1 with 

		Impl(p3,p4) -> (

			match  p4 with
			
				Impl(p5,p6) -> (

					match p2 with
					 Impl(p7,p8)  -> (

					 	match p7 with
					 	 Impl(p9,p10) -> (

					 	 	match p8 with 

					 	 	 Impl(p11,p12) -> (

					 	 	 	if((p3=p9) && (p3=p11) && (p5=p10) && (p6 = p12)) then true 
					 	 	 		else false
					 	 	 )

					 	 	| _ -> false

					 	 )
					 	| _ -> false

					 )

					| _ -> false

				)

				| _ -> false

		)

		| _ -> false
	)

	| _ -> false

(* Checks if the 'K' type schema is folllowed*)
let isK p = match p with 

	Impl(p1,p2) -> (

		match p2 with 

			Impl(p3,p4) -> (if (p1=p4) then true else false)

			| _ -> false

	)

	| _ -> false	

(* If the proposition is present in the 'Γ' or not*)
let rec isPresent p gamma = match gamma with 

	[] -> false
  | x:: xs -> if (p=x) then true else (isPresent p xs)

(* Given a Hilbert proof tree, checks if it is valid or not*)
let rec valid_hprooftree root = match root with 

							E -> true
						  | Root(p, p1,p2,s,gamma) -> (


						  		match s with 

						  		"MP" -> (

						  			match p1 with 

						  			Root(q,q1,q2,s1,gamma1) -> (

						  				match p2 with 

						  				 Root(r,r1,r2,s3,gamma2) ->(

						  				 	
						  				 	match r with 

						  				 	Impl(p3,p4) -> (

						  				 		if ((q=p3) && (p=p4)&&(gamma2=gamma)&&(gamma2=gamma1)) then true else (


						  				 				match q with 

									  				 		Impl(p5,p6) -> (

									  				 			if ((r=p5)&& (p = p6) && (gamma2=gamma)&&(gamma2=gamma1)) then true else false

									  				 		)

									  				 		| _ -> false
	
						  				 		)

						  				 	)

						  				 	| _ -> (

						  				 		match q with 

						  				 		Impl(p5,p6) -> (

						  				 			if ((r=p5)&& (p = p6) && (gamma2=gamma)&&(gamma2=gamma1)) then true else false

						  				 		)

						  				 		| _ -> false


						  				 	)

						  				 )

						  				| _ -> false

						  			)

						  			| _ -> false

						  		)

						  	   | "R" -> (

						  	   	 if ((p1=E) && (p2 = E) && (isR p)) then true
						  	   	 	else false
						  	   )

						  	   | "S" -> (

						  	   	 if ((p1=E) && (p2 = E) && (isS p)) then true
						  	   	 	else false
						  	   )

						  	   | "K" -> (

						  	   	 if ((p1=E) && (p2 = E) && (isK p)) then true
						  	   	 	else false
						  	   )


						  	   | "Ass" -> (

						  	   	  if((p1=E) && (p2=E) && (isPresent p gamma)) then true
						  	   	  	else false
						  	   )

						  	   | _ -> false

						  )

(* Takes a valid Hlbert proof tree for Γ |- p and a proposition set Δ*)
(* Outputs the valid Hilbert-style proof for Γ U Δ |- p*)
let rec pad root delta = (

	match root with 

		E -> E
	  | Root(p,p1,p2,s,gamma) -> (

	  	 if (isPresent p (union gamma delta)) then Root(p,E,E,"Ass",gamma) 
	  	  else(

	  	  	Root(p,(pad p1 delta),(pad p2 delta),s,gamma)

	  	  )

	  )

)

(* Get the leaves of the tree *)
let rec leaves root = match root with

			 E -> []
			| Root(p,p1,p2,s,gamma) -> (

				match s with 

						  		"MP" -> (

						  			(leaves p1) @ (leaves p2)
						  			
						  		)

						  	   | "R" -> (

						  	   	  []
						  	   )

						  	   | "S" -> (

						  	   	 []

						  	   )

						  	   | "K" -> (

						  	   	  []
						  	   )


						  	   | "Ass" -> (

						  	   		[p]
						  	   )

						  	   

			)

(* Takes a valid Hlbert proof tree for Γ |- p*)
(* Outputs a valid Hilbert proof for Δ |- p, where Δ is a finite subset of Γ*)
let rec prune root = let delta = (leaves root) in (

	match root with 

		E -> E
	 | Root(p,p1,p2,s,gamma) -> Root(p,(prune p1),(prune p2),s,delta)

)

(*
 * Inputs: 
    * root: The (valid) input Hilbert proof tree of judgment Δ |- p, where Δ = {q_1, ..., q_k}
    * l: A list of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k
 * Outputs: A valid Hilbert-style proof of judgment Γ |- p
**)
let rec graft root l =  if (sameTable l) then ( 

	let gamma = (getTable l) in

	(match root with 

		E -> E
	 | Root(p,p1,p2,s,delta) -> (

				match s with 

						  		"MP" -> (

						  			Root(p,(graft p1 l),(graft p2 l),s,gamma)
						  			
						  		)

						  	   | "R" -> (

						  	   	  Root(p,p1,p2,s,gamma)
						  	   )

						  	   | "S" -> (

						  	   	 Root(p,p1,p2,s,gamma)

						  	   )

						  	   | "K" -> (

						  	   	  Root(p,p1,p2,s,gamma)
						  	   )


						  	   | "Ass" -> (

						  	   		(getproof l p)
						  	   )

						  	   

			)
	)

)  else raise (Myexp "Invalid proof list")


let rec getpropslist l q = match l with 

		[] -> q
	  | x::xs -> (

	  	 match x with 

	  	 	Root(p,p1,p2,s,gamma) -> (

	  	 		if ((p1=E)&&(p2=E)) then (getpropslist xs (x::q))
	  	 		 else (
	  	 		 	[x] @ (getpropslist (xs @ [p1] @ [p2]) q)
	  	 		 )
	  	 	)

	  	 	| _ -> []
	  )

let getprops root = match root with 

	E -> []
  | Root(p,p1,p2,s,gamma) -> (

				match s with 

						  	  "MP" -> (

						  			match p1 with
						  			 Root(q,q1,q2,s1,gamma1) -> (

						  			 	match p2 with 

							  			 	Root(r,r1,r2,s2,gamma2) -> (

							  			 		[root] @ (getpropslist [p1;p2] [])

							  			 	)

						  			 )

						  		)

						  	   | "R" -> (

						  	   	  [root]
						  	   )

						  	   | "S" -> (

						  	   	 [root]

						  	   )

						  	   | "K" -> (

						  	   	  [root]
						  	   )


						  	   | "Ass" -> (

						  	   		[root]
						  	   )

						  	   

			)

let rec revlist l = match l with 

	x::xs -> (revlist xs) @ [x]
   | _ -> []

(* Modify the 'gamma' (Γ) for the entire tree, keeping it valid still*)
let rec changeGamma root gamma = match root with 

		E -> E
	 | Root(p,p1,p2,s,delta) -> (

				match s with 

						  		"MP" -> (

						  			Root(p,(changeGamma p1 gamma),(changeGamma p2 gamma),s,gamma)
						  			
						  		)

						  	   | "R" -> (

						  	   	  Root(p,p1,p2,s,gamma)
						  	   )

						  	   | "S" -> (

						  	   	 Root(p,p1,p2,s,gamma)

						  	   )

						  	   | "K" -> (

						  	   	  Root(p,p1,p2,s,gamma)
						  	   )


						  	   | "Ass" -> (

						  	   		Root(p,p1,p2,s,gamma)
						  	   )

			)

let getStandard p gamma = Root(Impl(p,p),(Root(Impl(Impl(p,Impl(L("q"),p)),Impl(p,p)),Root(Impl(Impl(p,Impl(Impl(L("q"),p),p)),Impl(Impl(p,Impl(L("q"),p)),Impl(p,p))),E,E,"S",gamma),Root(Impl(p,Impl(Impl(L("q"),p),p)),E,E,"K",gamma),"MP",gamma)),(Root(Impl(p,Impl(L("q"),p)),E,E,"K",gamma)),"MP",gamma)

let getAxiom p q gamma = if (isR q) then (

								Root(Impl(p,q),(Root(q,E,E,"R",gamma)),(Root(Impl(q,Impl(p,q)),E,E,"K",gamma)),"MP",gamma)

							)

						else(

							if(isK q) then (

								Root(Impl(p,q),(Root(q,E,E,"K",gamma)),(Root(Impl(q,Impl(p,q)),E,E,"K",gamma)),"MP",gamma)

							)

						    else(

						    	if(isS q) then (

						    		Root(Impl(p,q),(Root(q,E,E,"S",gamma)),(Root(Impl(q,Impl(p,q)),E,E,"K",gamma)),"MP",gamma)

						    	)

						    	else (

						    		Root(Impl(p,q),(Root(q,E,E,"Ass",gamma)),(Root(Impl(q,Impl(p,q)),E,E,"K",gamma)),"MP",gamma)

						    	)

						    )

						)

let rec getsubproof q qs l = match qs with 

	[] -> E
  | x::xs -> (

  		match l with 

  			y :: ys -> (

  				match y with 

		  			Root(y',_,_,_,_) ->	if (q=y') then x else (getsubproof q xs ys)

		  		   | E -> (getsubproof q xs ys)
  			)

  			| [] -> E


  )

let rec getInduction p qi ql gamma pi1 pi2 = Root(Impl(p,ql),(Root(Impl(Impl(p,qi),Impl(p,ql)),pi2,(Root(Impl(Impl(p,Impl(qi,ql)),Impl(Impl(p,qi),Impl(p,ql))),E,E,"S",gamma)),"MP",gamma)),pi1,"MP",gamma)

let rec deduction p l gamma qs l'= match l with

		x :: xs -> (

			match x with 

				Root(q,q1,q2,s,delta) -> (

					if((q1=E)&&(q2=E)) then (

						if (q=p) then (((getStandard p gamma)) :: (deduction p xs  gamma ( qs @ [(getStandard p gamma)]) l'))
							else (

								((getAxiom p q gamma) :: (deduction p xs  gamma ( qs @ [(getAxiom p q gamma)]) l'))

							)

					)

					 else (


					 	 
								match q1 with 

								 Root(qi,q1',q2',s',delta) -> (

								 	match q2 with 

								 		Root(qj,_,_,_,delta) -> (

							 	 let pi1 = (getsubproof qi qs l') and pi2 = (getsubproof qj qs l') in 
								 		  

								 		  (
								 			if(qi = Impl(qj,q)) then (

								 				((getInduction p qj q gamma pi2 pi1) :: (deduction p xs  gamma ( qs @ [(getInduction p qj q gamma pi2 pi1)]) l'))								 		    	
								 			)

								 		    else (

												((getInduction p qi q gamma pi1 pi2) :: (deduction p xs  gamma ( qs @ [(getInduction p qi q gamma pi1 pi2)]) l'))								 		    	

								 		    )

								 		  )

								 		)

								 )					 	 	

					 )

				)

				| _ -> raise (Myexp "Improper proofs given")

		)

		| _ -> []

(*
 * Inputs:
    * root: The (valid) input Hilbert proof tree of judgement Γ U {p}  |- q
    * p: The proposition 'p' used in the above definition of root
 * Outputs: A valid Hilbert-style proof of judgment Γ |- p -> q
**)
let dedthm root p = 

	match root with 

		Root(_,_,_,_,delta) -> 	let l = (deduction p (revlist (getprops root)) (remove p delta) [] (revlist (getprops root))) in (List.hd (revlist l))
	 | _ -> E
