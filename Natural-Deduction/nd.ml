(* Defining the Recursive type for the different types of propositions*)
type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop

(*Defining the type for the Natural Deduction proof Data-structure*)
type nat = Root of prop  * nat * nat * nat * (prop list) * string | E 

(* Custom Exception *)
exception Myexp of string

(* Basic Helper functions *)
let rec member x l = match l with 
  [] -> false
  | y :: ys -> (if y=x then true else (member x ys))

let rec union l1 l2 = match l1 with 

  [] -> l2
  | x :: xs -> (
    if (member x l2) then (union xs l2) else ([x] @ (union xs l2))
  )

let rec deletion l1 l2 = match l1 with 
  [] -> []
| x:: xs -> if (member x l2) then (deletion xs l2) else (x :: (deletion xs l2))  

let add p l = if (member p l) then l else p :: l

let rec delete x l = match l with 
  y :: ys -> if (x=y) then ys else y :: (delete x ys)
 | _ -> []

let rec removeRep l1 = match l1 with 
	 [] -> []
	 | x :: xs -> if (xs=[]) then [x] else(
	 	match xs with 
	 	 y :: ys -> if (x=y) then ((removeRep xs)) else (x::(removeRep xs))
	 ) 

let rec equals l1' l2' = let l1 = (removeRep l1') and l2 = (removeRep l2') in 

	(if ((List.length l1) = (List.length l2)) then (

			match l1 with 

			 [] -> true
		 |	x :: xs -> (if (member x l2) then (equals xs (delete x l2)) else false)

	) else false )

(* Checks for the axiom type '->-I' *)
let isImplI p r1 r2 r3 gamma = match p with 

     			 Impl(p1,q1) -> (

     			 	match r1 with 

     			 	 E -> (

     			 	 	match r2 with 

     			 	 	 E -> (

     			 	 	 	match r3 with 

     			 	 	 	 E -> false
     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

     			 	 	   	  if ((p'=q1) && (equals gamma' (add p1 gamma))) then (true)
     			 	 	   	  else false
     			 	 	   )

     			 	 	 )

     			 	   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=q1) && (equals gamma' (add p1 gamma)) && (r3=E)) then (true)
     			 	 	  else false


     			 	   )

     			 	 )

                   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=q1) && (equals gamma' (add p1 gamma)) && (r3=E) && (r2=E)) then (true)
     			 	 	  else false


     			 	   )

     			 )

     			 | _ -> false

(* Returns for the axiom type '->-I' *)
let retImplI p r1 r2 r3 gamma =  match p with 

     			 Impl(p1,q1) -> (

     			 	match r1 with 

     			 	 E -> (

     			 	 	match r2 with 

     			 	 	 E -> (

     			 	 	 	match r3 with 

     			 	 	 	 E -> E
     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

     			 	 	   	  if ((p'=q1) && (equals gamma' (add p1 gamma))) then (r3)
     			 	 	   	  else E
     			 	 	   )

     			 	 	 )

     			 	   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=q1) && (equals gamma' (add p1 gamma)) && (r3=E)) then (r2)
     			 	 	  else E


     			 	   )

     			 	 )

                   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=q1) && (equals gamma' (add p1 gamma)) && (r3=E) && (r2=E)) then (r1)
     			 	 	  else E


     			 	   )

     			 )

     			 | _ -> E

(* Checks for the axiom type '~-Int' *)
let isNotInt p r1 r2 r3 gamma = match r1 with 

     			 	 E -> (

     			 	 	match r2 with 

     			 	 	 E -> (

     			 	 	 	match r3 with 

     			 	 	 	 E -> false
     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

     			 	 	   	  if ((p'=F) && (equals gamma' (gamma))) then (true)
     			 	 	   	  else false
     			 	 	   )

     			 	 	 )

     			 	   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=F)  && (r3=E)&& (equals gamma' (gamma))) then (true)
     			 	 	  else false


     			 	   )

     			 	 )

                   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=F)  && (r3=E) && (r2=E)&& (equals gamma' (gamma))) then (true)
     			 	 	  else false


     			 	   )
    			 
(* Returns for the axiom type '~-Int' *)    			 
let retNotInt p r1 r2 r3 gamma = match r1 with 

     			 	 E -> (

     			 	 	match r2 with 

     			 	 	 E -> (

     			 	 	 	match r3 with 

     			 	 	 	 E -> E
     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

     			 	 	   	  if ((p'=F)&& (equals gamma' (gamma))) then (r3)
     			 	 	   	  else E
     			 	 	   )

     			 	 	 )

     			 	   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=F)  && (r3=E)&& (equals gamma gamma')) then (r2)
     			 	 	  else E


     			 	   )

     			 	 )

                   | Root(p',_,_,_,gamma',_) -> (

						  if ((p'=F)  && (r3=E) && (r2=E)&& (equals gamma gamma')) then (r1)
     			 	 	  else E


     			 	   )

(* Checks for the axiom type '~-Class' *)
let isNotClass p r1 r2 r3 gamma = 


		match p with 

			Not(p'') ->(		match r1 with 

	     			 	 E -> (

	     			 	 	match r2 with 

	     			 	 	 E -> (

	     			 	 	 	match r3 with 

	     			 	 	 	 E -> false
	     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

	     			 	 	   	  if ((p'=F) && (equals gamma' (add p'' gamma))) then (true)
	     			 	 	   	  else false
	     			 	 	   )

	     			 	 	 )

	     			 	   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add p'' gamma)))  && (r3=E)) then (true)
	     			 	 	  else false


	     			 	   )

	     			 	 )

	                   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma'  (add p'' gamma)))  && (r3=E) && (r2=E)) then (true)
	     			 	 	  else false


	     			 	   )

					)

		| _ -> (


			match r1 with 

	     			 	 E -> (

	     			 	 	match r2 with 

	     			 	 	 E -> (

	     			 	 	 	match r3 with 

	     			 	 	 	 E -> false
	     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

	     			 	 	   	  if ((p'=F) && (equals gamma' (add (Not(p)) gamma))) then (true)
	     			 	 	   	  else false
	     			 	 	   )

	     			 	 	 )

	     			 	   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add (Not(p)) gamma)))  && (r3=E)) then (true)
	     			 	 	  else false


	     			 	   )

	     			 	 )

	                   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add (Not(p)) gamma)))  && (r3=E) && (r2=E)) then (true)
	     			 	 	  else false


	     			 	   )


		)

(* Returns for the axiom type '~-Class' *)
(* I am assuming the INF form i.e. No Not(Not(p)) case will be there*)
let retNotClass p r1 r2 r3 gamma = match p with 

			Not(p'') ->(		match r1 with 

	     			 	 E -> (

	     			 	 	match r2 with 

	     			 	 	 E -> (

	     			 	 	 	match r3 with 

	     			 	 	 	 E -> E
	     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

	     			 	 	   	  if ((p'=F) && (equals gamma' (add p'' gamma))) then (r3)
	     			 	 	   	  else E
	     			 	 	   )

	     			 	 	 )

	     			 	   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add p'' gamma)))  && (r3=E)) then (r2)
	     			 	 	  else E


	     			 	   )

	     			 	 )

	                   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma'  (add p'' gamma)))  && (r3=E) && (r2=E)) then (r1)
	     			 	 	  else E


	     			 	   )

					)

		| _ -> (


			match r1 with 

	     			 	 E -> (

	     			 	 	match r2 with 

	     			 	 	 E -> (

	     			 	 	 	match r3 with 

	     			 	 	 	 E -> E
	     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

	     			 	 	   	  if ((p'=F) && (equals gamma' (add (Not(p)) gamma))) then (r3)
	     			 	 	   	  else E
	     			 	 	   )

	     			 	 	 )

	     			 	   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add (Not(p)) gamma)))  && (r3=E)) then (r2)
	     			 	 	  else E


	     			 	   )

	     			 	 )

	                   | Root(p',_,_,_,gamma',_) -> (

							  if (((p'=F) && (equals gamma' (add (Not(p)) gamma)))  && (r3=E) && (r2=E)) then (r1)
	     			 	 	  else E


	     			 	   )

		)

(* Checks for the axiom type '/\-EL' *)
let isAndEL p r1 r2 r3 gamma = match r1 with 

		     			 	 E -> (

		     			 	 	match r2 with 

		     			 	 	 E -> (

		     			 	 	 	match r3 with 

		     			 	 	 	 E -> false
		     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

		     			 	 	   		match p' with 

		     			 	 	   		And(p1',p2') -> if ((p1'=p)&& (equals gamma gamma')) then (true) else false
		     			 	 	   		| _ -> false
		     			 	 	   	)

		     			 	 	 )

		     			 	   | Root(p',_,_,_,gamma',_) -> (

								  match p' with 

		     			 	 	   	And(p1',p2') -> if ((p1'=p) && (r3=E)&& (equals gamma gamma')) then (true) else false
		     			 	 	   	| _ -> false


		     			 	   )

		     			 	 )

		                   | Root(p',_,_,_,gamma',_) -> (

								match p' with 

		     			 	 	And(p1',p2') -> if ((p1'=p) && (r3=E) && (r2=E)&& (equals gamma gamma')) then (true) else false
		     			 	 	| _ -> false

	 

		     			 	)

(* Returns for the axiom type '/\-EL' *)
let retAndEL p r1 r2 r3 gamma = match r1 with 

		     			 	 E -> (

		     			 	 	match r2 with 

		     			 	 	 E -> (

		     			 	 	 	match r3 with 

		     			 	 	 	 E -> E
		     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

		     			 	 	   		match p' with 

		     			 	 	   		And(p1',p2') -> if ((p1'=p)&& (equals gamma gamma')) then (r3) else E
		     			 	 	   		| _ -> E
		     			 	 	   	)

		     			 	 	 )

		     			 	   | Root(p',_,_,_,gamma',_) -> (

								  match p' with 

		     			 	 	   	And(p1',p2') -> if ((p1'=p) && (r3=E)&& (equals gamma gamma')) then (r2) else E
		     			 	 	   	| _ -> E


		     			 	   )

		     			 	 )

		                   | Root(p',_,_,_,gamma',_) -> (

								match p' with 

		     			 	 	And(p1',p2') -> if ((p1'=p) && (r3=E) && (r2=E)&& (equals gamma gamma')) then (r1) else E
		     			 	 	| _ -> E

	 

		     			 	)

(* Returns for the axiom type '/\-ER' *)
let retAndER p r1 r2 r3 gamma = match r1 with 

			     			 	 E -> (

			     			 	 	match r2 with 

			     			 	 	 E -> (

			     			 	 	 	match r3 with 

			     			 	 	 	 E -> E
			     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

			     			 	 	   		match p' with 

			     			 	 	   		And(p1',p2') -> if ((p2'=p)&& (equals gamma gamma')) then (r3) else E
			     			 	 	   		| _ -> E
			     			 	 	   	)

			     			 	 	 )

			     			 	   | Root(p',_,_,_,gamma',_) -> (

									  match p' with 

			     			 	 	   	And(p1',p2') -> if ((p2'=p) && (r3=E)&& (equals gamma gamma')) then ( r2) else E
			     			 	 	   	| _ -> E


			     			 	   )

			     			 	 )

			                   | Root(p',_,_,_,gamma',_) -> (

									match p' with 

			     			 	 	And(p1',p2') -> if ((p2'=p) && (r3=E) && (r2=E)&& (equals gamma gamma')) then (r1) else E
			     			 	 	| _ -> E

			     			 	)

 
(* A highly complicated function that would check if the given Input ND proof tree is valid or not*)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let rec valid_ndprooftree root = let rec valid_ndprooftreelist l = (match l with 

	[] -> true
  | x:: xs -> (valid_ndprooftree x) && (valid_ndprooftreelist xs)
)

in

(

	match root with 

	E -> true
  | Root(p,r1,r2,r3,gamma,s) -> (

  	if ((member p gamma) && (r1=E) && (r2=E) && (r3=E) && (s="Hyp")) then true
    else (

  		if ((p=T) && (r1=E) && (r2=E) && (r3=E) && (s="T-I")) then true 
     	else (

     		if(s="->-I") then (

				if (isImplI p r1 r2 r3 gamma) then (valid_ndprooftree (retImplI p r1 r2 r3 gamma)) else false
     			
     		)

     		else(

                if (s="~-Int") then (
						
					if (isNotInt p r1 r2 r3 gamma) then (valid_ndprooftree (retNotInt p r1 r2 r3 gamma)) else false
     			
                )

                else(

                	if (s="~-Class") then (

							if (isNotClass p r1 r2 r3 gamma) then (valid_ndprooftree (retNotClass p r1 r2 r3 gamma)) else false
     			
                	)

                	else (

                		if (s="/\\-EL") then (

                			 	if (isAndEL p r1 r2 r3 gamma) then (valid_ndprooftree (retAndEL p r1 r2 r3 gamma)) else false
     			
                		)

                	    else (
 
                	    	if (s="/\\-ER") then (

                	    		match r1 with 

			     			 	 E -> (

			     			 	 	match r2 with 

			     			 	 	 E -> (

			     			 	 	 	match r3 with 

			     			 	 	 	 E -> false
			     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

			     			 	 	   		match p' with 

			     			 	 	   		And(p1',p2') -> if ((p2'=p)&& (equals gamma gamma')) then (valid_ndprooftree r3) else false
			     			 	 	   		| _ -> false
			     			 	 	   	)

			     			 	 	 )

			     			 	   | Root(p',_,_,_,gamma',_) -> (

									  match p' with 

			     			 	 	   	And(p1',p2') -> if ((p2'=p) && (r3=E)&& (equals gamma gamma')) then (valid_ndprooftree r2) else false
			     			 	 	   	| _ -> false


			     			 	   )

			     			 	 )

			                   | Root(p',_,_,_,gamma',_) -> (

									match p' with 

			     			 	 	And(p1',p2') -> if ((p2'=p) && (r3=E) && (r2=E)&& (equals gamma gamma')) then (valid_ndprooftree r1) else false
			     			 	 	| _ -> false

		 

			     			 	)


	                			
                		    )

                	        else (


                	        	if (s="\\/-IL") then (

                	        		match p with 

                	        		 Or(p1,p2) -> (


                	        		 	match r1 with 

					     			 	 E -> (

					     			 	 	match r2 with 

					     			 	 	 E -> (

					     			 	 	 	match r3 with 

					     			 	 	 	 E -> false
					     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

					     			 	 	   	   if ((p'=p1)&& (equals gamma gamma')) then (valid_ndprooftree r3) else false
					     			 	 	   	)

					     			 	 	 )

					     			 	   | Root(p',_,_,_,gamma',_) -> (

					     			 	   		 if ((p'=p1) && (r3=E)&& (equals gamma gamma')) then (valid_ndprooftree r2) else false

					     			 	   )

					     			 	 )

					                   | Root(p',_,_,_,gamma',_) -> (

				 							 if ((p'=p1) && (r2=E) && (r3=E)&& (equals gamma gamma')) then (valid_ndprooftree r1) else false	

					     			 	)



                	        		 )

                	        	   | _ -> false

                	        	)

                	            else (

                	            	if (s="\\/-IR") then (

	                	        		match p with 

	                	        		 Or(p1,p2) -> (


	                	        		 	match r1 with 

						     			 	 E -> (

						     			 	 	match r2 with 

						     			 	 	 E -> (

						     			 	 	 	match r3 with 

						     			 	 	 	 E -> false
						     			 	 	   | Root(p',r1',r2',r3',gamma',s') -> (

						     			 	 	   	   if ((p'=p2)&& (equals gamma gamma')) then (valid_ndprooftree r3) else false
						     			 	 	   	)

						     			 	 	 )

						     			 	   | Root(p',_,_,_,gamma',_) -> (

						     			 	   		 if ((p'=p2) && (r3=E)&& (equals gamma gamma')) then (valid_ndprooftree r2) else false

						     			 	   )

						     			 	 )

						                   | Root(p',_,_,_,gamma',_) -> (

					 							 if ((p'=p2) && (r2=E) && (r3=E)&& (equals gamma gamma')) then (valid_ndprooftree r1) else false	

						     			 	)



	                	        		 )

	                	        	   | _ -> false

	                	        	)

                	                else (


                	                	if (s="\\/-E") then (

                	                		match r1 with 

                	                		Root(p',_,_,_,gamma1',_) -> (

                	                			if (p'=p) then (

                	                				match r2 with 

                	                				 E -> false
                	                			  | Root(p'',_,_,_,gamma2',_) -> (

                	                			  	if ((p''=p)) then (

                	                			  		match r3 with

                	                			  		 E -> false
                	                			  	   | Root(p1'',_,_,_,gamma3',_) -> (

                	                			  	   		match p1'' with 

                	                			  	   		 Or(p1,p2) -> (

  																if ((equals gamma3' gamma)) then (

  																	if (equals gamma2' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then valid_ndprooftreelist [r1;r2;r3] else false)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then valid_ndprooftreelist [r1;r2;r3] else false)
  																		else false

  																	)				
  																)
  																
  																else false

                	                			  	   		 )

                	                			  	   	   | _ -> false

                	                			  	   )
                	                			  	)

                	                			    else (


                	                			    	match p'' with 

                	                			    		Or(p1,p2) -> (

                	                			    			match r3 with 

                	                			    			E -> false
                	                			    		 | Root(p1'',_,_,_,gamma3',_) -> (

                	                			    		 	if ((p1''=p) && ( equals gamma2' gamma)) then (

                	                			    		 		if (equals gamma3' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then valid_ndprooftreelist [r1;r2;r3] else false)
  																	else (
  																		if (equals gamma3' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then valid_ndprooftreelist [r1;r2;r3] else false)
  																		else false

  																	)
                	                			    		 	)


                	                			    		    else false
                	                			    		 )

                	                			    		)

                	                			    	| _ -> false	

                	                			    )

                	                			  )

                	                			)

                	                		    else(

                	                		    	match p' with 

                	                		    	 Or(p1,p2) -> (

                	                		    	 	match r2 with 

                	                		    	 	 E -> false
                	                		    	    | Root(p'',_,_,_,gamma2',_) -> (

                	                		    	    	match r3 with 

                	                		    	    	 E -> false
                	                		    	      | Root(p1'',_,_,_,gamma3',_) -> (

                	                		    	      	if ((p''=p) && (p1'' = p) && (equals gamma1' gamma)) then (

                	                		    	      		if (equals gamma2' (add p1 gamma)) then (if (equals gamma3' (add p2 gamma)) then (valid_ndprooftreelist [r1;r2;r3]) else false)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma3' (add p1 gamma)) then (valid_ndprooftreelist [r1;r2;r3]) else false)
  																		else false

  																	)

                	                		    	      	)

                	                		    	      	else false

                	                		    	      )
                	                		    	    	
                	                		    	    )

                	                		    	 )

                	                		    	| _ -> false

                	                		    ) 

                	                		)

                	                	  | E -> false


                	                	)

                	                	
                	                    else (

                	                    	if (s="/\\-I") then (

                	                    		match p with 

                	                    		And(p1,p2) -> (

                	                    			match r1 with 

                	                    			E -> (

                	                    				match r2 with 

                	                    				 E -> false
                	                    			   | Root(p'',_,_,_,gamma2',_) -> (

                	                    			   		match r3 with 

                	                    			   		 E -> false
                	                    			   	  | Root(p1'',_,_,_,gamma3',_) -> (

                	                    			   	  	 if ((equals gamma3' gamma) && ( equals gamma2' gamma)) then (

                	                    			   	  	 	if (((p1''=p1) && (p''=p2)) || ((p1''=p2) && (p''=p1))) then (valid_ndprooftreelist [r2;r3]) else false
                	                    			   	  	 )

                	                    			   	  	 else false

                	                    			   	  )

                	                    			   )

                	                    			)

                	                    		  | Root(p',_,_,_,gamma1',_) -> (

                	                    		  	  match r2 with 

                	                    		  	   E -> (

                	                    		  	   	
                	                    		  	   	 match r3 with 

                	                    		  	   	  E -> false
 														| Root(p1'',_,_,_,gamma3',_) -> (


 															if ((((p1''=p2) && (p'=p1)) || ((p1''=p1) && (p'=p2))) && (gamma3'=gamma) && (gamma1'=gamma)) then (valid_ndprooftreelist [r1;r3]) else false


 														)


                	                    		  	   )

                	                    		  	 | Root(p'',_,_,_,gamma2',_) -> (

                	                    		  	 	if ((r3 =E) && (((p''=p2) && (p'=p1)) || ((p''=p1) && (p'=p2))) && (gamma2'=gamma) && (gamma1'=gamma)) then (valid_ndprooftreelist [r1;r2]) else false

                	                    		  	 )

                	                    		  )

                	                    		)

                	                    	  | _ -> false


                	                    	)

                	                        else (

                	                        	if (s="->-E") then (

                	                        		match r1 with 

                	                        		 E -> (

                	                        		 	match r2 with 

                	                        		 	 E -> false
                	                        		   | Root(p'',_,_,_,gamma2',_) -> (

                	                        		   		match r3 with
                	                        		   		  E -> false
                	                        		   		| Root(p1'',_,_,_,gamma3',_) -> (

                	                        		   			match p'' with 


                	                        		   			Impl(p1,p2) -> (

                	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r2;r3]) else (


                	                        		   					match p1'' with 

		                	                        		   		  		Impl(p1,p2) -> (

		                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r2;r3]) else false
		                	                        		   		  		)

		                	                        		   		  	  | _ -> false

		                	                        		   				)

                	                        		   			)

                	                        		   		  | _ -> (

                	                        		   		  		match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (

                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r2;r3]) else false
                	                        		   		  		)

                	                        		   		  	  | _ -> false

                	                        		   		  )

                	                        		   		)

                	                        		   )

                	                        		 )

                	                        	   | Root(p',_,_,_,gamma1',_) -> (


                	                        	   		match r2 with 

                	                        	   		 E -> (

                	                        	   		 	match r3 with 

                	                        	   		 	 E -> false
                	                        	   		  | Root(p1'',_,_,_,gamma3',_) -> (


                	                        	   		  		match p' with 


                	                        		   			Impl(p1,p2) -> (

                	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r1;r3]) else (

                	                        		   					match p1'' with 

		                	                        		   		  		Impl(p1,p2) -> (

		                	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r1;r3]) else false
		                	                        		   		  		)

		                	                        		   		  	| _ -> false


                	                        		   				)

                	                        		   			)

                	                        		   		  | _ -> (

                	                        		   		  		match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (

                	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (valid_ndprooftreelist [r1;r3]) else false
                	                        		   		  		)

                	                        		   		  	  | _ -> false

                	                        		   		  )


                	                        	   		  )

                	                        	   		 )

                	                        	   	  | Root(p'',_,_,_,gamma2',_) -> (

                	                        	   	  	if (r3=E) then (

                	                        	   	  		match p' with 


                	                        		   			Impl(p1,p2) -> (

                	                        		   				if ((p2=p) && (p1 = p'') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (valid_ndprooftreelist [r1;r2]) else (

                	                        		   					match p'' with 

		                	                        		   		  		Impl(p1,p2) -> (

		                	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (valid_ndprooftreelist [r1;r2]) else false
		                	                        		   		  		)

		                	                        		   		  	  | _ -> false


                	                        		   				)

                	                        		   			)

                	                        		   		  | _ -> (

                	                        		   		  		match p'' with 

                	                        		   		  		Impl(p1,p2) -> (

                	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (valid_ndprooftreelist [r1;r2]) else false
                	                        		   		  		)

                	                        		   		  	  | _ -> false

                	                        		   		  )


                	                        	   	  	) else false

                	                        	   	  )
                	                        	   	  	 

                	                        	   )

                	                        	)

                	                            else (raise (Myexp s))

                	                        )
                	                    	

                       	                )
                	                	

                	                )


                  	            )


                	        )


                     	)


                	)

                )

     		)

     	)

    )
  )

)

(* Takes a valid ND proof tree for Γ |- p and a proposition set Δ*)
(* Outputs the valid ND proof for Γ U Δ |- p*)
let rec pad root delta = (

	match root with 

		E -> E
	  | Root(p,p1,p2,p3,gamma,s) -> (

	  	 if (member p (union gamma delta)) then Root(p,E,E,E,(union gamma delta),"Hyp") 
	  	  else(

	  	  	Root(p,(pad p1 delta),(pad p2 delta),(pad p3 delta),(union gamma delta),s)

	  	  )

	  )

)

(* Get the leaves of the tree *)
let rec leaves root = match root with

			 E -> []
			| Root(p,p1,p2,p3,gamma,s) -> (

				match s with 

					"Hyp" -> [p]
				  | "T-I" -> []
				  | _ -> ((leaves p1) @ (leaves p2)) @ (leaves p3)	  							  	   

			)

let rec pruneTemp p delta gamma = match p with 

 E -> E 
| Root(p',p1',p2',p3',gamma',s') -> Root(p',(pruneTemp p1' delta gamma), (pruneTemp p2' delta gamma), (pruneTemp p3' delta gamma), (union delta (deletion gamma' gamma)), s')


(* Takes a valid ND proof tree for Γ |- p*)
(* Outputs a valid ND proof for Δ |- p, where Δ is a finite subset of Γ*)
let prune root = let delta = (leaves root) in (

	match root with 

		E -> E
	 | Root(p,p1,p2,p3,gamma,s) -> Root(p,(pruneTemp p1 delta gamma),(pruneTemp p2 delta gamma),(pruneTemp p3 delta gamma),delta,s)
)


let rec sameTable l = match l with 

	[] -> true
  | x::xs -> (

  	match xs with 


  		[] -> true

  		| y::ys -> (

  			match x with 


  				Root(p,p1,p2,p3,gamma,s) -> (

  					match y with 

  						Root(q,q1,q2,q3,gamma1,s2) -> (

  							if (equals gamma gamma1) then (sameTable xs)
  						    else false

  						)

  					| _ -> false

  				)

  			 | _ -> false

  		)
  )



let getTable l = match l with 

	[] -> raise (Myexp "Empty list error")
  | x :: xs -> (match x with
  	
  	 Root(p,p1,p2,p3,gamma,_) -> gamma
  	| _ -> []
 
 )
             			
let rec getproof l p = match l with 

	[] ->E
  | x:: xs -> (

  	match  x with
  	 	
  	 	Root(q,q1,q2,q3,gamma,s) -> (

  	 		if(q=p) then x else (getproof xs p)

  	 	)

  	  | E -> raise (Myexp "Invalid proof")
 
  )

let rec graftTemp root l delta = if (sameTable l) then ( 

	let gamma = (getTable l) in

	(match root with 

		E -> E
	 | Root(p,p1,p2,p3,delta',s) -> (

				match s with 

				"Hyp" -> (getproof l p)

			  | "T-I" -> Root(p,p1,p2,p3,gamma,s)
			  | _ -> Root(p,(graftTemp p1 l delta),(graftTemp p2 l delta),(graftTemp p3 l delta),(union (deletion delta' delta) gamma),s)		  		  	
						  	   

			)
	)

)  else raise (Myexp "Invalid proof list")


(*
 * Inputs: 
	* root: The (valid) input ND proof tree of judgment Δ |- p, where Δ = {q_1, ..., q_k}
	* l: A list of proof trees π_1, ... π_k of judgments Γ |- q_1 ... Γ |- q_k
** Outputs: A valid ND proof of judgment Γ |- p
*)
let graft root l =  if (sameTable l) then ( 

	let gamma = (getTable l) in

	(match root with 

		E -> E
	 | Root(p,p1,p2,p3,delta,s) -> (

				match s with 

				"Hyp" -> (getproof l p)

			  | "T-I" -> Root(p,p1,p2,p3,gamma,s)
			  | _ -> Root(p,(graftTemp p1 l delta),(graftTemp p2 l delta),(graftTemp p3 l delta),gamma,s)		  		  	
						  	   

			)
	)

)  else raise (Myexp "Invalid proof list")


let getVal r1 r2 r3 = if(r1=E) then (if (r2=E) then r3 else r2) else r1

(* A complicated function that takes a valid ND proof tree and returns if it has an r-pair or not *)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let rec has_rpair root = match root with 

  E -> false
| Root(p,r1,r2,r3,gamma,s) -> (

	if(s="/\\-EL") then (

		let r' = (retAndEL p r1 r2 r3 gamma) in (

			match r' with 

			E -> false
		  | Root(p',r1',r2',r3',gamma',s') -> (

		  	 if (s'="/\\-I") then (

		  	 	true

		  	 )

		  	else (has_rpair r')


		  )

		)

	)
 
    else(

    	if (s="/\\-ER") then (

    		let r' = (retAndER p r1 r2 r3 gamma) in (

				match r' with 

				E -> false
			  | Root(p',r1',r2',r3',gamma',s') -> (

			  	 if (s'="/\\-I") then (

			  	 	true

			  	 )

			  	else (has_rpair r')


			  )

			)



    	)

        else(


        	if (s="->-E") then (



                	    match r1 with 

                	     E -> (

                	              match r2 with
                       		 	 E -> false
                     		   | Root(p'',_,_,_,gamma2',_) -> (

                       		   		match r3 with
                     		   		  E -> false
                  		   			| Root(p1'',_,_,_,gamma3',_) -> (

                        		   			match p'' with 


   	                        		   			Impl(p1,p2) -> (

  	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

  	                        		   					match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r2))


  	                        		   				) else (

          	                        		   					match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (
                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

                	                        		   		  						match r3 with 

								  	                        		   					E -> false
								  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r2))
									


                	                        		   		  			) else false
                	                        		   		  		)

                	                        		   		  	  | _ -> false

               	                        		   		)

	                        		   			)

   	                        		   		  | _ -> (

   	                        		   		  		match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

   	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

   	                        		   		  						match r3 with 

			  	                        		   					E -> false
			  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r2))



   	                        		   		  			) else false
	                        		   		  		)

                	                        		| _ -> false

	                        				  )

    	             		   		   )

	              		           )

                	        )

                 	   | Root(p',_,_,_,gamma1',_) -> (


                       	   		match r2 with 

                     	   		 E -> (

                      	   		 	match r3 with 

                      	   		 	 E -> false
                      	   		  | Root(p1'',_,_,_,gamma3',_) -> (

                        	   		  		match p' with 


	                       		   			Impl(p1,p2) -> (

		                   		   				if ((p2=p) && (p1 = p1'') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

		                   		   							match r1 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r1))


		                   		   				) else (

                        		   					match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r1))


  	                        		   		  			) else false
   	                        		   		  		)

   	                        		   		  		| _ -> false


                        		   				)

                	                        )

                        		   		  | _ -> (

                        		   		  		match p1'' with 

  	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r3) || (has_rpair r1))


  	                        		   		  			) else false
   	                        		   		  		)

                        		   		  	  | _ -> false

	                       		   		  )


	                       	   		  )
                       	   		 )


                       	   	  | Root(p'',_,_,_,gamma2',_) -> (

		                 	   	  	if (r3=E) then (

 	                        	   	  		match p' with 

   	                        		   			Impl(p1,p2) -> (

 	                        		   				if ((p2=p) && (p1 = p'') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

 	                        		   							match r1 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))


 	                        		   				) else (

     	                        		   					match p'' with 

	       	                        		   		  		Impl(p1,p2) -> (

	       	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

	       	                        		   		  						match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))


	       	                        		   		  			) else false
	         	                        		   		  		)

		      	                        		   		  	  | _ -> false


              	                        		   	 )

                	                   			)

    	                        		   		  | _ -> (

      	                        		   		  		match p'' with 

        	                        		   		  		Impl(p1,p2) -> (

          	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

          	                        		   		  						match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))



          	                        		   		  			) else false
           	                        		   		  		)

            	                        		   		  	  | _ -> false

             	                        		   		)


                	                 ) else false

                     	   	  )
               	                        	   	  	 

                	     )

        	)


        	

            else(

            	if (s="\\/-E") then (

									match r1 with 

                	                		Root(p',_,_,_,gamma1',_) -> (

                	                			if (p'=p) then (

                	                				match r2 with 

                	                				 E -> false
                	                			  | Root(p'',_,_,_,gamma2',_) -> (

                	                			  	if ((p''=p)) then (

                	                			  		match r3 with

                	                			  		 E -> false
                	                			  	   | Root(p1'',_,_,_,gamma3',_) -> (

                	                			  	   		match p1'' with 

                	                			  	   		 Or(p1,p2) -> (

  																if ((equals gamma3' gamma)) then (

  																	if (equals gamma2' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r3 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)

  																	) else false)

  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r3 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)


  																		) else false)
  																		else false

  																	)				
  																)
  																
  																else false

                	                			  	   		 )

                	                			  	   	   | _ -> false

                	                			  	   )
                	                			  	)

                	                			    else (


                	                			    	match p'' with 

                	                			    		Or(p1,p2) -> (

                	                			    			match r3 with 

                	                			    			E -> false
                	                			    		 | Root(p1'',_,_,_,gamma3',_) -> (

                	                			    		 	if ((p1''=p) && ( equals gamma2' gamma)) then (

                	                			    		 		if (equals gamma3' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r2 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)


                	                			    		 		) else false)
  																	else (
  																		if (equals gamma3' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r2 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)


  																		) else false)
  																		else false

  																	)
                	                			    		 	)


                	                			    		    else false
                	                			    		 )

                	                			    		)

                	                			    	| _ -> false	

                	                			    )

                	                			  )

                	                			)

                	                		    else(

                	                		    	match p' with 

                	                		    	 Or(p1,p2) -> (

                	                		    	 	match r2 with 

                	                		    	 	 E -> false
                	                		    	    | Root(p'',_,_,_,gamma2',_) -> (

                	                		    	    	match r3 with 

                	                		    	    	 E -> false
                	                		    	      | Root(p1'',_,_,_,gamma3',_) -> (

                	                		    	      	if ((p''=p) && (p1'' = p) && (equals gamma1' gamma)) then (

                	                		    	      		if (equals gamma2' (add p1 gamma)) then (if (equals gamma3' (add p2 gamma)) then (

  																		match r1 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)


                	                		    	      		) else false)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma3' (add p1 gamma)) then (

  																		match r1 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))		
  																	 						)


  																		) else false)
  																		else false

  																	)

                	                		    	      	)

                	                		    	      	else false

                	                		    	      )
                	                		    	    	
                	                		    	    )

                	                		    	 )

                	                		    	| _ -> false

                	                		    ) 

                	                		)

                	                	  | E -> false

            	)

                else ((has_rpair r1) || (has_rpair r2) || (has_rpair r3))

            )

        )


    )


)

(* A complicated function that checks if the input corresponds to an r-pair or not *)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let rec is_rpair root = match root with 

  E -> false
| Root(p,r1,r2,r3,gamma,s) -> (

	if(s="/\\-EL") then (

		let r' = (retAndEL p r1 r2 r3 gamma) in (

			match r' with 

			E -> false
		  | Root(p',r1',r2',r3',gamma',s') -> (

		  	 if (s'="/\\-I") then (

		  	 	true

		  	 )

		  	else false

		  )

		)

	)
 
    else(

    	if (s="/\\-ER") then (

    		let r' = (retAndER p r1 r2 r3 gamma) in (

				match r' with 

				E -> false
			  | Root(p',r1',r2',r3',gamma',s') -> (

			  	 if (s'="/\\-I") then (

			  	 	true

			  	 )

			  	else false


			  )

			)



    	)

        else(


        	if (s="->-E") then (



                	    match r1 with 

                	     E -> (

                	              match r2 with
                       		 	 E -> false
                     		   | Root(p'',_,_,_,gamma2',_) -> (

                       		   		match r3 with
                     		   		  E -> false
                  		   			| Root(p1'',_,_,_,gamma3',_) -> (

                        		   			match p'' with 


   	                        		   			Impl(p1,p2) -> (

  	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

  	                        		   					match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false


  	                        		   				) else (

          	                        		   					match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (
                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

                	                        		   		  						match r3 with 

								  	                        		   					E -> false
								  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false
									


                	                        		   		  			) else false
                	                        		   		  		)

                	                        		   		  	  | _ -> false

               	                        		   		)

	                        		   			)

   	                        		   		  | _ -> (

   	                        		   		  		match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

   	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

   	                        		   		  						match r3 with 

			  	                        		   					E -> false
			  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false



   	                        		   		  			) else false
	                        		   		  		)

                	                        		| _ -> false

	                        				  )

    	             		   		   )

	              		           )

                	        )

                 	   | Root(p',_,_,_,gamma1',_) -> (


                       	   		match r2 with 

                     	   		 E -> (

                      	   		 	match r3 with 

                      	   		 	 E -> false
                      	   		  | Root(p1'',_,_,_,gamma3',_) -> (

                        	   		  		match p' with 


	                       		   			Impl(p1,p2) -> (

		                   		   				if ((p2=p) && (p1 = p1'') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

		                   		   							match r1 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false


		                   		   				) else (

                        		   					match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false


  	                        		   		  			) else false
   	                        		   		  		)

   	                        		   		  		| _ -> false


                        		   				)

                	                        )

                        		   		  | _ -> (

                        		   		  		match p1'' with 

  	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else false


  	                        		   		  			) else false
   	                        		   		  		)

                        		   		  	  | _ -> false

	                       		   		  )


	                       	   		  )
                       	   		 )


                       	   	  | Root(p'',_,_,_,gamma2',_) -> (

		                 	   	  	if (r3=E) then (

 	                        	   	  		match p' with 

   	                        		   			Impl(p1,p2) -> (

 	                        		   				if ((p2=p) && (p1 = p'') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

 	                        		   							match r1 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))


 	                        		   				) else (

     	                        		   					match p'' with 

	       	                        		   		  		Impl(p1,p2) -> (

	       	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

	       	                        		   		  						match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))


	       	                        		   		  			) else false
	         	                        		   		  		)

		      	                        		   		  	  | _ -> false


              	                        		   	 )

                	                   			)

    	                        		   		  | _ -> (

      	                        		   		  		match p'' with 

        	                        		   		  		Impl(p1,p2) -> (

          	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

          	                        		   		  						match r2 with 

  	                        		   					E -> false
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then true else ((has_rpair r1) || (has_rpair r2))



          	                        		   		  			) else false
           	                        		   		  		)

            	                        		   		  	  | _ -> false

             	                        		   		)


                	                 ) else false

                     	   	  )
               	                        	   	  	 

                	     )

        	)


        	

            else(

            	if (s="\\/-E") then (

									match r1 with 

                	                		Root(p',_,_,_,gamma1',_) -> (

                	                			if (p'=p) then (

                	                				match r2 with 

                	                				 E -> false
                	                			  | Root(p'',_,_,_,gamma2',_) -> (

                	                			  	if ((p''=p)) then (

                	                			  		match r3 with

                	                			  		 E -> false
                	                			  	   | Root(p1'',_,_,_,gamma3',_) -> (

                	                			  	   		match p1'' with 

                	                			  	   		 Or(p1,p2) -> (

  																if ((equals gamma3' gamma)) then (

  																	if (equals gamma2' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r3 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)

  																	) else false)

  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r3 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)


  																		) else false)
  																		else false

  																	)				
  																)
  																
  																else false

                	                			  	   		 )

                	                			  	   	   | _ -> false

                	                			  	   )
                	                			  	)

                	                			    else (


                	                			    	match p'' with 

                	                			    		Or(p1,p2) -> (

                	                			    			match r3 with 

                	                			    			E -> false
                	                			    		 | Root(p1'',_,_,_,gamma3',_) -> (

                	                			    		 	if ((p1''=p) && ( equals gamma2' gamma)) then (

                	                			    		 		if (equals gamma3' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r2 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)


                	                			    		 		) else false)
  																	else (
  																		if (equals gamma3' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r2 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)


  																		) else false)
  																		else false

  																	)
                	                			    		 	)


                	                			    		    else false
                	                			    		 )

                	                			    		)

                	                			    	| _ -> false	

                	                			    )

                	                			  )

                	                			)

                	                		    else(

                	                		    	match p' with 

                	                		    	 Or(p1,p2) -> (

                	                		    	 	match r2 with 

                	                		    	 	 E -> false
                	                		    	    | Root(p'',_,_,_,gamma2',_) -> (

                	                		    	    	match r3 with 

                	                		    	    	 E -> false
                	                		    	      | Root(p1'',_,_,_,gamma3',_) -> (

                	                		    	      	if ((p''=p) && (p1'' = p) && (equals gamma1' gamma)) then (

                	                		    	      		if (equals gamma2' (add p1 gamma)) then (if (equals gamma3' (add p2 gamma)) then (

  																		match r1 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)


                	                		    	      		) else false)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma3' (add p1 gamma)) then (

  																		match r1 with 

  																		E -> false
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then true 
  																	 						else (

  																	 							if (s'="\\/-IR") then true
  																	 							else false
  																	 						)


  																		) else false)
  																		else false

  																	)

                	                		    	      	)

                	                		    	      	else false

                	                		    	      )
                	                		    	    	
                	                		    	    )

                	                		    	 )

                	                		    	| _ -> false

                	                		    ) 

                	                		)

                	                	  | E -> false


            	)

                else false

            )

        )


    )


)

(* A complicated recursive function that finds r-pair for the corresponding ND-proof tree *)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let rec ffind_rpair root = if (has_rpair root) then (

	match root with 

	E -> E
| Root(p,r1,r2,r3,gamma,s) -> (

	if(s="/\\-EL") then (

		let r' = (retAndEL p r1 r2 r3 gamma) in (

			match r' with 

			E -> E
		  | Root(p',r1',r2',r3',gamma',s') -> (

		  	 if (s'="/\\-I") then (

		  	 	root

		  	 )

		  	else (ffind_rpair r')


		  )

		)

	)
 
    else(

    	if (s="/\\-ER") then (

    		let r' = (retAndEL p r1 r2 r3 gamma) in (

				match r' with 

				E -> E
			  | Root(p',r1',r2',r3',gamma',s') -> (

			  	 if (s'="/\\-I") then (

			  	 	root

			  	 )

			  	else (ffind_rpair r')


			  )

			)



    	)

        else(


        	if (s="->-E") then (



                	    match r1 with 

                	     E -> (

                	              match r2 with
                       		 	 E -> E
                     		   | Root(p'',_,_,_,gamma2',_) -> (

                       		   		match r3 with
                     		   		  E -> E
                  		   			| Root(p1'',_,_,_,gamma3',_) -> (

                        		   			match p'' with 


   	                        		   			Impl(p1,p2) -> (

  	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

  	                        		   					match r2 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) (ffind_rpair r2) E)


  	                        		   				) else (

          	                        		   					match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (
                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

                	                        		   		  						match r3 with 

								  	                        		   					E -> E
								  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) (ffind_rpair r2) E)
									


                	                        		   		  			) else E
                	                        		   		  		)

                	                        		   		  	  | _ -> E

               	                        		   		)

	                        		   			)

   	                        		   		  | _ -> (

   	                        		   		  		match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

   	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

   	                        		   		  						match r3 with 

			  	                        		   					E -> E
			  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) E (ffind_rpair r2))



   	                        		   		  			) else E
	                        		   		  		)

                	                        		| _ -> E

	                        				  )

    	             		   		   )

	              		           )

                	        )

                 	   | Root(p',_,_,_,gamma1',_) -> (


                       	   		match r2 with 

                     	   		 E -> (

                      	   		 	match r3 with 

                      	   		 	 E -> E
                      	   		  | Root(p1'',_,_,_,gamma3',_) -> (

                        	   		  		match p' with 


	                       		   			Impl(p1,p2) -> (

		                   		   				if ((p2=p) && (p1 = p1'') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

		                   		   							match r1 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) (ffind_rpair r1) E)

		                   		   				) else (

                        		   					match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) (ffind_rpair r1) E)


  	                        		   		  			) else E
   	                        		   		  		)

   	                        		   		  		| _ -> E


                        		   				)

                	                        )

                        		   		  | _ -> (

                        		   		  		match p1'' with 

  	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r3) (ffind_rpair r1) E)


  	                        		   		  			) else E
   	                        		   		  		)

                        		   		  	  | _ -> E

	                       		   		  )


	                       	   		  )
                       	   		 )


                       	   	  | Root(p'',_,_,_,gamma2',_) -> (

		                 	   	  	if (r3=E) then (

 	                        	   	  		match p' with 

   	                        		   			Impl(p1,p2) -> (

 	                        		   				if ((p2=p) && (p1 = p'') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

 	                        		   							match r1 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r1) (ffind_rpair r2) E)


 	                        		   				) else (

     	                        		   					match p'' with 

	       	                        		   		  		Impl(p1,p2) -> (

	       	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

	       	                        		   		  						match r2 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else ( getVal (ffind_rpair r1) (ffind_rpair r2) E)


	       	                        		   		  			) else E
	         	                        		   		  		)

		      	                        		   		  	  | _ -> E

              	                        		   	 )

                	                   			)

    	                        		   		  | _ -> (

      	                        		   		  		match p'' with 

        	                        		   		  		Impl(p1,p2) -> (

          	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

          	                        		   		  						match r2 with 

  	                        		   					E -> E
  	                        		   				 | Root(_,_,_,_,_,s') -> if (s'="->-I") then root else (getVal (ffind_rpair r1) (ffind_rpair r2) E)



          	                        		   		  			) else E
           	                        		   		  		)

            	                        		   		  	  | _ -> E

             	                        		   		)


                	                 ) else E

                     	   	  )
               	                        	   	  	 

                	     )

        	)


        	

            else(

            	if (s="\\/-E") then (

									match r1 with 

                	                		Root(p',_,_,_,gamma1',_) -> (

                	                			if (p'=p) then (

                	                				match r2 with 

                	                				 E -> E
                	                			  | Root(p'',_,_,_,gamma2',_) -> (

                	                			  	if ((p''=p)) then (

                	                			  		match r3 with

                	                			  		 E -> E
                	                			  	   | Root(p1'',_,_,_,gamma3',_) -> (

                	                			  	   		match p1'' with 

                	                			  	   		 Or(p1,p2) -> (

  																if ((equals gamma3' gamma)) then (

  																	if (equals gamma2' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r3 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root 
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1) (ffind_rpair r2) (ffind_rpair r3))		
  																	 						)

  																	) else E)

  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r3 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))		
  																	 						)


  																		) else E)
  																		else E

  																	)				
  																)
  																
  																else E

                	                			  	   		 )

                	                			  	   	   | _ -> E

                	                			  	   )
                	                			  	)

                	                			    else (


                	                			    	match p'' with 

                	                			    		Or(p1,p2) -> (

                	                			    			match r3 with 

                	                			    			E -> E
                	                			    		 | Root(p1'',_,_,_,gamma3',_) -> (

                	                			    		 	if ((p1''=p) && ( equals gamma2' gamma)) then (

                	                			    		 		if (equals gamma3' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r2 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root 
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))		
  																	 						)


                	                			    		 		) else E)
  																	else (
  																		if (equals gamma3' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r2 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))		
  																	 						)


  																		) else E)
  																		else E

  																	)
                	                			    		 	)


                	                			    		    else E
                	                			    		 )

                	                			    		)

                	                			    	| _ -> E

                	                			    )

                	                			  )

                	                			)

                	                		    else(

                	                		    	match p' with 

                	                		    	 Or(p1,p2) -> (

                	                		    	 	match r2 with 


                	                		    	 	 E -> E
                	                		    	    | Root(p'',_,_,_,gamma2',_) -> (

                	                		    	    	match r3 with 

                	                		    	    	 E -> E
                	                		    	      | Root(p1'',_,_,_,gamma3',_) -> (

                	                		    	      	if ((p''=p) && (p1'' = p) && (equals gamma1' gamma)) then (

                	                		    	      		if (equals gamma2' (add p1 gamma)) then (if (equals gamma3' (add p2 gamma)) then (

  																		match r1 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))		
  																	 						)


                	                		    	      		) else E)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma3' (add p1 gamma)) then (

  																		match r1 with 

  																		E -> E
  																	 | Root(_,_,_,_,_,s') -> if (s' = "\\/-IL") then root
  																	 						else (

  																	 							if (s'="\\/-IR") then root
  																	 							else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))	
  																	 						)


  																		) else E)
  																		else E

  																	)

                	                		    	      	)

                	                		    	      	else E

                	                		    	      )
                	                		    	    	
                	                		    	    )

                	                		    	 )

                	                		    	| _ -> E

                	                		    ) 

                	                		)

                	                	  | E -> E


            	)

                else (getVal (ffind_rpair r1)  (ffind_rpair r2)  (ffind_rpair r3))

            )

        )


    )


	)



) else E

(* The main find_pair function that gets called along with the feature of exceptions*)
let find_rpair root = if ((ffind_rpair root) = E) then raise (Myexp "Normalized") else (ffind_rpair root)

let rec findLeavesTemp root gamma p = match root with 

  E -> [[]]

| Root(p',p1,p2,p3,gamma',s) ->(	

				match s with 

					"Hyp" -> if (p'=p) then (let delta = (deletion gamma' gamma) in [delta]) else [[]]
				  | "T-I" -> [[]]
				  | _ -> ((findLeavesTemp p1 gamma p) @ (findLeavesTemp p2 gamma p)) @ (findLeavesTemp p3 gamma p)	  		
				
				)


let findLeaves root p= match root with

			 E -> []
			| Root(p',p1,p2,p3,gamma,s) -> (

				(findLeavesTemp root gamma p) 			  	   

			)

let rec pad_arr root l = match l with 

   [] -> []
 | x :: xs -> (pad root x) :: (pad_arr root xs)

let findSimple pi1 pi2 = match pi2 with 

    Root(p,_,_,_,gamma,_) -> (

    	let delta_arr = (findLeaves pi1 p) in (

    		let proof_arr = (pad_arr pi2 delta_arr) in (graft pi1 proof_arr)

    	)

    )

(* Simplifying the Implication axioms*)
let simplifyImlp r1 r2 r3 gamma p =    match r1 with 

                	     E -> (

                	              match r2 with
                       		 	 E -> E
                     		   | Root(p'',_,_,_,gamma2',_) -> (

                       		   		match r3 with
                     		   		  E -> E
                  		   			| Root(p1'',_,_,_,gamma3',_) -> (

                        		   			match p'' with 


   	                        		   			Impl(p1,p2) -> (

  	                        		   				if ((p2=p) && (p1 = p1'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

  	                        		   					match r2 with 

  	                        		   					
										                 Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r3) else (findSimple r2' r3) 

										                                             ) else (findSimple r1' r3)
	


  	                        		   				) else (

          	                        		   					match p1'' with 

                	                        		   		  		Impl(p1,p2) -> (
                	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

                	                        		   		  						match r3 with 

                	                        		   		  						    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r2) else (findSimple r2' r2) 

										                                             ) else (findSimple r1' r2)
	
									


                	                        		   		  			) else E
                	                        		   		  		)

                	                        		   		  	  | _ -> E

               	                        		   		)

	                        		   			)

   	                        		   		  | _ -> (

   	                        		   		  		match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

   	                        		   		  			if ((p2=p) && (p1 = p'') && (equals gamma2' gamma) && (equals gamma3' gamma) ) then (

   	                        		   		  						match r3 with 

			  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r2) else (findSimple r2' r2) 

										                                             ) else (findSimple r1' r2)
	


   	                        		   		  			) else E
	                        		   		  		)

                	                        		| _ -> E

	                        				  )

    	             		   		   )

	              		           )

                	        )

                 	   | Root(p',_,_,_,gamma1',_) -> (


                       	   		match r2 with 

                     	   		 E -> (

                      	   		 	match r3 with 

                      	   		 	 E -> E
                      	   		  | Root(p1'',_,_,_,gamma3',_) -> (

                        	   		  		match p' with 


	                       		   			Impl(p1,p2) -> (

		                   		   				if ((p2=p) && (p1 = p1'') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

		                   		   							match r1 with 

  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r3) else (findSimple r2' r3) 

										                                             ) else (findSimple r1' r3)
	
		                   		   				) else (

                        		   					match p1'' with 

   	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   			    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r1) else (findSimple r2' r1) 

										                                             ) else (findSimple r1' r1)
	

  	                        		   		  			) else E
   	                        		   		  		)

   	                        		   		  		| _ -> E


                        		   				)

                	                        )

                        		   		  | _ -> (

                        		   		  		match p1'' with 

  	                        		   		  		Impl(p1,p2) -> (

  	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && (equals gamma3' gamma) ) then (

  	                        		   		  						match r3 with 

  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r1) else (findSimple r2' r1) 

										                                             ) else (findSimple r1' r1)
	

  	                        		   		  			) else E
   	                        		   		  		)

                        		   		  	  | _ -> E

	                       		   		  )


	                       	   		  )
                       	   		 )


                       	   	  | Root(p'',_,_,_,gamma2',_) -> (

		                 	   	  	if (r3=E) then (

 	                        	   	  		match p' with 

   	                        		   			Impl(p1,p2) -> (

 	                        		   				if ((p2=p) && (p1 = p'') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

 	                        		   							match r1 with 

  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r2) else (findSimple r2' r2) 

										                                             ) else (findSimple r1' r2)
	

 	                        		   				) else (

     	                        		   					match p'' with 

	       	                        		   		  		Impl(p1,p2) -> (

	       	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

	       	                        		   		  						match r2 with 

  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r1) else (findSimple r2' r1) 

										                                             ) else (findSimple r1' r1)
	

	       	                        		   		  			) else E
	         	                        		   		  		)

		      	                        		   		  	  | _ -> E

              	                        		   	 )

                	                   			)

    	                        		   		  | _ -> (

      	                        		   		  		match p'' with 

        	                        		   		  		Impl(p1,p2) -> (

          	                        		   		  			if ((p2=p) && (p1 = p') && (equals gamma1' gamma) && ( equals gamma2' gamma) ) then (

          	                        		   		  						match r2 with 

  	                        		   				    Root(_,r1',r2',r3',_,s') -> if (r1'=E) then (

										                                              if (r2'=E) then (findSimple r3' r1) else (findSimple r2' r1) 

										                                             ) else (findSimple r1' r1)
	


          	                        		   		  			) else E
           	                        		   		  		)

            	                        		   		  	  | _ -> E

             	                        		   		)


                	                 ) else E

                     	   	  )
               	                        	   	  	 

                	     )

(* Simplifying the OR axioms*)
let simplifyOr r1 r2 r3 gamma p = 	match r1 with 

                	                		Root(p',_,_,_,gamma1',_) -> (

                	                			if (p'=p) then (

                	                				match r2 with 

                	                				 E -> E
                	                			  | Root(p'',_,_,_,gamma2',_) -> (

                	                			  	if ((p''=p)) then (

                	                			  		match r3 with

                	                			  		 E -> E
                	                			  	   | Root(p1'',_,_,_,gamma3',_) -> (

                	                			  	   		match p1'' with 

                	                			  	   		 Or(p1,p2) -> (

  																if ((equals gamma3' gamma)) then (

  																	if (equals gamma2' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r3 with 

  																		
  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r3') else (findSimple r2 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r2') else (findSimple r2 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r1') else (findSimple r2 r1'))
  																	    )


  																	 )

  																	) else E)

  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r3 with 

  																		
  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r3') else (findSimple r2 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r2') else (findSimple r2 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r1') else (findSimple r2 r1'))
  																	    )


  																	 )	


  																		) else E)
  																		else E

  																	)				
  																)
  																
  																else E

                	                			  	   		 )

                	                			  	   	   | _ -> E

                	                			  	   )
                	                			  	)

                	                			    else (


                	                			    	match p'' with 

                	                			    		Or(p1,p2) -> (

                	                			    			match r3 with 

                	                			    			E -> E
                	                			    		 | Root(p1'',_,_,_,gamma3',_) -> (

                	                			    		 	if ((p1''=p) && ( equals gamma2' gamma)) then (

                	                			    		 		if (equals gamma3' (add p1 gamma)) then (if (equals gamma1' (add p2 gamma)) then (

  																		match r2 with 

  																
  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r3') else (findSimple r3 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r2') else (findSimple r3 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r1') else (findSimple r3 r1'))
  																	    )


  																	 )

                	                			    		 		) else E)
  																	else (
  																		if (equals gamma3' (add p2 gamma)) then (if (equals gamma1' (add p1 gamma)) then (

  																		match r2 with 

  																	
  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r3') else (findSimple r3 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r2') else (findSimple r3 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma1' (add a1 gamma)) then (findSimple r1 r1') else (findSimple r3 r1'))
  																	    )


  																	 )

  																		) else E)
  																		else E

  																	)
                	                			    		 	)


                	                			    		    else E
                	                			    		 )

                	                			    		)

                	                			    	| _ -> E

                	                			    )

                	                			  )

                	                			)

                	                		    else(

                	                		    	match p' with 

                	                		    	 Or(p1,p2) -> (

                	                		    	 	match r2 with 


                	                		    	 	 E -> E
                	                		    	    | Root(p'',_,_,_,gamma2',_) -> (

                	                		    	    	match r3 with 

                	                		    	    	 E -> E
                	                		    	      | Root(p1'',_,_,_,gamma3',_) -> (

                	                		    	      	if ((p''=p) && (p1'' = p) && (equals gamma1' gamma)) then (

                	                		    	      		if (equals gamma2' (add p1 gamma)) then (if (equals gamma3' (add p2 gamma)) then (

  																		match r1 with 

  																
  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r3') else (findSimple r3 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r2') else (findSimple r3 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r1') else (findSimple r3 r1'))
  																	    )


  																	 )

                	                		    	      		) else E)
  																	else (
  																		if (equals gamma2' (add p2 gamma)) then (if (equals gamma3' (add p1 gamma)) then (

  																		match r1 with 

  																		
  																	  Root(_,r1',r2',r3',_,s') -> (

  																	 	if(r1'=E) then (

  																	 		if(r2'=E) then (

  																	 	    	match r3' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r3') else (findSimple r3 r3'))


  																	 		)

  																	 	    else(

  																	 	    	match r2' with 

	  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r2') else (findSimple r3 r2'))


  																	 	    )

  																	 	)

  																	    else(

  																	    	match r1' with 

  																	    	Root(a1,_,_,_,_,_) -> (if (equals gamma2' (add a1 gamma)) then (findSimple r2 r1') else (findSimple r3 r1'))
  																	    )


  																	 )

  																		) else E)
  																		else E

  																	)

                	                		    	      	)

                	                		    	      	else E

                	                		    	      )
                	                		    	    	
                	                		    	    )

                	                		    	 )

                	                		    	| _ -> E

                	                		    ) 

                	                		)

                	                	  | E -> E

(* A complicated function that correct the improper ND tree with respect to the '->-I' axioms*)
(* To be called for the outputs of prune and graft because of their issues with the "->-I" case*)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let rec simplify root gamma'= match root with 

  E -> E 
 | Root(p,r1,r2,r3,gamma,s) -> (


 	if(member p gamma') then(

			Root(p,E,E,E,gamma',"Hyp")
		)
		
 	
	else(

		if(s="->-I") then (

 		match p with 


	 	Impl(p1,p2) ->	match r1 with 

	 		 E -> (

	 		 	match r2 with 

	 		 	 E -> (

	 		 	 	match r3 with 

	 		 	 	 Root(p',r1',r2',r3',gamma'',s') -> (

	 		 	 	 	let r' = Root(p',r1',r2',r3',(add p1 gamma''),s') in 

	 		 	 	 	 Root(p,E,E,(simplify r' (add p1 gamma'')),gamma',s)

	 		 	 	 )


	 		 	 )

 	 		 	 |	 Root(p',r1',r2',r3',gamma'',s') -> (

	 		 	 	 	let r' = Root(p',r1',r2',r3',(add p1 gamma''),s') in 

	 		 	 	 	 Root(p,E,(simplify r' (add p1 gamma'')),E,gamma',s)



	 		 		)

 			
 			)

	 		| 	Root(p',r1',r2',r3',gamma'',s') -> (

	 		 	 	 	let r' = Root(p',r1',r2',r3',(add p1 gamma''),s') in 

	 		 	 	 	 Root(p,(simplify r' (add p1 gamma'')),E,E,gamma',s)


		)

 
	)   


		else Root(p,(simplify r1 gamma'),(simplify r2 gamma'),(simplify r3 gamma'),gamma',s) 

	) 
)

(* A complicated function that simplifies the ND tree with respect to the '/\-EL', '/\-ER', '\/-E', and '->-E' axioms*)
(* Apart from checking for the rules, appropriate tree invariants are also taken into account*)
(* For example, if a node is a expanded to only two further nodes, then those two can be either the first and second child
	Or they can be the first and third child etc. for the tree (Remember the type definition for ND proof tree)
*)
let simplify2 root = match root with 

  Root(p,r1,r2,r3,gamma,s) -> (

  	if(s="/\\-EL") then (

		let r' = (retAndEL p r1 r2 r3 gamma) in (

			match r' with 

	
		   Root(p',r1',r2',r3',gamma',s') -> (

		   	match r1' with 

		   	 E -> (

		   	 	match r2' with 

		   	 	 Root(p1,_,_,_,_,_) -> if (p1=p) then r2' else r3'


		   	 )

		  | Root(p1,_,_,_,_,_) -> if(p1=p) then r1' else(

		  	match r2' with 

		  	 E -> r3'
          | _ -> r2'

		  )


		  	
		  )

		)

	)
 
    else(

    	if (s="/\\-ER") then (

			let r' = (retAndER p r1 r2 r3 gamma) in (

				match r' with 

		
			   Root(p',r1',r2',r3',gamma',s') -> (

			   	match r1' with 

			   	 E -> (

			   	 	match r2' with 

			   	 	 Root(p1,_,_,_,_,_) -> if (p1=p) then r2' else r3'


			   	 )

			  | Root(p1,_,_,_,_,_) -> if(p1=p) then r1' else(

			  	match r2' with 

			  	 E -> r3'
	          | _ -> r2'

			  )


			  	
			  )

			)
	    		

    	)

        else(


    
        	if (s="->-E") then (

  				(simplifyImlp r1 r2 r3 gamma p)

        	)

  
        	else (

        		if (s="\\/-E") then (

        			(simplifyOr r1 r2 r3 gamma p)

        		)

        	     else root

        	)

        )


    )



  )

(*A valid but "simpler" ND proof tree of the same consequent judgment*)
(* Combines the both the simplifications defined earlier*)
let simplify1 root = 

  let root1 = (simplify2 root) in (

  	match root1 with 

	 E -> raise (Myexp "Empty Tree")
  | Root(_,_,_,_,gamma,_) -> (simplify root1 gamma)


  )


let rec normalise1 root = if (is_rpair root) then (

	(normalise1 (simplify2 root))
)

else (

	match root with 

	 E -> E
 | Root(p,r1,r2,r3,gamma,s) -> Root(p,(normalise1 r1),(normalise1 r2),(normalise1 r3),gamma,s)


)

(*A completely "simplified" ND proof tree, with no r-pairs*)
let normalise root = 

	let root1 = (normalise1 root) in (

	  	match root1 with 

		 E -> raise (Myexp "Empty Tree")
	  | Root(_,_,_,_,gamma,_) -> (simplify root1 gamma)


	  )
	

(* 	TESTING FOR THE FUNCTIONS DEALING WITH R-PAIR REMOVAL

-> Defining the Propositions and the ND-proof tree:

	let a = L("a");;
	let b = L("b");;
	let c = L("c");;

	let r = c;;
	let s = Impl(a,Impl(b,a));;
	let p = s;;
	let q = Impl(s,p);;

	let root = Root(q,E,(Root(p,E,E,(Root(And(p,r),E,(Root(p,(Root(Or(s,p),E,E,(Root(s,E,E,(Root(Impl(b,a),E,E,(Root(a,E,E,E,[r;a;b],"Hyp")),[r;a],"->-I")),[r],"->-I")),[r],"\\/-IL")),(Root(p,E,E,E,[r;s],"Hyp")),(Root(p,E,E,E,[r;p],"Hyp")),[r],"\\/-E")),(Root(r,E,E,E,[r],"Hyp")),[r],"/\\-I")),[r],"/\\-EL")),(Root(Impl(p,q),E,E,(Root(q,E,E,(Root(p,E,E,E,[r;p;s],"Hyp")),[r;p],"->-I")),[r],"->-I")),[r],"->-E");;

	Root
	   (Impl (Impl (L "a", Impl (L "b", L "a")),
	     Impl (L "a", Impl (L "b", L "a"))),
	   E,
	   Root (Impl (L "a", Impl (L "b", L "a")), E, E,
	    Root (And (Impl (L "a", Impl (L "b", L "a")), L "c"), E,
	     Root (Impl (L "a", Impl (L "b", L "a")),
	      Root
	       (Or (Impl (L "a", Impl (L "b", L "a")),
	         Impl (L "a", Impl (L "b", L "a"))),
	       E, E,
	       Root (Impl (L "a", Impl (L "b", L "a")), E, E,
	        Root (Impl (L "b", L "a"), E, E,
	         Root (L "a", E, E, E, [L "c"; L "a"; L "b"], "Hyp"), [L "c"; L "a"],
	         "->-I"),
	        [L "c"], "->-I"),
	       [L "c"], "\\/-IL"),
	      Root (Impl (L "a", Impl (L "b", L "a")), E, E, E,
	       [L "c"; Impl (L "a", Impl (L "b", L "a"))], "Hyp"),
	      Root (Impl (L "a", Impl (L "b", L "a")), E, E, E,
	       [L "c"; Impl (L "a", Impl (L "b", L "a"))], "Hyp"),
	      [L "c"], "\\/-E"),
	     Root (L "c", E, E, E, [L "c"], "Hyp"), [L "c"], "/\\-I"),
	    [L "c"], "/\\-EL"),
	   Root
	    (Impl (Impl (L "a", Impl (L "b", L "a")),
	      Impl (Impl (L "a", Impl (L "b", L "a")),
	       Impl (L "a", Impl (L "b", L "a")))),
	    E, E,
	    Root
	     (Impl (Impl (L "a", Impl (L "b", L "a")),
	       Impl (L "a", Impl (L "b", L "a"))),
	     E, E,
	     Root (Impl (L "a", Impl (L "b", L "a")), E, E, E,
	      [L "c"; Impl (L "a", Impl (L "b", L "a"));
	       Impl (L "a", Impl (L "b", L "a"))],
	      "Hyp"),
	     [L "c"; Impl (L "a", Impl (L "b", L "a"))], "->-I"),
	    [L "c"], "->-I"),
	   [L "c"], "->-E")

-> On applying the find r-pair funciton, the program returns the same tree as the input one as expected

-> Also, I made a is_rpair function which returns true if a given Root is an R-pair root. I tested it for the various subtrees of the given input and the corresponding results were obtained correctly!

-> Also, I used the normalise functon and the simplify1 function on this given tree and checked it for the correctness of the Tree and the presence of any r-pairs or not. And the outputs came as expected

-> The final normalised tree of this given proof tree is:

	Root
	   (Impl (Impl (L "a", Impl (L "b", L "a")),
	     Impl (L "a", Impl (L "b", L "a"))),
	   E, E,
	   Root (Impl (L "a", Impl (L "b", L "a")), E, E, E,
	    [Impl (L "a", Impl (L "b", L "a")); L "c"], "Hyp"),
	   [L "c"], "->-I")

-> Another ND-tree on which the above system might be tested:
	let root = Root(L("q"),(Root(Impl(L("p"),L("q")),(Root(L("q"),(Root(F,E,E,E,[L("p");F],"Hyp")),E,E,[L("p");F],"~-Int")),(E),(E),[F],"->-I")),(Root(L("p"),(Root(F,E,E,E,[F],"Hyp")),E,E,[F],"~-Int")),(E),[F],"->-E");;

*)          		

                		