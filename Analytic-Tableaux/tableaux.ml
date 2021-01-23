(* Defining the Recursive type for the different types of propositions*)
type prop = T | F | L of string | Not of prop | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop

(* Defining a node for a proposition along with the boolean value it would have*)
type node = Null | Node of prop * bool 

(* Defining type for the Analytic Tableaux. 'E' is a leaf. 
	The first boolean value is True if the current node has been evaluated
	The second boolean value if True if the current node shows a contradiction. Marked as closed path.
*)
type tree = E | Root of node * bool * bool * tree * tree

(* Custom Exception*)
exception Myexp of string

(* Create a tree node *)
let mkroot n = Root(n,false,false,E,E)

(* Basic Helper functions *)
let rec isPresent s gamma = match gamma with 
						(x,b)::xs -> if x=s then true else (isPresent s xs)
						| [] -> false

let rec value s gamma = match gamma with 
						(x,b)::xs -> if x=s then b else (value s xs)
						| [] -> false

let insert a gamma = match gamma with
						x::xs  -> a :: gamma
						| [] -> [a]

let rec inDomain s l = match l with 
						[] -> false
						| (x,y)  :: xs -> if (x=s) then true else (inDomain s xs)

let rec find rho s = match rho with 
						(x,y) :: xs -> if (x=s) then y else (find xs s)
						| [] -> false

let rec member x l = match l with 
						[] -> false
						| y :: ys -> (if y=x then true else (member x ys))

let rec union l1 l2 = match l1 with 
						[] -> l2
						| x :: xs -> (
						    if (member x l2) then (union xs l2) else ([x] @ (union xs l2))
						)

(* Returns a list of the variables in the proposition p*)
let rec letters p = match p with
					T -> []
					| F -> []
					| L(s) -> [s]
					| Not(q) -> (letters q)
					| And(q1,q2) -> (union (letters q1) (letters q2))
					| Or(q1, q2) -> (union (letters q1) (letters q2))
					| Impl(q1, q2) -> (union (letters q1) (letters q2))
					| Iff(q1, q2) -> (union (letters q1) (letters q2))

(* Computes the truth value of the given proposition 'p' with regards to the assignments in 'rho' *)
let rec truth p rho = match p with 
					T -> true
					| F -> false
					| L(s) -> if (inDomain s rho) then (find rho s) else raise (Myexp "Not in domain")
					| Not(q) -> not (truth q rho)
					| And(q1,q2) -> if ((q1=F)||(q2=F)||(not(truth q1 rho))||(not(truth q2 rho))) then false else (truth q1 rho) && (truth q2 rho)
					| Or(q1, q2) -> if ((q1=T)||(q2=T)||((truth q1 rho))||((truth q2 rho))) then true else (truth q1 rho) || (truth q2 rho)
					| Impl(q1, q2) -> if (truth q1 rho) then (truth q2 rho) else true
					| Iff(q1, q2) -> if ((truth q1 rho)=(truth q2 rho)) then true else false

(* Create the complete analytic Tableaux for the node 'n'. 'gamma' here is the initial store for the variable assignments and should be Empty ideally*)
let rec makeAna n gamma= 

	(* A temporary function that acts as a map*)
	let rec makeAnalist l gamma = 
		(match l with

				n :: xs -> if xs=[] then (

                            (makeAna n gamma)

                        ) else(

	                        match  n with
	                            Node(T,true) -> Root(n,true,false,(makeAnalist xs gamma),E)
	                          | Node(F,false) -> Root(n,true,false,(makeAnalist xs gamma),E)
	                          | Node(T,false) -> Root(n,true,true,E,E)
	                          | Node(F, true) -> Root(n,true,true,E,E)
	                          | Node(L(s),b) -> if (isPresent s gamma) then (if (b=(value s gamma)) then (Root(n,true,false,(makeAnalist xs gamma),E)) else (Root(n,true,true,E,E))) else (Root(n,true,false,(makeAnalist xs (insert (s,b) gamma)),E)) 
	                          | Node(Not(p1),b) -> Root(n,true,false,(makeAnalist (Node(p1, (not b))::xs) gamma),E)
	                          | Node(And(p1,p2),false) -> Root(n,true,false,(makeAnalist (Node(p1,false)::xs) gamma),(makeAnalist (Node(p2,false)::xs) gamma))
	                          | Node(Or(p1,p2),true) -> Root(n,true,false,(makeAnalist (Node(p1,true)::xs) gamma),(makeAnalist (Node(p2,true)::xs) gamma))
	                          | Node(Impl(p1,p2),true) -> Root(n,true,false,(makeAnalist (Node(p1,false)::xs) gamma),(makeAnalist (Node(p2,true)::xs) gamma))
	                          | Node(And(p1,p2),true) -> Root(n,true,false,(makeAnalist ([Node(p1,true);Node(p2,true)]@ xs) gamma),E)
	                          | Node(Or(p1,p2),false) -> Root(n,true,false,(makeAnalist ([Node(p1,false);Node(p2,false)] @  xs) gamma),E)
	                          | Node(Impl(p1,p2),false) -> Root(n,true,false,(makeAnalist ([Node(p1,true);Node(p2,false)] @ xs) gamma),E)
	                          | Node(Iff(p1,p2),false) -> Root(n,true,false,(makeAnalist ([Node(p1,false);Node(p2,true)] @ xs) gamma),(makeAnalist ([Node(p1,true);Node(p2,false)] @ xs) gamma))
	                          | Node(Iff(p1,p2),true) -> Root(n,true,false,(makeAnalist ([Node(p1,false);Node(p2,false)] @ xs) gamma),(makeAnalist ([Node(p1,true);Node(p2,true)] @ xs) gamma))                


                        )
		)


	in (match n with
      
                    Node(T,true) -> Root(n,true,false,E,E)
                  | Node(F,false) -> Root(n,true,false,E,E)
                  | Node(T,false) -> Root(n,true,true,E,E)
                  | Node(F, true) -> Root(n,true,true,E,E)
                  | Node(L(s),b) -> if (isPresent s gamma) then (if (b=(value s gamma)) then (Root(n,true,false,E,E)) else (Root(n,true,true,E,E))) else (Root(n,true,false,E,E)) 
                  | Node(Not(p1),b) -> Root(n,true,false,(makeAna (Node(p1,(not b))) gamma),E)
                  | Node(And(p1,p2),false) -> Root(n,true,false,(makeAna (Node(p1,false)) gamma),(makeAna (Node(p2,false)) gamma))
                  | Node(Or(p1,p2),true) -> Root(n,true,false,(makeAna (Node(p1,true)) gamma),(makeAna (Node(p2,true)) gamma))
                  | Node(Impl(p1,p2),true) -> Root(n,true,false,(makeAna (Node(p1,false)) gamma),(makeAna (Node(p2,true)) gamma))
                  | Node(And(p1,p2),true) -> Root(n,true,false,(makeAnalist [Node(p1,true);Node(p2,true)] gamma),E)
                  | Node(Or(p1,p2),false) -> Root(n,true,false,(makeAnalist [Node(p1,false);Node(p2,false)] gamma),E)
                  | Node(Impl(p1,p2),false) -> Root(n,true,false,(makeAnalist [Node(p1,true);Node(p2,false)] gamma),E)
                  | Node(Iff(p1,p2),false) -> Root(n,true,false,(makeAnalist ([Node(p1,false);Node(p2,true)]) gamma),(makeAnalist ([Node(p1,true);Node(p2,false)]) gamma))
                  | Node(Iff(p1,p2),true) -> Root(n,true,false,(makeAnalist ([Node(p1,false);Node(p2,false)]) gamma),(makeAnalist ([Node(p1,true);Node(p2,true)]) gamma))                
	)
     
(* Given the Input tree, a partially built tableaux, returns the node which has contradiction and marks it closed*)
let rec contrad_path root gamma= 
  match root with
      
                    E -> E
                  | Root(Node(T,true),a,b,x,y) -> Root(Node(T,true),a,b,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(F,false),a,b,x,y) -> Root(Node(F,false),a,b,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(T,false),_,_,x,y) -> Root(Node(T,false),true,true,E,E);  
                  | Root(Node(F,true),_,_,x,y) -> Root(Node(F,true),true,true,E,E);  
                  | Root(Node(L(s),b),a,c,x,y) -> if (isPresent s gamma) then (if (b=(value s gamma)) then (Root(Node(L(s),b),a,c,(contrad_path x gamma),(contrad_path y gamma))) else ( Root(Node(L(s),b),true,true,E,E))) else (Root(Node(L(s),b),a,c,(contrad_path x (insert (s,b) gamma)),(contrad_path y (insert (s,b) gamma)))) 
                  | Root(Node(Not(p1),b),a,c,x,y) -> Root(Node(Not(p1),b),a,c,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(And(p1,p2),b),a,c,x,y) -> Root(Node(And(p1,p2),b),a,c,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(Or(p1,p2),b),a,c,x,y) -> Root(Node(Or(p1,p2),b),a,c,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(Impl(p1,p2),b),a,c,x,y) -> Root(Node(Impl(p1,p2),b),a,c,(contrad_path x gamma),(contrad_path y gamma))
                  | Root(Node(Iff(p1,p2),b),a,c,x,y) -> Root(Node(Iff(p1,p2),b),a,c,(contrad_path x gamma),(contrad_path y gamma))

(* Given the input tree, a fully or partially-built tableaux, checks it if is valid*)
(* A recursive function that checks this for all the possible propositions with both the possible values*)
let rec valid_tableau root gamma = 
    match root with 
             E -> true
           | Root(Node(T,true),a,b,x,y) -> (if ((a=true) && (b=false) ) then ((valid_tableau x gamma) && (valid_tableau y gamma)) else (if (a=false) then true else false))
           | Root(Node(F,false),a,b,x,y) -> (if ((a=true) && (b=false) ) then ((valid_tableau x gamma) && (valid_tableau y gamma)) else (if (a=false) then true else false))
           | Root(Node(T,false),a,b,x,y) -> (if ((a=true) && (b=true) && (x=E) && (y=E)) then true else (if (a=false) then true else false))
           | Root(Node(F,true),a,b,x,y) -> (if ((a=true) && (b=true) && (x=E) && (y=E)) then true else (if (a=false) then true else false))
           | Root(Node(L(s),b),a,c,x,y) -> if (isPresent s gamma) then (if (b=(value s gamma)) then (if ((a=true)&&(c=false)) then ((valid_tableau x gamma) && (valid_tableau y gamma)) else ((if (a=false) then true else false))) else (if ((a=true) && (c=true) && (x=E) && (y=E)) then true else (if (a=false) then true else false)))  
                                            else (if((a=true)&&(c=false)) then ((valid_tableau x (insert (s,b) gamma))&&(valid_tableau y (insert (s,b) gamma))) else (if (a=false) then true else false))
           | Root(Node(Not(p1),b),a,c,x,y) -> (if ((a=true)&(c=false)) then (

                match x with 

	                Root(Node(p2,(b1)),q,w,n,m) -> (if ((p1=p2) && (b = (not b1)) && (q=true) && (w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau y gamma)) else (if ((p1=p2) && (b = (not b1)) && (q=false)) then true else false))
		        	| _ -> (

		                match y with 

		                   Root(Node(p2,(b2)),q,w,n,m) -> (if ((p1=p2) && (b = (not b2)) && (q=true) && (w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau x gamma)) else (if ((p1=p2) && (b = (not b2)) && (q=false)) then true else false))
		                  | _ -> false


              		)

            ) else (if (a=false) then true else false))

           | Root(Node(And(p1,p2),true),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

	                Root(Node(p3,true),q,w,n,m) -> if (((p2 = p3) || (p1=p3))&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau y gamma)) else (if (((p2 = p3) || (p1=p3))&&(q=false)) then true else false)
	              	| _ -> (

		                match y with 

		                    Root(Node(p3,true),q,w,n,m) -> if (((p2 = p3) || (p1=p3))&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau x gamma)) else (if (((p2 = p3) || (p1=p3))&&(q=false)) then true else false)
		                    | _ -> false
		            )

            ) else ((if (a=false) then true else false))

           | Root(Node(Or(p1,p2),false),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

		            Root(Node(p3,false),q,w,n,m) -> if (((p2 = p3) || (p1=p3))&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau y gamma)) else (if (((p2 = p3) || (p1=p3))&&(q=false)) then true else false)
		            | _ -> (

		                match y with 

		                    Root(Node(p3,false),q,w,n,m) -> if (((p2 = p3) || (p1=p3))&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau x gamma)) else (if (((p2 = p3) || (p1=p3))&&(q=false)) then true else false)
		                    | _ -> false

            		)

            ) else ((if (a=false) then true else false))

         | Root(Node(Impl(p1,p2),false),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                Root(Node(p3,true),q,w,n,m) -> if ( (p1=p3)&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau y gamma)) else (if ( (p1=p3)&&(q=false)) then true else false)
              | Root(Node(p3,false),q,w,n,m) -> if ( (p2=p3)&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau y gamma)) else (if ( (p2=p3)&&(q=false)) then true else false)
              | _ -> (

                match y with 

                        Root(Node(p3,true),q,w,n,m) -> if ((p1=p3)&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau x gamma)) else (if ( (p1=p3)&&(q=false)) then true else false)
                      |   Root(Node(p3,false),q,w,n,m) -> if ((p2=p3)&&(q=true)&&(w=false)) then (((valid_tableau n gamma) && (valid_tableau m gamma)) && (valid_tableau x gamma)) else (if ( (p2=p3)&&(q=false)) then true else false)
                      | _ -> false

              )


             ) else ((if (a=false) then true else false))
    
        |  Root(Node(And(p1,p2),false),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                  Root(Node(p3,false),q,w,n,m) -> if ((p1=p3) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p4,false),q1,w1,n1,m1) -> if ((p2=p4) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p2=p4) &&(q1=false)) then true else false)

                    | _ -> false

                  ) else (

                    if ((p1=p3) &&(q=false)) then true else false


                  )


                |  Root(Node(p5,false),q,w,n,m) -> if ((p2=p5) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p6,false),q1,w1,n1,m1) -> if ((p1=p6) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p1=p6) &&(q1=false)) then true else false)

                     | _ -> false

                  ) else (if ((p2=p5) &&(q=false)) then true else false)

              | _ -> false

            ) else (if (a=false) then true else false)

        | Root(Node(Or(p1,p2),true),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                  Root(Node(p3,true),q,w,n,m) -> if ((p1=p3) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p4,true),q1,w1,n1,m1) -> if ((p2=p4) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p2=p4) &&(q1=false)) then true else false)

                      | _ -> false

                  ) else (if ((p1=p3) &&(q=false)) then true else false)


                |  Root(Node(p5,true),q,w,n,m) -> if ((p2=p5) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p6,true),q1,w1,n1,m1) -> if ((p1=p6) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p1=p6) &&(q1=false)) then true else false)

                      | _ -> false

                  ) else (if ((p2=p5) &&(q=false)) then true else false)

              | _ -> false

            ) else (if (a=false) then true else false)

        | Root(Node(Impl(p1,p2),true),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                  Root(Node(p3,false),q,w,n,m) -> if ((p1=p3) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p4,true),q1,w1,n1,m1) -> if ((p2=p4) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p2=p4) &&(q1=false)) then true else false)

                      | _ -> false

                  ) else (if ((p1=p3) &&(q=false)) then true else false)


                |  Root(Node(p5,true),q,w,n,m) -> if ((p2=p5) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p6,false),q1,w1,n1,m1) -> if ((p1=p6) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if ((p1=p6) &&(q1=false)) then true else false)

                      | _ -> false

                  ) else (if ((p2=p5) &&(q=false)) then true else false)

              | _ -> false


          ) else (if (a=false) then true else false)


        | Root(Node(Iff(p1,p2),true),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                  Root(Node(p3,false),q,w,n,m) -> if (((p2=p3) || (p1=p3)) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p4,true),q1,w1,n1,m1) -> if (((p1 = p4) || (p2=p4)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p1=p4) || (p2=p4)) &&(q=false)) then true else false)

   
                    | _ -> false

                  ) else (if (((p2=p3) || (p1=p3)) &&(q=false)) then true else false) 


                |  Root(Node(p5,true),q,w,n,m) -> if (((p1=p5) || (p2=p5)) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p6,false),q1,w1,n1,m1) -> if (((p2=p6) || (p1=p6)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p2=p6) || (p1=p6)) &&(q=false)) then true else false)

                      | _ -> false

                  ) else (if (((p1=p5) || (p2=p5)) &&(q=false)) then true else false) 

              | _ -> false

            ) else (if (a=false) then true else false)

      | Root(Node(Iff(p1,p2),false),a,b,x,y) -> if ((a=true) && (b=false)) then (

                match x with 

                  Root(Node(p3,false),q,w,n,m) -> if (((p1=p3)) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p4,true),q1,w1,n1,m1) -> if (((p1 = p4)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p1 = p4)) &&(q1=false)) then true else false)

                    | Root(Node(p4,false),q1,w1,n1,m1) -> if (((p2 = p4)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p2 = p4)) &&(q1=false)) then true else false)


                    | _ -> false

                  ) else (


                      if (((p2=p3)) &&(q=true)&&(w=false)) then (

                       match y with 

                        Root(Node(p4,true),q1,w1,n1,m1) -> if (((p2 = p4)) &&(q1=true)&&(w1=false)) then (

                          ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                        ) else (if (((p2 = p4)) &&(q1=false)) then true else false)

                      | Root(Node(p4,false),q1,w1,n1,m1) -> if (((p1 = p4)) &&(q1=true)&&(w1=false)) then (

                          ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                        ) else (if (((p1 = p4)) &&(q1=false)) then true else false)


                      | _ -> false

                    )                       

                    else (if (((p2=p3)||(p1=p3))&& (q=false)) then true else false)

                  )


                |  Root(Node(p5,true),q,w,n,m) -> if (((p1=p5) ) &&(q=true)&&(w=false)) then (

                     match y with 

                      Root(Node(p6,false),q1,w1,n1,m1) -> if (((p1=p6)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p1 = p6)) &&(q1=false)) then true else false)

                      | Root(Node(p6,true),q1,w1,n1,m1) -> if (((p2=p6)) &&(q1=true)&&(w1=false)) then (

                        ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                      ) else (if (((p2 = p6)) &&(q1=false)) then true else false)

                      | _ -> false

                  ) else (

                      if (((p2=p5) ) &&(q=true)&&(w=false)) then (

                       match y with 

                        Root(Node(p6,false),q1,w1,n1,m1) -> if (((p2=p6)) &&(q1=true)&&(w1=false)) then (

                          ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                        ) else (if (((p2 = p6)) &&(q1=false)) then true else false)

                        | Root(Node(p6,true),q1,w1,n1,m1) -> if (((p1=p6)) &&(q1=true)&&(w1=false)) then (

                          ((valid_tableau n gamma) && (valid_tableau n1 gamma) && (valid_tableau m gamma) && (valid_tableau m1 gamma))

                        ) else (if (((p1 = p6)) &&(q1=false)) then true else false)

                        | _ -> false

                    ) 

                     else (if (((p2=p5)||(p1=p5))&& (q=false)) then true else false)

                  )

              | _ -> false

          
          )   else (if (a=false) then true else false)


let report_contradiction_change root = let root1 = (contrad_path root []) in (if (root1=root) then false else true)

(* Takes a partially built tableaux and selects an unvisited node for further Investigation*)
let rec select_node root = 
  match root with 

                     E -> Null
                  |  Root(n,a,b,x,y) -> (

                    if a=false then (

                      if b=false then (

                         n
                      )

                      else(

                        raise(Myexp "Is showing contraction without even visiting!")

                      )

                    )

                    else (

                      if b=true then (

                          Null
                      )

                      else(

                        let p = (select_node x) and q = (select_node y) in (

                          if p=Null then (

                             if q=Null then Null else q

                          )

                          else p 

                        )

                      )


                    )

                  )

(* Finds the path of an unvisited node in the given partially complete tree*)
let rec findpath root = let p = (select_node root) in (
  if p=Null then (raise(Myexp "No open paths"))
  else (

    match root with 

                     E -> []
                  |  Root(n,a,b,x,y) -> (

                    if a=false then (

                      if b=false then (

                         []
                      )

                      else(

                        raise(Myexp "Is showing contraction without even visiting!")

                      )

                    )

                    else (

                      if b=true then (

                          []
                      )

                      else(


                        match n with 

                        Node(L(s),b) -> (let p = (select_node x) and q = (select_node y) in (

                          if p=Null then (

                            (s,b) :: (findpath y)

                          )

                          else (s,b) :: (findpath x) ))

                      | _ -> 

                        (let p = (select_node x) and q = (select_node y) in (

                          if p=Null then (

                             (findpath y)

                          )

                          else (findpath x) ))

                        )

                      )


                    )

                  )



  )

(* Takes the node under examination and a partially built tableaux and outputs the fully completed subtree with that node as the root*)
let step_develop node root = let gamma = (findpath root) in (makeAna node gamma)

(* Checks if there is any closed path in the tree.*)
let rec checkAllclosed root = match root with 

      Root(n,a,b,x,y) -> (

        if b=true then(

            true

        )

        else (

          if x=E then(

            if y=E then(

              false

            )

            else(

              (checkAllclosed y)

            )


          )

         else(

            if y=E then(

                (checkAllclosed x)
            )

            else(


                (checkAllclosed x) && (checkAllclosed y)
            )

         )

        )


      )

(* Takes a fully built tableaux and outputs all the variable assignments that are satisfying it*)
let find_assignments root = 

	let rec setValues l p gamma b = (

	  match l with 

	    [] -> if ((truth p gamma)=b) then [gamma] else []
	  | x:: xs -> (

	    let p1 = (setValues xs p (insert (x,true) gamma) b) and 
	        p2 = (setValues xs p (insert (x,false) gamma) b) in p1 @ p2
	  )

	) in (

	  match root with

	   Root(Node(p,b),_,_,_,_) ->  (setValues (letters p) p [] b)
	   | _ -> []
	
	)

(* Represent the assignment list as a String*)
let rec mkstr l = match l with
	(x,y) :: xs -> (
	  if xs = [] then (x ^ " |-> " ^ (string_of_bool y))
		else (x ^ " |-> " ^ (string_of_bool y) ^ " ; " ^ (mkstr xs))
	)

	| _ -> ""


(* Checks if the given proposition is a Tautology. If not then returns a counter-example*)
let check_tautology p = let root = (makeAna (Node(p,false)) []) in (

  if (checkAllclosed root) then (root)
  
  else(

     let l = (find_assignments root) in (let q = (List.hd l) in ( let s = (mkstr q) in
      (raise(Myexp ("A counter example is " ^ s)))))
  )


)                 
  
(* Checks if the given proposition is a Contradiction. If not, then returns a counter-example*)
let check_contradiction p = let root = (makeAna (Node(p,true)) []) in (

  if (checkAllclosed root) then (root)
  
  else(

         let l = (find_assignments root) in (let q = (List.hd l) in ( let s = (mkstr q) in
	      (raise(Myexp ("A counter example is " ^ s)))))
  )

)                 




(* Test cases for checking, listed in order:

  let p = Impl(L("s"),L("a"));;
  let q = Impl(p,p);;
  let gamma = [];;

  let n = (Node(q,true));;
  let root1 = makeAna n gamma;;

     Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), true), true,
     false,
     Root (Node (Impl (L "s", L "a"), false), true, false,
      Root (Node (L "s", true), true, false,
       Root (Node (L "a", false), true, false, E, E), E),
      E),
     Root (Node (Impl (L "s", L "a"), true), true, false,
      Root (Node (L "s", false), true, false, E, E),
      Root (Node (L "a", true), true, false, E, E)))


  valid_tableau root1 gamma;;
  select_node root1;;
  find_assignments root1;;

  check_tautology p;;
  check_contradiction p;;

  step_develop (Node(Impl (L "s", L "a"), true)) root1;;

let root2 =  Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), true), true,
    false,
    Root (Node (Impl (L "s", L "a"), false), false, false,E,E),
    Root (Node (Impl (L "s", L "a"), true), false, false,
    E,E));;


  valid_tableau root2 gamma;;
  select_node root2;;
  find_assignments root2;;

  check_tautology q;;
  check_contradiction q;;

  step_develop (select_node root2) root2;;

  let n = (Node(q,false));;
  let root3 = makeAna n gamma;;
    val root3 : tree =
      Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), false), true,
       false,
       Root (Node (Impl (L "s", L "a"), true), true, false,
        Root (Node (L "s", false), true, false,
         Root (Node (Impl (L "s", L "a"), false), true, false,
          Root (Node (L "s", true), true, true, E, E), E),
         E),
        Root (Node (L "a", true), true, false,
         Root (Node (Impl (L "s", L "a"), false), true, false,
          Root (Node (L "s", true), true, false,
           Root (Node (L "a", false), true, true, E, E), E),
          E),
         E)),
       E)

  let root4 =       Root (Node (Impl (Impl (L "s", L "a"), Impl (L "s", L "a")), false), true,
         false,
         Root (Node (Impl (L "s", L "a"), true), true, false,
          Root (Node (L "s", false), true, false,
           Root (Node (Impl (L "s", L "a"), false), true, false,
            Root (Node (L "s", true), false, false, E, E), E),
           E),
          Root (Node (L "a", true), true, false,
           Root (Node (Impl (L "s", L "a"), false), true, false,
            Root (Node (L "s", true), true, false,
             Root (Node (L "a", false), true, true, E, E), E),
            E),
           E)),
         E)
  ;;

  contrad_path root4;;
  select_node root4;;
  valid_tableau root4;;


*)