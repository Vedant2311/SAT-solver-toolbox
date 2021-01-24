(******************************************************A TOY PROPOSITIONAL LANGUAGE *****************************************************************************************************)
(*********************************THE SAME IMPLEMENTATION AS PRESENT IN THE basic-toolbox DIRECTORY**************************************************************************************)
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

let rho s = match s with 

	"x1" -> false
  | "x2" -> true
  | "x3" -> true
  | "x4" -> false
  | _ -> true

let rec inDomain s l = match l with 

	[] -> false
  | x  :: xs -> if (x=s) then true else (inDomain s xs)

let dom = ["x1";"x2";"x3";"x4"];;

let rec ht p = match p with

	T -> 0
  | F -> 0
  | L(s) -> 0
  | Not(q) -> 1 + (ht q)
  | And(q1,q2) -> 1 + (max (ht q1) (ht q2))
  | Or(q1, q2) -> 1 + (max (ht q1) (ht q2))
  | Impl(q1, q2) -> 1 + (max (ht q1) (ht q2))
  | Iff(q1, q2) -> 1 + (max (ht q1) (ht q2))

let rec size p = match p with 

	T -> 1
  | F -> 1
  | L(s) -> 1
  | Not(q) -> 1 + (size q)
  | And(q1,q2) -> 1 + (size q1) + (size q2)
  | Or(q1, q2) -> 1 + (size q1) + (size q2)
  | Impl(q1, q2) -> 1 + (size q1) + (size q2)
  | Iff(q1, q2) -> 1 + (size q1) + (size q2)

let rec subst p x b = match p with

  T -> T
  | F -> F
  | L(s) -> if (s=x) then b else L(s)
  | Not(q) -> Not(subst q x b)
  | And(q1,q2) -> And((subst q1 x b), (subst q2 x b))
  | Or(q1, q2) -> Or((subst q1 x b), (subst q2 x b))
  | Impl(q1, q2) -> Impl((subst q1 x b), (subst q2 x b))
  | Iff(q1, q2) -> Iff((subst q1 x b), (subst q2 x b))


let rec letters p = match p with

	T -> []
  | F -> []
  | L(s) -> [s]
  | Not(q) -> (letters q)
  | And(q1,q2) -> (union (letters q1) (letters q2))
  | Or(q1, q2) -> (union (letters q1) (letters q2))
  | Impl(q1, q2) -> (union (letters q1) (letters q2))
  | Iff(q1, q2) -> (union (letters q1) (letters q2))


let rec truth p rho = match p with 

	T -> true
  | F -> false
  | L(s) -> if (inDomain s dom) then (rho s) else raise (Myexp "Not in domain")
  | Not(q) -> not (truth q rho)
  | And(q1,q2) -> if ((q1=F)||(q2=F)||(not(truth q1 rho))||(not(truth q2 rho))) then false else (truth q1 rho) && (truth q2 rho)
  | Or(q1, q2) -> if ((q1=T)||(q2=T)||((truth q1 rho))||((truth q2 rho))) then true else (truth q1 rho) || (truth q2 rho)
  | Impl(q1, q2) -> if (truth q1 rho) then (truth q2 rho) else true
  | Iff(q1, q2) -> if ((truth q1 rho)=(truth q2 rho)) then true else false

let rec subprop p1 p2 = match p2 with 

	T -> (if p1=T then true else false)
  | F -> (if p1 = T then true else false)
  | L(s) -> (if p1=L(s) then true else false)
  | Not(q) -> (if ((p1=q)||(p1=p2)) then true else (subprop p1 q))
  | And(q1,q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Or(q1, q2) ->(if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Impl(q1, q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))
  | Iff(q1, q2) -> (if ((p1=p2)||(p1=q1)||(p1=q2)) then true else ((subprop p1 q1)||(subprop p1 q2)))


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

let rec cnf p = let p1 = nnf p in (

	match p1 with

	 Or(q1,And(q2,q3)) -> (And((cnf (Or((cnf q1),(cnf q2)))),(cnf (Or((cnf q1),(cnf q3))))))
   | Or(And(q2,q3),q1) -> (And((cnf (Or((cnf q2),(cnf q1)))),(cnf (Or((cnf q3),(cnf q1))))))
   | And(q1,q2) -> And(cnf q1, cnf q2)
   | _  -> p1

)

let rec dnf p = let p1 = nnf p in (

	match p1 with

	 And(q1,Or(q2,q3)) -> (Or((dnf (And((dnf q1),(dnf q2)))),(dnf (And((dnf q1),(dnf q3))))))
   | And(Or(q2,q3),q1) -> (Or((dnf (And((dnf q2),(dnf q1)))),(dnf (And((dnf q3),(dnf q1))))))
   | Or(q1,q2) -> Or(dnf q1, dnf q2)
   | _ -> p1

)

(**********************************************************************************************************************************************************************)
(***************************************DEFINING THE ROBDD FUNCTIONS FROM THIS POINT ONWARDS***************************************************************************)

(* Helper functions used for creating a ROBDD *)
let rec lookup hH (i,l,h) = match hH with 

    [] -> -1
  |  ((i',l',h'),u):: xs -> if ((i=i')&& (l=l') && (h=h')) then u else lookup xs (i,l,h)

let rec memberH hH (i,l,h) = match hH with 

    [] -> false
  |  ((i',l',h'),u):: xs -> if ((i=i')&& (l=l') && (h=h')) then true else memberH xs (i,l,h)

let insert hH (i,l,h) u = ((i,l,h),u) :: hH

(* Initialising the Table *)
let initT t = let varList = (letters t) in (let size = (List.length varList) in (

    [(1,(size+1,-1,-1));(0,(size+1,-1,-1))]

  )

)

let rec find u tT = match tT with 

  [] -> (-1,-1,-1)
| (u',(i,l,h)):: xs -> (if (u=u') then (i,l,h) else (find u xs))

let var u tT = let tup = find u tT in (

    match tup with 
    (i,l,h) -> i
)

let low u tT = let tup = find u tT in (

    match tup with 
    (i,l,h) -> l
)


let high u tT = let tup = find u tT in (

    match tup with 
    (i,l,h) -> h
)

let add tT (i,l,h) u = (u,(i,l,h)) :: tT

(*************************************************************CREATING THE ROBDD ***************************************************************************)

(* Give the Proposition that you wish to be solved here*)
let t = Or(Iff(L("x1"),L("x2")),L("x3"));;
(*let t =   Or (And (Or (Not (L "x1"), L "x2"), Or (Not (L "x2"), L "x1")), L "x3");;*)
(*let t = Impl(And(L("x1"),Not(L("x2"))),L("x3"));;*)
(*let t = Or(Impl(And(L("x1"),Not(L("x2"))),L("x3")),Or(Iff(L("x1"),L("x2")),L("x3")));;*)
(*let t = Or(Not(L("x1")), L("x3"));;*)
(*let t = Or(L("x1"),L("x2"));;*)

(* Important global pointers needed to construct the tree *)
let initH = [];;
let hH = ref (initH);;

let tTT = initT t;;
let tT = ref (tTT);;

let u_used = ref (1);;

(* Add the tuple to the Table *)
let mk (i,l,h) = if (l=h) then l else(

  if (memberH !hH (i,l,h)) then (lookup !hH (i,l,h))
  else(

    let u = (!u_used)+1 in
    ( 
        tT := (add !tT (i,l,h) u); hH := (insert !hH (i,l,h) u); u_used := u; u

    )
  )

)

(* Helper funciton for the construction of the ROBDD table *)
let rec build t i vars n = (if (i>n) then (

	  let b = (truth t rho) in (
	    if (b=false) then 0 else 1
	  )

	) else(
		  let v0 = (build (subst t (List.nth vars (i-1)) F) (i+1)) and v1 = (build (subst t (List.nth vars (i-1)) T) (i+1)) in (

		    mk (i,v0,v1)
		  )
	  )
	)

(* Builts a tree for the given proposition t *)
let rec buildEx t = tT := (initT t); hH := (initH) ; u_used := 1; (build t 1 (letters t) (List.length (letters t)))

(* For: (x1 <=> x2) \/ x3 *)
(* Below ROBDD obtained by applying the buildEx command *)
let tT1 =  ([(5, (1, 3, 4)); (4, (2, 2, 1)); (3, (2, 1, 2)); (2, (3, 0, 1));
 (0, (4, -1, -1)); (1, (4, -1, -1))]
) ;;

(* For: (x1 /\ (-x2)) => x3 *)
(* Below ROBDD obtained by applying the buildEx command *)
let tT2 = [(4, (1, 1, 3)); (3, (2, 2, 1)); (2, (3, 0, 1)); (0, (4, -1, -1));
 (1, (4, -1, -1))];;

let initH3 = [];;
let hH3 = ref (initH3);;

let tTT3 = initT t;;
let tT3 = ref (tTT3);;

let u_used3 = ref (1);;

let mk3 (i,l,h) = if (l=h) then l else(

  if (memberH !hH3 (i,l,h)) then (lookup !hH3 (i,l,h))
  else(

    let u = (!u_used3)+1 in
    ( 
        tT3 := (add !tT3 (i,l,h) u); hH3 := (insert !hH3 (i,l,h) u); u_used3 := u; u

    )
  )

)

let gG = ref ([]);;

let rec presentInG u1 u2 gG = match (gG) with 

	[] -> false
 | (ux,uy,u) :: xs -> (if ((ux=u1) && (uy=u2)) then true else (presentInG u1 u2 xs))

 let rec findInG u1 u2 gG = match (gG) with 

	[] -> -1
 | (ux,uy,u) :: xs -> (if ((ux=u1) && (uy=u2)) then u else (findInG u1 u2 xs))

let rec addInG u1 u2 u gG = (u1,u2,u) :: gG

let applyOp u1 u2 op = match op with 

						"And" -> if ((u1=1) && (u2=1)) then 1 else 0
					  | "Or" -> if ((u1=0) && (u2=0)) then 0 else 1
					  | "Impl" -> if ((u1=0) || (u2=1)) then 1 else 0
					  | "Iff" ->  if (u1=u2) then 1 else 0
					  | _ -> (raise (Myexp "Invalid Operator Input"))

(* The apply function that merges the two ROBDD and gets the new one according to the operation "opp"*)
let rec app u1 u2 op = gG := [] ; 
					   if (u2>u1) then (app u2 u1 op) else (
						if (presentInG u1 u2 (!gG)) then (findInG u1 u2 (!gG)) 
							else (

								if (((u1 = 0) || (u1 = 1)) && ((u2=0) || (u2=1))) then (gG := (addInG u1 u2 (applyOp u1 u2 op) (!gG)); (applyOp u1 u2 op))
								else (

									if ((var u1 tT1) = (var u2 tT2)) then (let p = (mk3 ((var u1 tT1),(app (low u1 tT1) (low u2 tT2) op),(app (high u1 tT1) (high u2 tT2) op))) in (gG := (addInG u1 u2 p (!gG)); p))
									else (

										if ((var u1 tT1) <  (var u2 tT2)) then (let p = (mk3 ((var u1 tT1),(app (low u1 tT1) u2 op),(app (high u1 tT1) u2 op))) in (gG := (addInG u1 u2 p (!gG)); p))
										else (let p = (mk3 ((var u2 tT2),(app u1 (low u2 tT2) op),(app u1 (high u2 tT2) op))) in (gG := (addInG u1 u2 p (!gG)); p))
									)
								)

							)
						)

(* Corrects the Table obtained from the previous apply function *)
let rec correctApp tT = match tT with 

	[] -> []
 | (u,(i,l,h)) :: xs -> if (((l=0) && (h=1)) || ((l=1) && (h=0))) then (u,(i,l,h)) :: (correctApp xs) else ((u,(i,h,l)) :: (correctApp xs))


(*************************************************************USING ROBDD TO SOLVE SAT ***************************************************************************)

let rec exp2 v = if v=0 then 1 else 2 * (exp2 (v-1))

(* Takes the integer u for the root noode of the ROBDD and the implemented ROBDD, as a list*)
(* Outputs the total number of Satisfiable solutions for the given ROBDD *)
let satCount u tT = (

	let rec count u tT= if u=0 then 0 else (

		if u=1 then 1 else (

			(exp2 ((var (low u tT) tT) - (var u tT) - 1)) * (count (low u tT) tT)
				+ (exp2 ((var (high u tT) tT) - (var u tT) - 1)) * (count (high u tT) tT)

		)

	)

in (exp2 ((var u tT) - 1)) * (count u tT)
) 

(* Takes the integer u for the root noode of the ROBDD and the implemented ROBDD, as a list*)
(* Outputs any one satisfiable arguement for the given ROBDD *)
let rec anySat u tT = if u=0 then (raise (Myexp "Error")) else (

	if u=1 then [] else 
		if ((low u tT) = 0) then ((var u tT),1) :: (anySat (high u tT) tT)
		else ((var u tT),0) :: (anySat (low u tT) tT)

)

(* Some trivial helper functions *)
let rec addToFront x l = match l with 

	[] -> []
  | y :: ys -> (x :: y) :: (addToFront x ys)

let rec addLists l1 l2 = if (l2 = [[(-1,-1)]]) then l2 else (match l1 with 

	[] -> l2
  | x :: xs -> x :: (addLists xs l2)
)

let rec tempSat u tT = if u=0 then [[(-1,-1)]]
						else (

							if u=1 then [[]]
							else (addLists (addToFront ((var u tT),0) (tempSat (low u tT) tT)) (addToFront ((var u tT),1) (tempSat (high u tT) tT)))

						)


let rec presentNegOne l = match l with 

	[] -> false
  | (a,b) :: xs -> if ((a=(-1)) && (b=(-1))) then true else (presentNegOne xs)

let rec removeZeroVals tT = match tT with 

	[] ->  []
  | x :: xs -> if (presentNegOne x) then (removeZeroVals xs) else (x :: (removeZeroVals xs))

(* Takes the integer u for the root noode of the ROBDD and the implemented ROBDD, as a list*)
(* Outputs all the Satisfiable arguments for the ROBDD*)
let allSat u tT = let p = (tempSat u tT) in (removeZeroVals p)


(*************************************************************MODIFYING THE ROBDD***************************************************************************)

(*
let tT =  ([(5, (1, 3, 4)); (4, (2, 2, 1)); (3, (2, 1, 2)); (2, (3, 0, 1));
 (0, (4, -1, -1)); (1, (4, -1, -1))]
) ;;


(*Corresponding to x1 => x2*)
let tT1 = [(3, (1, 1, 2)); (2, (2, 0, 1)); (1, (3, -1, -1)); (0, (3, -1, -1))];;

let t =   Or (And (Or (Not (L "x1"), L "x2"), Or (Not (L "x2"), L "x1")), L "x3");;


let initH2 = [];;
let hH2 = ref (initH2);;

let tTT2 = initT t;;
let tT2 = ref (tTT2);;

let u_used2 = ref (1);;

let mk2 (i,l,h) = if (l=h) then l else(

  if (memberH !hH2 (i,l,h)) then (lookup !hH2 (i,l,h))
  else(

    let u = (!u_used2)+1 in
    ( 
        tT2 := (add !tT2 (i,l,h) u); hH2 := (insert !hH2 (i,l,h) u); u_used2 := u; u

    )
  )

)

(* The restrict function as specified in the algorithm*)
let restrict (u,j,b) = 

    let rec res u = if ((var u tT) > j) then (

    	if (((low u tT) = -1) || ((high u tT) = -1)) then 
    		u
    	else (mk2 ((var u tT),((low u tT)),( (high u tT))))

	) else (

        if ((var u tT) < j) then (mk2 ((var u tT),(res (low u tT)),(res (high u tT))))
        else(

          if (b=0) then (res (low u tT)) else (res (high u tT))
        )
    ) in (res u)

let rec reduceTable l p = match l with 

	[] -> []
 | (u,(i,l,h)) :: xs -> (u,(i-p,l,h)) :: (reduceTable xs p)

let rec simplifyTable tT = if ((List.length tT) <2) then tT else (

	match tT with 

	(u,(i,l,h)) :: (u1,(i1,l1,h1)) :: xs -> (

		if ((i1-i)>1) then (

			let p = (i1-1-1) in ((u,(i,l,h)) :: (simplifyTable (reduceTable ((u1,(i1,l1,h1)) :: xs) p)))

		)

		else (u,(i,l,h)) :: (simplifyTable ((u1,(i1,l1,h1)) :: xs))


	)

)

(*
Test:

---- We test this function for the above constructed ROBDD by taking x2 |-> 0 substitution, thus leaving (-x1 \/ x3)
--- The inputs of the Restrict function should be: ((u_used + 1), var j, value b)

# restrict (5,2,0);;
- : int = 3
# !tT2;;
- : (int * (int * int * int)) list =
[(3, (1, 1, 2)); (2, (3, 0, 1)); (0, (4, -1, -1)); (1, (4, -1, -1))]

---- Then we build the ROBDD for (-x1 \/ x3) and comparing it with this ROBDD gives a similar output

buildEx t;;
- : int = 3
# !tT;;
- : (int * (int * int * int)) list =
[(3, (1, 1, 2)); (2, (2, 0, 1)); (0, (3, -1, -1)); (1, (3, -1, -1))]


--- This can be further simplified if we changed the variable numbering in the reduced ROBDD then both of them can be equal.

# let a = !tT2;;
val a : (int * (int * int * int)) list =
  [(3, (1, 1, 2)); (2, (3, 0, 1)); (0, (4, -1, -1)); (1, (4, -1, -1))]
# simplifyTable a;;
- : (int * (int * int * int)) list =
[(3, (1, 1, 2)); (2, (2, 0, 1)); (0, (3, -1, -1)); (1, (3, -1, -1))]

# tT2 :=a;;
- : unit = ()
# !tT2;;
- : (int * (int * int * int)) list =
[(3, (1, 1, 2)); (2, (3, 0, 1)); (0, (4, -1, -1)); (1, (4, -1, -1))]
*)

(* Function to Simplify the formed ROBDD *)
let rec simplify d u = if d=0 then 0 else (if (u<=1) then u else (

		if d=1 then mk2((var u tT),(simplify d (low u tT)),(simplify d (high u tT)))
		else (

			if ((var u tT) = (var d tT1)) then (

				if ((low d tT1) = 0) then (simplify (high d tT1) (high u tT))
				else if ((high d tT1) = 0) then (simplify (low d tT1) (low u tT1))
				else mk2((var u tT),(simplify (low d tT1) (low u tT)),(simplify (high d tT1) (high u tT)))
			)

			else (

				if ((var d tT1) < (var u tT)) then mk2((var d tT1),(simplify (low d tT1) u),(simplify (high d tT1) u))
				else mk2((var u tT),(simplify d (low u tT)),(simplify d (high u tT)))
			)

		)
	)

)

(* Some helper functions to program SAT solving to verify the usability of the above commands *)
let rec addToFront x l = match l with 

	[] -> []
  | y :: ys -> (x :: y) :: (addToFront x ys)

let rec addLists l1 l2 = if (l2 = [[(-1,-1)]]) then l2 else (match l1 with 

	[] -> l2
  | x :: xs -> x :: (addLists xs l2)
)

let rec tempSat u tT = if u=0 then [[(-1,-1)]]
						else (

							if u=1 then [[]]
							else (addLists (addToFront ((var u tT),0) (tempSat (low u tT) tT)) (addToFront ((var u tT),1) (tempSat (high u tT) tT)))

						)


let rec presentNegOne l = match l with 

	[] -> false
  | (a,b) :: xs -> if ((a=(-1)) && (b=(-1))) then true else (presentNegOne xs)

let rec removeZeroVals tT = match tT with 

	[] ->  []
  | x :: xs -> if (presentNegOne x) then (removeZeroVals xs) else (x :: (removeZeroVals xs))


let allSat u tT = let p = (tempSat u tT) in (removeZeroVals p)



(*
Test for the Simplify function:

--- We simplify (x1 <=> x2) \/ x3 against (x1 \/ x2). We observe that the size of the new ROBDD is reduced

# simplify 3 5;;
- : int = 4
# !tT2;;
- : (int * (int * int * int)) list =
[(4, (1, 3, 1)); (3, (2, 1, 2)); (2, (3, 0, 1)); (1, (4, -1, -1));
 (0, (4, -1, -1))]


--- Now, we check for the Satisfiable outcomes for this above ROBDD

# allSat 5 tT;;
- : (int * int) list list =
[[(1, 0); (2, 0)]; [(1, 0); (2, 1); (3, 1)]; [(1, 1); (2, 0); (3, 1)];
 [(1, 1); (2, 1)]]

# allSat 3 tT1;;
- : (int * int) list list = [[(1, 0)]; [(1, 1); (2, 1)]]

# allSat 4 !tT2;;
- : (int * int) list list =
[[(1, 0); (2, 0)]; [(1, 0); (2, 1); (3, 1)]; [(1, 1)]]


--- Now, if we obtain the intersections of the Satisfiable outcomes, we get the result for both the cases as:

[[(1,0);(2,0);(3,0)];[(1,0);(2,0);(3,1)];[(1,0);(2,1);(3,1)];[(1,1);(2,1);(3,0)];[(1,1);(2,1);(3,1)]]

*)
*)

(*************************************************************END OF THE ROBDD PROGRAM***************************************************************************)