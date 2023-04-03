(* Question 3 *)

(*

x1 = x2 /\ x2 = x3 /\ x4 = x5 /\ ~ ( f(x1) = f(x3) )

x1 = x2 /\ x2 = x3 /\ x4 = x5 /\ f(x1) =/= f(x3)

1.a. -> { x1, x2 } , { x2, x3 } , { x4 , x5 } , { f(x1) } , { f(x3) }
1.b. -> { x1, x2, x3 } , { x4, x5 } , { f(x1) } , { f(x3) }
1.c. -> { x1, x2, x3 } , { x4, x5 } , { f(x1), f(x3) }
2. -> Unsatisfiable

*)



(* Question 4 *)

type term = V of int | F of string * (int list) ;;

type eq_pred = Eq of term * term | NEq of term * term | Not of eq_pred ;;

type conj_eq = eq_pred list ;;

let exemple = [ Eq ( (V 1), (V 2) ); Eq ( (V 2), (V 3) ); Eq ( (V 4), (V 5) ); Not ( Eq ( F ( "f" , [1] ), F ( "f" , [3] )  ) ) ];;

let rec simpl phi = match phi with
    | [] -> []
    | Eq(t1, t2)::phi -> Eq(t1, t2)::(simpl phi)
    | NEq(t1, t2)::phi -> NEq(t1, t2)::(simpl phi)
    | (Not (Eq(t1, t2)))::phi -> NEq(t1, t2)::(simpl phi)
    | (Not (NEq(t1, t2)))::phi -> Eq(t1, t2)::(simpl phi)
    | (Not (Not ep))::phi -> simpl (ep::phi)
;;

simpl exemple;;

let partition_a phi =
  let l = ref [] in
  let rec parcours1 phi = match phi with
    | [] -> []
    | (Eq(t1, t2))::phi -> l := t1::t2::( !l ); [t1; t2]::(parcours1 phi)
    | _::phi -> parcours1 phi
  in let c = parcours1 phi in
     let rec parcours2 phi = match phi with
       | [] -> c
       | NEq(t1, t2)::phi when List.mem t1 !l -> if List.mem t2 !l then parcours2 phi else (l := t2::(!l); [t2]::(parcours2 phi))
       | NEq(t1, t2)::phi -> if List.mem t2 !l then (l := t1::(!l); [t1]::(parcours2 phi)) else (l := t1::t2::(!l); [t1]::[t2]::(parcours2 phi))
       | _::phi -> parcours2 phi
     in parcours2 phi
;;

let classes_a = partition_a (simpl exemple);;

let rec merge l1 l2 = match l2 with
  | [] -> l1
  | x::l2 when List.mem x l1 -> merge l1 l2
  | x::l2 -> x::(merge l1 l2)
;;
