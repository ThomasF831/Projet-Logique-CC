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

type term = V of int | F of string * (term list) ;;

type eq_pred = Eq of term * term | NEq of term * term | Not of eq_pred ;;

type conj_eq = eq_pred list ;;

let exemple = [ Eq ( (V 1), (V 2) ); Eq ( (V 2), (V 3) ); Eq ( (V 4), (V 5) ); Not ( Eq ( F ( "f" , [V 1] ), F ( "f" , [V 3] )  ) ) ];;

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
classes_a;;

let rec merge l1 l2 = match l2 with
  | [] -> l1
  | x::l2 when List.mem x l1 -> merge l1 l2
  | x::l2 -> x::(merge l1 l2)
;;

let rec merge_liste l = match l with
  | [] -> []
  | l1::l -> merge l1 (merge_liste l)
;;

let fusionne_c c classes =
  let leq = ref [c] in
  let rec parcours_classes x classes = match classes with
    | [] -> ()
    | c::classes when List.mem x c -> leq := c::(!leq); parcours_classes x classes
    | c::classes -> parcours_classes x classes
  and parcours_c c = match c with
    | [] -> ()
    | x::c -> parcours_classes x classes; parcours_c c
  and lneq classes = match classes with
    | [] -> []
    | c::classes when List.mem c !leq -> lneq classes
    | c::classes -> c::(lneq classes)
  in parcours_c c; (merge_liste !leq), lneq classes
;;

let rec partition_b classes = match classes with
  | [] -> []
  | c::classes -> let nc, l = fusionne_c c classes in nc::(partition_b l)
;;

let classes_b = partition_b classes_a;;
classes_b;;

let liste_classes_f_ti ti classes =
  let l = ref [] in
  let rec parcours_c c c0 = match c with
    | [] -> ()
    | F(id_f,[t])::c when t = ti -> l := (id_f, c0)::(!l); parcours_c c c0
    | _::c -> parcours_c c c0
  and parcours_classes classes = match classes with
    | [] -> ()
    | c::classes -> parcours_c c c; parcours_classes classes
  in parcours_classes classes;
     !l
;;

liste_classes_f_ti (V 1) classes_b;;

let cloture_congruence c classes =
  let leq = ref [] in
  let locc = ref [] in
  let rec parcours_c c = match c with
    | [] -> ()
    | x::c -> let lx = (liste_classes_f_ti x classes) in parcours_lx lx; locc := merge lx !locc; parcours_c c
  and parcours_lx lx = match lx with
    | [] -> ()
    | (id_f, classe)::lx -> cherche id_f classe (!locc); parcours_lx lx
  and cherche id c0 l = match l with
    | [] -> ()
    | (id2, c)::l when id2 = id -> leq := c0::c::(!leq)
    | _::l -> cherche id c0 l
  and lneq classes = match classes with
    | [] -> []
    | c::classes when List.mem c !leq -> lneq classes
    | c::classes -> c::(lneq classes)
  in parcours_c c; (merge_liste !leq), lneq classes
;;

cloture_congruence [V 1; V 2; V 3] [[F ("f", [V 1])]; [F ("f", [V 3])]; [V 4; V 5]];;

let rec partition_c classes = match classes with
  | [] -> []
  | c::classes -> let leq, lneq = cloture_congruence c classes in leq::(partition_c lneq)
;;
