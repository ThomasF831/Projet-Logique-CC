open Projet_logique
open Printf;;

let rec print_term t = match t with
  | V n -> printf "X%d" n
  | F (id,l) -> printf "%s(" id; List.iter print_term l; printf ")"
;;

let rec print_eqpred e = match e with
  | Eq (t1, t2) -> print_term t1; printf " = "; print_term t2
  | NEq (t1, t2) -> print_term t1; printf " =/= "; print_term t2
  | Not e -> printf "¨¨¨|("; print_eqpred e; printf " )"
;;

let rec print_formule l = match l with
  | [] -> printf "T"
  | [e] -> print_eqpred e
  | e::l -> print_eqpred e; printf " /\\ "; print_formule l
;;

let rec enumere_classe c = match c with
  | [] -> printf "Ø"
  | [t] -> print_term t
  | t::c -> print_term t; printf ", "; enumere_classe c
;;

let print_elems c = match c with
  | [] -> enumere_classe c
  | _ -> printf "{ "; enumere_classe c; printf " } "
;;

let rec print_classes classes = match classes with
  | [] -> printf "Ø"
  | [c] -> print_elems c
  | c::l -> print_elems c; printf ", "; print_classes l
;;

let n () = printf "\n";;
n();;

printf "x1 = x2 /\\ x2 = x3 /\\ x4 = x5 /\\ ~ ( f(x1) = f(x3) ) :\n\n";;
n(); print_formule (exemple);
n(); n();;
printf "Etape de simplification:\nx1 = x2 /\\ x2 = x3 /\\ x4 = x5 /\\ f(x1) =/= f(x3)\nAppel à simpl :\n\n";
print_formule (simpl (exemple));
n();n();n();;

printf "Etape 1.a:\n{ x1, x2 } , { x2, x3 } , { x4 , x5 } , { f(x1) } , { f(x3) }\nAppel à partition_a:\n\n";
print_classes (partition_a (simpl exemple));
n();n();n();;

printf "Etape 1.b:\n{ x1, x2, x3 } , { x4, x5 } , { f(x1) } , { f(x3) }\nAppel à partition_b:\n\n";
print_classes (partition_b classes_a);
n();n();n();;

printf "Etape 1.c:\n{ x1, x2, x3 } , { x4, x5 } , { f(x1), f(x3) }\nAppel à partition_c:\n\n";
print_classes (partition_c classes_b);
n();n();n();;

printf "Etape 2, appel à congruence_closure:\n\n";
congruence_closure exemple;;
n();;

