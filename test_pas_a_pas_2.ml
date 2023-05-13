open Projet_logique
open Printf;;

let exemple2 = [ Eq ( (V 1), (V 2) ); Eq ( (V 2), (V 3) ); Eq ( (V 4), (V 5) ); Not ( Eq ( F ( "f" , [V 1] ), F ( "f" , [V 4] )  ) ) ];;

n();;

printf "x1 = x2 /\\ x2 = x3 /\\ x4 = x5 /\\ ~ ( f(x1) = f(x3) ) :\n\n";;
n(); print_formule (exemple2);
n(); n();;
printf "Etape de simplification:\nx1 = x2 /\\ x2 = x3 /\\ x4 = x5 /\\ f(x1) =/= f(x3)\nAppel à simpl :\n\n";
print_formule (simpl (exemple2));
n();n();n();;

printf "Etape 1.a:\n{ x1, x2 } , { x2, x3 } , { x4 , x5 } , { f(x1) } , { f(x3) }\nAppel à partition_a:\n\n";;
let classes_a2 = partition_a (simpl exemple2);;
print_classes (classes_a2);;
n();n();n();;

printf "Etape 1.b:\n{ x1, x2, x3 } , { x4, x5 } , { f(x1) } , { f(x3) }\nAppel à partition_b:\n\n";;
let classes_b2 = partition_b classes_a2;;
print_classes (classes_b2);;
n();n();n();;

printf "Etape 1.c:\n{ x1, x2, x3 } , { x4, x5 } , { f(x1), f(x3) }\nAppel à partition_c:\n\n";;
let classes_c2 = partition_c classes_b2;;
print_classes (classes_c2);;
n();n();n();;

printf "Etape 2, appel à congruence_closure:\n\n";;
congruence_closure exemple2;;
n();;
