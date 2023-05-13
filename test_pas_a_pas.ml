open Projet_logique
open Printf;;

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

