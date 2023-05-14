open Projet_logique
open Printf;;

n(); n();;

printf " X1 = X2 /\\ X2 = X3 /\\ X4 = X5 /\\X4 = X6 /\\ X1 = X6 /\\ X7 = X8 /\\ X3 = X7 /\\ X1 =/= X9"
let exemple3 = [Eq(V 1, V 2); Eq (V 2, V 3); Eq (V 4, V 5); Eq (V 5, V 6); Eq (V 1, V 6); Eq(V 7, V 8); Eq(V 8, V 9); Eq(V 3, V 7); NEq(V 1, V 9)];;

n(); n();;
let classes_a3 = partition_a exemple3 in
    print_classes classes_a3; n();
    let classes_b3 = partition_b classes_a3 in
    print_classes classes_b3; n();
    print_classes (partition_c classes_b3); n();
    congruence_closure exemple3;;
