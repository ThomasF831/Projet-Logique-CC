open Projet_logique;;

let n () = print_string "\n";;

n();;
print_string "x1 = x2 /\ x2 = x3 /\ x4 = x5 /\ ~ ( f(x1) = f(x3) ) :";
n();;
congruence_closure exemple;;
n();;
