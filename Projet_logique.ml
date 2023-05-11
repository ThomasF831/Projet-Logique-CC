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



                                         (*    Partie I-a    *)


let rec simpl phi = match phi with
    | [] -> []
    | Eq(t1, t2)::phi -> Eq(t1, t2)::(simpl phi)
    | NEq(t1, t2)::phi -> NEq(t1, t2)::(simpl phi)
    | (Not (Eq(t1, t2)))::phi -> NEq(t1, t2)::(simpl phi)
    | (Not (NEq(t1, t2)))::phi -> Eq(t1, t2)::(simpl phi)
    | (Not (Not ep))::phi -> simpl (ep::phi)
;;

(* simplifie l'expression de phi en supprimant les Not qui y apparaissent *)

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

(* réalise la partition de la partie 1.a de l'algorithme :
   pour tout prédicat de la forme t=u on crée une classe d'équivalence {t,u}
*)




                                         (*    Partie I-b    *)


let classes_a = partition_a (simpl exemple);;
classes_a;;

let rec merge l1 l2 = match l2 with
  | [] -> l1
  | x::l2 when List.mem x l1 -> merge l1 l2
  | x::l2 -> x::(merge l1 l2)
;;

(* fusionne deux listes sans doublons *)

let rec merge_liste l = match l with
  | [] -> []
  | l1::l -> merge l1 (merge_liste l)
;;

(* fusionne toutes les listes de la liste l *)

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

(* revoie un couple (leq, lneq) où leq est la liste des classes de classes qui ont un élément commun avec c
   et lneq est la liste des autres classes
*)

let rec partition_b classes = match classes with
  | [] -> []
  | c::classes -> let nc, l = fusionne_c c classes in nc::(partition_b l)
;;

(* réalise la partition de la partie 1.b de l'algorithme :
   fusionne ensemble toutes les classes d'équivalence qui partagent un terme
*)

let classes_b = partition_b classes_a;;
classes_b;;




                                          (*    Partie I-c    *)


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

(* étant donné un terme ti, renvoie la liste des couples de la forme "(f,[f])"
   avec f une fonction d'arité 1 tel qu'un terme de la forme "f(ti)" apparaît
   dans une classe de "classes"
*)

liste_classes_f_ti (V 1) classes_b;;

let fusionne_congruence c classes =
  let leq = ref [] in
  let locc = ref [] in
  let c_in_leq = ref false in
  let rec parcours_c c = match c with
    | [] -> ()
    | x::c -> let lx = (liste_classes_f_ti x classes) in parcours_lx lx; locc := merge lx !locc; parcours_c c
(* calcule locc la liste des termes de la forme "f(ti)" apparaissant dans les classes de "classes" avec
   "ti" un terme de "c" et "f" une fonction d'arité 1 *)
  and parcours_lx lx = match lx with
    | [] -> ()
    | (id_f, classe)::lx -> cherche id_f classe (!locc); parcours_lx lx
(* Pour tout terme de la forme "f(x)" avec f une fonction d'arité 1 on cherche si un temre de la forme
   "f(ti)" avec ti~x a déjà été rencontré *)
  and cherche id c0 l = match l with
    | [] -> ()
    | (id2, c1)::l when id2 = id -> if (c0 = c || c1 = c) then c_in_leq := true; leq := c0::c1::(!leq)
    | _::l -> cherche id c0 l
(* cherche si la fonction "id" a déjà été ajoute à occ ce qui signifie que c0 et la classe où il apparaissait
   précédemment doivent être fusionnées, les classes devant être fusionnées sont ajoutées à leq *)
  and lneq classes = match classes with
    | [] -> []
    | c::classes when List.mem c !leq -> lneq classes
    | c::classes -> c::(lneq classes)
(* clacule la liste des classes ne devant pas être fusionnées suite au parcours de c *)
  in parcours_c c; (merge_liste !leq), lneq classes, c_in_leq
;;

(* renvoie le couple (cf, lneq) avec cf la fusion des classes contenant des termes de la forme f(ti) et f(tj)
   tels que ti et t sont dans c et lneq la liste des classes ne devant pas être fusionnées
*)

fusionne_congruence [V 1; V 2; V 3] [[F ("f", [V 1])]; [F ("f", [V 3])]; [V 4; V 5]];;

let rec elim_classes_vides classes = match classes with
  | [] -> []
  | []::classes -> elim_classes_vides classes
  | c::classes -> c::(elim_classes_vides classes)
;;

let rec cloture_congruence c classes =
  let nc, nclasses, b = fusionne_congruence c classes in
  let l = elim_classes_vides (nc::nclasses) in
  if (not !b) then l else cloture_congruence nc nclasses
;;

(* itère fusionne_congruence pour calculer la clôture des ensembles obtenus en appliquant le procédé de la
   partie 1.c de l'algorithme
*)

fusionne_congruence [V 1; V 2] [[F ("f", [V 1]); V 3]; [F ("f", [V 2]); V 4]; [F ("f", [V 3])]; [F("f",[V 4])]];;
cloture_congruence [V 1; V 2] [[F ("f", [V 1]); V 3]; [F ("f", [V 2]); V 4]; [F ("f", [V 3]); F("f",[V 4])]];;

(* Note : si on a "( t1 = t3 ) /\ (t2 = t4) /\ (F(t1,t2) = y) /\ (F(t3,t4) = z)"
          alors on obtient les classes {t1,t3},{t2,t4},{F(t1,t2),y},{F(t3,t4),z}
          (les fonctions d'arité au moins 2 ne sont pas traitées par l'algorithme)
          on pourrait étendre l'algorithme en disant que si on a des termes de la forme
          f(x1,...,xn) et f(y1,...,yn) avec x1~y1,...,xn~yn alors f(x1,...,xn)~f(y1,...,yn)
 *)

cloture_congruence [V 1; V 2] [[F ("f", [V 1]); V 3]; [F ("f", [V 2]); V 4; V 5]; [V 5; V 6; V 7]; [F ("f", [V 6]); F ("g", [V 5])]; [F ("g", [V 7])]; [F ("h", [V 1])]];;

let partition_c classes =
  let q = ref (Queue.create ()) in
  let rec enfile_classes cl = match cl with
      | [] -> ()
      | c::cl -> Queue.add c !q; enfile_classes cl
  in enfile_classes classes;
  let mc = ref classes in
  let rc = ref classes in
  let b = ref true in
  while !mc <> !rc || !b do
    mc := !rc;
    while not (Queue.is_empty !q) do
      let c = Queue.take !q in
      let l = cloture_congruence c (!rc) in
      rc := l;
    done;
    b := false;
    enfile_classes !rc;
  done;
  !mc
;;

(* réalise la partition de la partie 1.c de l'algorithme:
   on appelle cloture_congruence pour chaque classe de la liste des classes puis on recommence avec la
   nouvelle liste de classes ainsi obtenue jusqu'à ce que la liste de classes ne soit plus modifiée
*)


let classes_c = partition_c classes_b;;
classes_c;;

partition_c [[F ("f", [V 1]); V 3]; [F ("f", [V 2]); V 4; V 5]; [V 5; V 6; V 7]; [F ("f", [V 6]); F ("g", [V 5])]; [F ("g", [V 7])]; [F ("h", [V 1])]];;



                                          (*    Partie II    *)


let rec liste_inegalites formule = match formule with
  | [] -> []
  | (NEq (ti,tj))::formule -> (ti,tj)::(liste_inegalites formule)
  | _::formule -> liste_inegalites formule
;;

(* extrait les inégalités de formule et renvoie la liste des couples de terme ne devant pas appartenir à
   la même classe
*)

let rec sont_congrus ti tj classes = match classes with
  | [] -> failwith "L'un des termes n'apparaît dans aucune classe !"
  | c::classes when List.mem ti c -> List.mem tj c
  | _::classes -> sont_congrus ti tj classes
;;

let rec est_satisfiable liste_ineq classes = match liste_ineq with
  | [] -> true
  | (ti,tj)::liste_ineq -> if sont_congrus ti tj classes then false else est_satisfiable liste_ineq classes
;;

let congruence_closure formule =
  let classes = partition_c (partition_b (partition_a (simpl formule))) in
  let liste_ineq = liste_inegalites (simpl formule) in
  let b = est_satisfiable liste_ineq classes in
  if b then print_string "Satisfiable !" else print_string "Insatisfiable !"
;;

congruence_closure exemple;;
