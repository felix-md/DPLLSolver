(* MP1 2024/2025 - dpll.ml *)

open List


(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien y ajouter.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   afficher le résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  
  (* on cré un alias f de notre fonction de filtre *)
  (* la fonction de filtre parcours une clause en enlevant
   les proposotion non(l) car elle sont forcement fausse *)
  let f c = filter_map (fun x -> if x = -l then None else Some x) c in
  (* on cré une fonction auxiliaire qui va parcourir les clauses recursivement *)
  let rec aux l clauses acc = 
    match clauses with
    (* Quand on a fini, on renvoie notre accumulateur dans le bon sens *)
    | []   -> List.rev acc
    | h::t -> 
              (* si l est dans la clause h alors on ne l'ajoute pas car elle est satisfaite *)
              if mem l h then aux l t acc
              else
              (* sinon on filtre la clause *)
              let h_simplified = f h in 
              (* si la clause est vide, alors on renvoie une liste vide ce qui optimise l'algorithme *)
              if h_simplified = [] then [[]] else aux l t (h_simplified::acc)
             

  in aux l clauses []


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, renvoie None *)
let pur clauses =
  (* On applatit la list de list en list *)
  (* On trie la liste et on enleve les doublons *)
  let uniq_flatten =List.sort_uniq Int.compare (flatten clauses) in
  (* Fonction auxiliare qui permet de parcourir les éléments de uniq_flatten *)
  let rec aux  = function
    (* Si on a parcouru tout les elements de uniq_flatten alors on renvoie None *)
    | [] -> None
    (* Sinon on regarde si la négation du littéral qu'on traite est présente dans uniq_flatten *)
    | h::t -> if mem (-h) uniq_flatten then aux t else Some h
  in aux uniq_flatten



(* unitaire : int list list -> int option
- si `clauses' contient au moins une clause unitaire, retourne
le littéral de cette clause unitaire ;
- sinon, renvoie None *)
let rec unitaire clauses =
  match clauses with
  | []   -> None
  (* Si une clause est de taille 1, alors elle est unitaire *)
  | [x]::t -> Some x
  
  | _::t ->  unitaire t

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if clauses = [[]] then None else
  (* on cherche une clause unitaire *)
  let u = unitaire clauses in 
  match u with
    (* Si il y en a une on la met a vraie dans notre interpretation*)
    | Some lit -> solveur_dpll_rec (simplifie lit clauses) (lit::interpretation)
    | None ->
      (* Si il n'y a pas de clause unitaire, on cherche une variable pur *)
      let p = pur clauses in 
      (* Si il y en a une on la met a vraie dans notre interpretation*)
      match p with 
      | Some lit -> solveur_dpll_rec (simplifie lit clauses) (lit::interpretation)
      | None -> 
          (* Si il n'y a ni clause unitaire ni variable pur *)
          (* On prend la première variable de la liste *)
          let l = hd ( hd clauses) in
          
          (* On la satisfait dans notre interpretation *)
          let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
          match branche with
            (* Si la branche est insatisfiable, on satisfait son opposé *)
            | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
            (* Sinon on retourne la branche *)
            | _    -> branche

(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses []);
  
