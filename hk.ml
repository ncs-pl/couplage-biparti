(* Copyright (C) 2025 Nicolas Paul <nicolas.paul1@etu.univ-orleans.fr>
   and Tolunay Akkaya <tolunay.akkaya@etu.univ-orleans.fr>.

   This program is free software: you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation, either version 3 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

(*** ENSEMBLES ********************************************************)

module Ensemble = struct
  (** ['a t] est un ensemble d'éléments uniques de type ['a]. *)
  type 'a t = 'a list

  let vide = []
  
  (** [x @? s] est vrai si [x] est un élément de [s]. *)
  let (@?) x s = List.mem x s

  (** [x ~? s] est vrai si [x] n'est pas un élément de [s]. *)
  let (~?) x s = not (x @? s)

  (** [ajoute x s] est l'ensemble construit à partir de [s] auquel
      on ajoute [x] si possible. *)
  let ajoute s x = if x @? s then s else x :: s

  (** [retire x s] est l'ensemble construit en supprimant [x] de [s]. *)
  let retire x = List.filter ((<>) x)

  let of_list l = List.fold_left (fun s x -> ajoute s x) vide l
  let to_list s = s

  (** [s |> f] est l'ensemble où [f] est appliqué à chaque élément
      de [s]. *)
  let (|>) s f = of_list (List.map f s)

  (** [s |? p] est l'ensemble des éléments de [s] satisfaisant le
      prédicat [p]. *)
  let (|?) s p = of_list (List.filter p s)

  (** [s |/ f i] applique linéairement [f] sur les éléments de [s]
       avec [i] comme valeur initiale. *)
  let (|/) s f i = List.fold_left f i s

  (** [a + b] est l'union entre [a] et [b]. *)
  let (+) a b = List.fold_left (fun s x -> ajoute s x) a b

  (** [a * b] est le produit cartésien entre [a] et [b]. *)
  let ( * ) a b = a |> (fun x -> b |> (fun y -> (x, y)))

  (** [a & b] est l'intersection entre [a] et [b]. *)
  let (&) a b = a |? (fun x -> x @? b)

  (** [a - b] est la différence entre [a] et [b]. *)
  let (-) a b = a |? (fun x -> x ~? b)

  (** [a < b] est vrai si [a] est un sous-ensemble de [b]. *)
  let (<) a b = a <= b && not (a = b)

  (** [a > b] est vrai si [b] est un sous-ensemble de [a]. *)
  let (>) a b = b < a

  (** [a = b] est vrai si [a] est [b]. *)
  let (=) a b = a <= b && b <= a

  (** [a <= b] est vrai si [a] est [b] ou un sous-ensemble de [b]. *)
  let (<=) a b = List.for_all (fun x -> x @? b) a
  
  (** [a => b] est vrai si [b] est [a] ou un sous-ensemble de [a]. *)
  let (=>) a b = b <= a

  (** [card s] est la taille de [s]. *)
  let card = List.length

  (** [existe s p] est vrai si au moins un élément de [s] satisfait
       le prédicat [p]. *)
  let existe s p = List.exists p s

  (** [tous s p] est vrai si le prédicat [p] est satisfait par tous
      les éléments de [s]. *)
  let tous s p = List.for_all p s
end

(*** GRAPHES **********************************************************)

module Graphe = struct
  (** un graphe orienté représenté par une liste adjacente. *)
  type 'a t = 'a list array

  (** [creer n] est le graphe de [n] sommets sans arcs. *)
  let creer n = Array.init n (fun _ -> [])

  (** [ordre g] est le nombre de sommets de [g]. *)
  let ordre = Array.length
  
  (** [voisins g u] est l'ensemble des voisins de [u] dans [g]. *)
  let voisins g u = Ensemble.of_list g.(u)

  (** [g ++ u,v] ajoute l'arc [(u, v)] au graphe [g]. *)
  let (++) g (u,v) = g.(u) <- v :: g.(u)

  (** [g @?? u,v] indique si [(u, v)] est un arc du graphe [g]. *)
  let (@??) g (u,v) =  List.exists ((=) v) g.(u)

  (** [degre g u] est le degré du sommet [u]. *)
  let degre g u = List.length g.(u)

  let bfs g s f =
    let visited = Array.make (ordre g) false in
    let q = Queue.create () in
    List.iter (fun u -> visited.(u) <- true; Queue.push u q; f u) s;
    while not (Queue.is_empty q) do
      let u = Queue.pop q in
      g.(u)
        |> List.filter (fun v -> not visited.(v))
        |> List.iter (fun v -> visited.(v) <- true; f v; Queue.push v q)
    done

  let dfs g s f =
    let visited = Array.make (ordre g) false in
    let rec explore u =
      if not visited.(u) then
        visited.(u) <- true;
        f u;
        List.iter explore g.(u)
    in
    List.iter explore s
end

(*** HOPCROFT-KARP ****************************************************)

let construire_gm g m n b =
  let open Ensemble in
  let open Graphe in
  let gm = creer (ordre g) in
  let arc (u,v) = g @?? (u,v) || g @?? (v,u) in
  let ins (u,v) =
    if (u,v) @? m || (v,u) @? m then gm ++ (v,u)
    else gm ++ (u,v)
  in
  (n * b) |? arc |> ins;
  gm

let construire_niveaux gm n b =
  let open Ensemble in
  let open Graphe in
  let h = creer (ordre gm) in
  let niv = Array.make (ordre gm) (-1) in
  let _ = n |> (fun u -> niv.(u) <- 0) in
  let f u =
    (* NOTE(nico): Caml ne supporte pas la surcharge... *)
    let succ v = Stdlib.(niv.(v) = -1 || niv.(v) = niv.(u) + 1) in
    let visit v = niv.(v) <- Stdlib.(niv.(u) + 1); h ++ (u,v) in
    let _ = voisins gm u |? succ |> visit in ()
  in
  let _ = bfs gm n f in
  let k =
    match (b |? (fun u -> niv.(u) <> -1)) |> (fun u -> niv.(u)) with
    | [] -> -1
    | l -> List.fold_left min max_int l
  in h, niv, k

let renverser h =
  let open Graphe in
  let open List in
  let ht = creer (ordre h) in
  let _ = Array.iteri (fun u k -> iter (fun v -> ht ++ (v,u)) k) h in
  ht

let chemins_augmentants h z k =
  let open Graphe in
  let open List in
  let tag = Array.make (ordre h) false in
  let p = ref [] in
  let f u =
    if not tag.(u) then
      let aug = ref false in
      let chemin = ref [] in
      let g v =
        if not !aug && not tag.(v) then begin
          chemin := v :: !chemin;
          if mem v z then aug := true
        end
      in
      dfs h [u] g;
      if !aug then begin
        iter (fun v -> tag.(v) <- true) !chemin;
        p := rev !chemin :: !p
      end
  in
  iter f k;
  !p

let hopcroft_karp g n b =
  let open Ensemble in
  let libres e m =
    let tt x = not (existe m (fun (u, v) -> u = x || v = x)) in
    e |? tt
  in
  let niv_k niv k b = b |? (fun u -> niv.(u) = k) in
  let rec boucle m =
    let gm = construire_gm g m n b in
    let ln = libres n m in
    let lb = libres b m in
    let h, niv, k = construire_niveaux gm ln lb in
    let ht = renverser h in
    let lz = niv_k niv 0 ln in
    let lk = niv_k niv k lb in
    let p = chemins_augmentants ht lz lk in
    match p with
| vide -> m
| s -> 
    let c = List.fold_left (+) vide (List.map (fun chemin ->
      of_list (List.filter_map2 (fun a b ->
        if not ((a, b) @? m || (b, a) @? m) then Some (a, b) else None
      ) chemin (List.tl chemin))
    ) (to_list s)) in
    boucle ((m + c) - (m & c))
  in
  boucle vide

(*** MAIN *************************************************************)

let lire_echiquier f =
  let ic = open_in f in
  let n = int_of_string (input_line ic) in
  let echiquier = Array.make_matrix n n 'X' in
  for i = 0 to n - 1 do
    let ligne = input_line ic in
    let cases = String.split_on_char ' ' ligne in
    List.iteri (fun j case ->
      if j < n then echiquier.(i).(j) <- case.[0]
    ) cases
  done;
  close_in ic;
  (n, echiquier)

let construire_graphe n echiquier =
  let cases = ref [] in
  let noir = ref [] in
  let blanc = ref [] in
  
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if echiquier.(i).(j) <> 'X' then begin
        let case = (i, j) in
        cases := case :: !cases;
        if (i + j) mod 2 = 0 then
          noir := case :: !noir
        else
          blanc := case :: !blanc
      end
    done
  done;
  
  let g = Graphe.creer (List.length !cases) in
  let case_to_id = Hashtbl.create (List.length !cases) in
  List.iteri (fun id case -> Hashtbl.add case_to_id case id) !cases;
  
  (* Ajouter les arêtes entre cases adjacentes *)
  List.iter (fun (i, j) ->
    List.iter (fun (i', j') ->
      if abs (i - i') + abs (j - j') = 1 && echiquier.(i').(j') <> 'X' then begin
        let open Graphe in
        let u = Hashtbl.find case_to_id (i, j) in
        let v = Hashtbl.find case_to_id (i', j') in
        g ++ (u,v);
        g ++ (v,u);
      end
    ) !cases
  ) !cases;
  
  (g, List.length !cases, 
   Ensemble.of_list !noir, 
   Ensemble.of_list !blanc,
   case_to_id)

let afficher_resultat n echiquier couplage case_to_id =
  (** TODO *)

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <echiquier>\n" Sys.argv.(0);
    exit 1
  end;
  let fichier = Sys.argv.(1) in
  let n, echiquier = lire_echiquier fichier in
  let g, nb, noir, blanc, case_to_id = construire_graphe n echiquier in
  let m = hopcroft_karp g noir blanc in
  if (Ensemble.card m) * 2 = (Ensemble.card noir + Ensemble.card blanc)
  then begin
    Printf.printf "True\n";
    afficher_resultat n echiquier m case_to_id
  end else begin
    Printf.printf "False\n"
  end

(* vim: set ft=ocaml ts=2 sts=2 sw=2 expandtab cc=72: *)
