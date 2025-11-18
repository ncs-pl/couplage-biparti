
(*
   Une implémentation de l'algorithme de Hopcroft-Karp en Objective Caml dans
   le cadre du cours de Modélisation, graphes et algorithmes à l'Université
   d'Orléans.

   Copyright (C) 2025 Nicolas Paul <nicolas.paul1@etu.univ-orleans.fr> and
   Tolunay Akkaya <tolunay.akkaya@etu.univ-orleans.fr>.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

(*** PARSING *****************************************************************)

module Parser = struct
  (* Monade *)

  type 'a t = string -> ('a * string) option

  let return v s = Some (v, s)
  let empty _ = None

  let bind p f s = Option.bind (p s) (fun (v, rest) -> f v rest)
  let (>>=) = bind

  (* Combinateurs principaux. *)

  let map p f = p >>= fun v -> return (f v)
  let (|>) = map

  let choice p q s = Option.value ~default:(q s) (p s)
  let (<|>) = choice

  let left p q = p >>= fun v -> q >>= fun _ -> return v
  let (<<) = left

  let right p q = p >>= fun _ -> q
  let (>>) = right

  let peek p s = Option.map (fun v, _ -> v, s) (p s)
  let (?>) = peek

  let rec repeat p acc s =
    Option.fold ~none:(fun _ -> return (List.rev acc) s)
                ~some:(fun v, s' -> repeat p (v :: acc) s')
		(p s)
  let ( * ) = repeat

  let any s =
    if s = "" then None
    else Some (String.get s 0, String.sub s 1 (String.length s - 1))
  let (.) = any

  (* Combinateurs dérivés et pratiques. *)

  let satisfy pred = . >>= fun c -> if pred c then return c else empty

  let char c = satisfy ((=) c)
  let one_of chars = satisfy (fun c -> List.exists ((=) c) chars)
  let none_of chars = satisfy (fun c -> not (List.exists ((=) c) chars))

  let digit = satisfy (fun c -> '0' <= c && c <= '9')
  let rec digits acc = (digit >>= fun d -> digits (d :: acc)) <|> return (List.rev acc)
  let natural = digits [] |> fun cs -> return (int_of_string (String.of_seq (List.to_seq cs)))
  
  let space = char ' '
  let optional_cr = (char '\r') <|> return '\000'
  let newline = optional_cr >> char '\n'

  let sep_by1 sep p =
    p >>= fun first ->
    let rec aux acc =
      (sep >> p >>= fun v -> aux (v :: acc)) <|> return (List.rev acc)
    in aux [first]

  let sep_by sep p = sep_by1 sep p <|> return []
end

(*** GRAPH *******************************************************************)

(*** MAIN ********************************************************************)

(* FS I/O pour Windows, OS X et GNU. *)

let read_board_file filename =
  let ic = open_in filename in
  let len = in_channel_length ic in
  let data = really_input_string ic len in
  close_in ic;
  data

(* TODO: write *)

(* Parser monadique combinatoire. *)

type ast = cell list list
and cell = B | N | X

let parse_board_file data =
  let open Parser in
  let cell_of_string =
    function
    | 'N' -> return N
    | 'B' -> return B
    | 'X' -> return X
    | _ -> empty
  in
  let cell = one_of ['N'; 'B'; 'X'] |> cell_of_string in
  let row n =
    let valid cells = if List.length cells = n then return cells else empty in
    sep_by1 space cell_parser >>= valid
  in
  let matrix n =
    let valid rows = if List.length rows = n then return rows else empty in
    repeat (row n) [] >>= valid
  in
  let board = natural >>= matrix in
  match board data with
  | Some (n, ast), "" -> n, ast
  | Some _, s' -> failwith "invalid size"
  | None -> failwith "invalid input"

(* Sémantique denotationelle vers un graphe. *)

(* Algorithme de Hopcroft-Karp et vérifications axiomatiques *)

(* Génèse. *)

let () =
  let filename = "echiquier.dat" in
  let data = read_board_file filename in
  let n, ast = parse_board_data data in
  if validate_ast n ast then
    let graph = construct_graph ast in
    (* TODO *)
  else
    failwith "invalid board"

