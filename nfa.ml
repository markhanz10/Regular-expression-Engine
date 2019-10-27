open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)
let rec delta_lookup state delt = List.filter (fun (a, b, c) -> a = state) delt

let rec edge_filter edgs_lst s_opt = List.fold_left (fun acc (a, b, c) -> if b = s_opt then c::acc else acc) [] edgs_lst

let rec epsilon_lookup state delt = List.filter (fun (a, b, c) -> b = state) delt


let insert_all lst1 lst2 =
  List.fold_left (fun acc y -> Sets.insert y acc) lst2 lst1

  let rec move_abstract nfa qs2 s fin lookup =
    match qs2 with
    | [] -> fin
    | h::t -> let edgs = lookup h nfa.delta in
    let next_states = edge_filter edgs s in
    move_abstract nfa t s (insert_all next_states fin) lookup

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
    move_abstract nfa qs s [] delta_lookup



let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec aux delta qs2 fin =
  match delta with
  |[] -> fin
  | h::t ->
  (match h with
  | (a, b, c) -> let fin = if(List.mem a qs2) && b = None then (if (List.mem c fin) then fin else c::fin) else fin in
  aux t qs fin) in
  aux nfa.delta qs qs

let rec accept_aux nfa chars =
  let final_lst = List.fold_left (fun acc x -> (e_closure nfa (move nfa acc (Some x)))) (e_closure nfa [nfa.q0]) chars in
  List.fold_left (fun acc x -> if List.mem x nfa.fs then true else acc) false final_lst


let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let lst = explode s in
  accept_aux nfa lst


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)





let epsilon_move nfa qs s: 'q list = move_abstract nfa qs s [] delta_lookup



let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.fold_left (fun acc x -> (e_closure nfa (epsilon_move nfa qs (Some x)))::acc) [] nfa.sigma



let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.fold_left (fun acc x -> x::acc) [] (List.map (fun y -> (qs, (Some y), (e_closure nfa (move nfa qs (Some y))))) nfa.sigma)



let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.fold_left (fun acc x -> if List.mem x nfa.fs then [qs] else acc) [] qs


let rec contains x lst =
  match lst with
  |[] -> false
  |h::t -> if Sets.eq x h then true else contains x t

let rec nfa_dfa_aux nfa dfa work marked =
  match work with
  |[] -> dfa
  |h::t -> let e = new_states nfa h in
  let m = List.fold_left (fun acc x -> if contains x marked then dfa.qs else x::dfa.qs) dfa.qs e in
  let r = (new_trans nfa h) in
  let dfa2 = {qs = union e dfa.qs; sigma = dfa.sigma; delta = union r dfa.delta; q0 = dfa.q0; fs = union (new_finals nfa h) dfa.fs} in
  (nfa_dfa_aux nfa dfa2 (diff (union t (diff e dfa.qs)) [[]]) (h::marked))

let nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
    nfa_dfa_aux nfa dfa work []



let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
let q0' = (e_closure nfa [nfa.q0]) in
let dfa = {qs = (new_states nfa [nfa.q0]); sigma = nfa.sigma;
  delta = (new_trans nfa q0'); q0 = (e_closure nfa q0'); fs = (new_finals nfa q0');} in
  nfa_to_dfa_step nfa dfa (new_states nfa [nfa.q0])
