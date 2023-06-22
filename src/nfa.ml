open List
open Sets

(* Define types for transition and NFA *)
type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma : 's list; (* set of possible inputs for the automaton *)
  qs : 'q list; (* set of states in the automaton *)
  q0 : 'q; (* initial state of the automaton *)
  fs : 'q list; (* set of final states of the automaton *)
  delta : ('q, 's) transition list; (* transition function *)
}

(* Function to convert a string to a character list *)
let explode (s : string) : char list =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(* Function to check if list l1 is a subset of list l2 *)
let contains l1 l2 = intersection l1 l2 != []

(* Function to compute the set of reachable states from a given set of states
   via any single transition. It takes in the NFA, a list of states, and an optional input symbol. *)
let move (nfa : ('q, 's) nfa_t) (qs : 'q list) (s : 's option) : 'q list =
  (* Check if the list of states is a subset of all states in the NFA *)
  if not (subset qs nfa.qs) then []
    (* Check if the input symbol is in the set of all possible inputs for the NFA *)
  else if not (subset (match s with None -> [] | Some s -> [ s ]) nfa.sigma)
  then []
  else
    let rec move' qs s =
      match qs with
      | [] -> []
      | q :: qs' ->
          (* find (q, s, ?) in nfa.delta *)
          let rec move'' qs'' s =
            match qs'' with
            (* move' for q end, go for qs' now! *)
            | [] -> move' qs' s
            | (q', s', q'') :: delta' ->
                if q = q' && s = s' then q'' :: move'' delta' s
                else move'' delta' s
          in
          move'' nfa.delta s
    in
    (* must be unique *)
    List.sort_uniq Stdlib.compare (move' qs s)

(* Function to compute the epsilon closure of a set of states *)
let e_closure (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list =
  if not (contains qs nfa.qs) then []
  else
    let rec e_closure' qs acc =
      match qs with
      | [] -> acc
      | q :: qs' ->
          if subset [ q ] acc then e_closure' qs' acc
          else
            let next_move_with_e = move nfa [ q ] None in
            if List.length next_move_with_e = 0 then e_closure' qs' (q :: acc)
            else e_closure' (qs' @ next_move_with_e) (q :: acc)
    in
    List.sort_uniq Stdlib.compare (e_closure' qs [])

(* Function to check if all transitions in a list are valid *)
let rec check_valid_all nfa actions : bool =
  List.for_all
    (fun a -> List.exists (fun (_, s, _) -> s = Some a) nfa.delta)
    actions

(* Function to check if a given NFA accepts a string *)
let accept (nfa : ('q, char) nfa_t) (s : string) : bool =
  let actions = explode s in
  if not (check_valid_all nfa actions) then false
  else
    let rec accept' actions qs =
      match qs with
      | [] -> false
      | q :: qs' ->
          let e_ALL = e_closure nfa [ q ] in
          if List.length actions = 0 then contains e_ALL nfa.fs
          else
            (* length actions != 0 *)
            let next_move_with_action =
              move nfa e_ALL (Some (List.hd actions))
            in
            if List.length next_move_with_action = 0 then false
            else
              accept' (List.tl actions) next_move_with_action
              || accept' actions (e_closure nfa qs')
    in
    accept' actions [ nfa.q0 ]

(* Functions to get new states, transitions, and finals of the NFA *)
let new_states (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  List.rev
    (List.fold_left
       (fun acc s -> e_closure nfa (move nfa qs (Some s)) :: acc)
       [] nfa.sigma)

let new_trans (nfa : ('q, 's) nfa_t) (qs : 'q list) :
    ('q list, 's) transition list =
  List.rev
    (List.fold_left
       (fun acc s -> (qs, Some s, e_closure nfa (move nfa qs (Some s))) :: acc)
       [] nfa.sigma)

let new_finals (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  if subset qs nfa.fs then [ qs ] else []

(* Functions to find finals, transitions and states of the NFA *)
let rec find_final m states = List.filter (fun x -> contains x m.fs) states

let rec trans m not_visited =
  List.fold_left (fun acc x -> acc @ new_trans m x) [] not_visited

let rec states m visited not_visited =
  match not_visited with
  | [] -> visited
  | h :: t ->
      if not (List.mem h visited) then
        let new_states = new_states m h in
        states m (visited @ [ h ]) (t @ new_states)
      else states m visited t

(* Function to convert an NFA to a DFA *)
let nfa_to_dfa (nfa : ('q, 's) nfa_t) : ('q list, 's) nfa_t =
  let s = states nfa [] [ e_closure nfa [ nfa.q0 ] ] in
  let t = trans nfa s in
  let f = find_final nfa s in
  {
    qs = s;
    sigma = nfa.sigma;
    delta = t;
    q0 = e_closure nfa [ nfa.q0 ];
    fs = f;
  }
