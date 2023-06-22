(* Function `elem` checks if an element `x` is a member of list `a`. *)
let rec elem x a = match a with h :: t -> h = x || elem x t | [] -> false

(* Function `insert` adds an element `x` to list `a` if it's not already present. *)
let rec insert x a = if not (elem x a) then x :: a else a

(* Function `insert_all` adds all elements from list `xs` to list `a` if they are not already present. *)
let insert_all xs a = List.fold_right insert xs a

(* Function `subset` checks if list `a` is a subset of list `b`. *)
let rec subset a b =
  match a with h :: t -> elem h b && subset t b | [] -> true

(* Function `eq` checks if lists `a` and `b` are equal, i.e., they contain the same elements. *)
let rec eq a b = subset a b && subset b a

(* Function `remove` removes an element `x` from list `a`. *)
let rec remove x a =
  match a with h :: t -> if h = x then t else h :: remove x t | [] -> []

(* Function `diff` computes the difference of lists `a` and `b`, i.e., elements in `a` that are not in `b`. *)
let rec diff a b = match b with [] -> a | h :: t -> diff (remove h a) t

(* Function `minus` is a wrapper for `diff`. *)
let rec minus a b = diff a b

(* Function `union` computes the union of lists `a` and `b`, i.e., all elements that are in `a` or `b`. *)
let rec union a b =
  match a with
  | h :: t -> insert h (union t b)
  | [] -> ( match b with h :: t -> insert h (union [] t) | [] -> [])

(* Function `intersection` computes the intersection of lists `a` and `b`, i.e., all elements that are in both `a` and `b`. *)
let rec intersection a b =
  match a with
  | h :: t -> if elem h b then insert h (intersection t b) else intersection t b
  | [] -> []

(* Function `product` computes the cartesian product of lists `a` and `b`, i.e., all pairs `(x, y)` where `x` is in `a` and `y` is in `b`. *)
let rec product a b =
  let rec product_help x b =
    match b with h :: t -> insert (x, h) (product_help x t) | [] -> []
  in
  match a with h :: t -> union (product_help h b) (product t b) | [] -> []

(* Function `cat` prepends an element `x` to each element of list `a`, producing a list of pairs `(x, y)`. *)
let rec cat x a = match a with [] -> [] | h :: t -> (x, h) :: cat x t
