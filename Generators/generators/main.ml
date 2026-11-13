(* understanding the coding scheme for enumerating and generating theories*)

open Base
open Stdio

(*
enumerate_theory : Integer -> Integer
*)
(* A theory is the list of arities of its operations (after the carrier
   "a : type"). E.g. [0; 0] is

     "1(1|0)(2|0)"
     a : type
     b : a
     c : a
*)
type theory1 = int list

(* size: the k-th operation (1-indexed) with arity t costs k + t + 1 *)
let sze (ts : theory1) : int =
(* Haskell to ocaml (under Base library definition) translation
  sum                            $ zipWith (+)              [1..]    (map ((+1).toInteger) ts)*)
  List.sum (module Int) ~f:Fn.id (List.mapi ~f:(fun i t -> (i + 1) + (t + 1)) ts)

(* all theories of size exactly n *)
let enumerate (n : int) : theory1 list =
  (* k = position/name of the next operation, r = remaining size budget *)
  let rec go (k : int) (r : int) : theory1 list =
    if r = 0 then [ [] ]
    else if r < k + 1 then []
    else
      List.concat_map (List.range 0 (r - k)) ~f:(fun t ->
          List.map (go (k + 1) (r - (k + 1 + t))) ~f:(fun rest -> t :: rest))
  in
  if n < 0 then [] else go 1 n

(* render as "1(1|t1)(2|t2)..." *)
(* leading 1 is for current 1 base type *)
let to_code (ts : theory1) : string =
  "1" ^ String.concat (List.mapi ts ~f:(fun i t -> "(" ^ Int.to_string (i + 1) ^ "|" ^ Int.to_string t ^ ")"))

let enumerate_theory (n : int) : string list = List.map (enumerate n) ~f:to_code
let enumerates (n : int) : theory1 list  = List.concat_map (List.range 1 (n+1)) ~f:enumerate
let enumerate_theories (n : int) : string list = List.concat_map (List.range 1 (n+1)) ~f:enumerate_theory
let () =
  let n =
    match Sys.get_argv () with
    | [| _; s |] -> Int.of_string s
    | _ -> 5
  in
  List.iter (enumerate_theories n) ~f:print_endline;
  printf "-- with sizes --\n";
  List.iter (enumerates n) ~f:(fun ts ->
      printf "%s   (size %d)\n" (to_code ts) (sze ts))

(*
I/0 is annoying try, but I only need it to get new ints
before runtime
let () =
  Out_channel.output_string "Enter a natural:";
  Out_channel.flush stdout;

  match In_channel
*)
