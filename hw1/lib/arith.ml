open S_exp

(******************************************************************************)
(* Task 1 *)

(* Task 1.1 *)

let rec string_of_s_exp : s_exp -> string =
  fun exp ->
    (* failwith "TODO" *)
    match exp with 
    | Num n -> string_of_int (n)
    | Sym s -> s
    | Lst l -> "(" ^ (String.concat " " (List.map (string_of_s_exp) l)) ^ ")"

(******************************************************************************)
(* Task 2 *)

(* Task 2.1 is found in `test/test_arith.ml` *)

(* Task 2.2 *)

let rec is_bin : s_exp -> bool =
  fun exp ->
    (* failwith "TODO" *)
    match exp with
    | Num _ -> true
    | Lst [Sym "+"; e1; e2] -> (is_bin e1) && (is_bin e2)
    | Lst [Sym "*"; e1; e2] -> (is_bin e1) && (is_bin e2)
    | _ -> false

(* Task 2.3 is found in `test/test_arith.ml` *)

(* Task 2.4 *)

exception Stuck of s_exp

let rec interp_bin : s_exp -> int =
  fun exp ->
    (* failwith "TODO" *)
    match exp with 
    | Num n -> n
    | Lst [Sym "+"; e1; e2] -> (interp_bin e1) + (interp_bin e2)
    | Lst [Sym "*"; e1; e2] -> (interp_bin e1) * (interp_bin e2)
    | _ -> raise (Stuck exp)


(* Task 2.5 is found in `test/test_arith.ml` *)

(* Task 2.6 *)

type instr
  = Push of int
  | Add
  | Mul

type stack =
  int list

exception ShortStack of stack

let rec pop_last_two : stack -> (stack * (int * int)) = 
  fun stack -> 
    match stack with 
    | [] -> raise (ShortStack stack)
    | [_] -> raise (ShortStack stack)
    | [n1; n2] -> ([], (n1, n2))
    | hd :: tl -> (
      let temp = (pop_last_two tl) in
      (hd :: (fst temp), snd temp) )

let interp_instr : stack -> instr -> stack =
  fun stack instr ->
    (* failwith "TODO" *)
    match instr with 
    | Push n -> stack @ [n]
    | Add -> (
      let temp = pop_last_two stack in
      (fst temp) @ [fst (snd temp) + snd (snd temp)]
      )
    | Mul -> (
      let temp = pop_last_two stack in
      (fst temp) @ [fst (snd temp) * snd (snd temp)]
      )

let interp_program : instr list -> int =
  fun instrs ->
    (* failwith "TODO" *)
    (List.fold_left (interp_instr) [] instrs) |> List.hd

(* Task 2.7 is found in `test/test_arith.ml` *)

(* Task 2.8 *)

let rec compile_bin : s_exp -> instr list =
  fun exp ->
    (* failwith "TODO" *)
    match exp with 
    | Num n -> [Push n]
    | Lst [Sym "+"; e1; e2] -> compile_bin e1 @ compile_bin e2 @ [Add]
    | Lst [Sym "*"; e1; e2] -> compile_bin e1 @ compile_bin e2 @ [Mul]
    | _ -> raise (Stuck exp)

(* Task 2.9 is found in `test/test_arith.ml` *)

(******************************************************************************)
(* Task 3 *)

(* Task 3.1 *)

let rec desugar_variadic : s_exp -> s_exp =
  fun exp ->
    (* failwith "TODO" *)
    match exp with 
    | Num n -> Num n
    | Lst (Sym "+" :: l) -> List.fold_right (fun exp s -> Lst [Sym "+"; (desugar_variadic exp); s]) l (Num 0) 
    | Lst (Sym "*" :: l) -> List.fold_right (fun exp s -> Lst [Sym "*"; (desugar_variadic exp); s]) l (Num 1) 
    | _ -> raise (Stuck exp)

(* Task 3.2 *)

let rec interp_variadic : s_exp -> int =
  fun exp ->
    (* failwith "TODO" *)
    match exp with 
    | Num n -> n
    | Lst (Sym "+" :: l) -> List.fold_left (+) (0) (List.map (fun e -> interp_variadic e) l)
    | Lst (Sym "*" :: l) -> List.fold_left ( * ) (1) (List.map (fun e -> interp_variadic e) l)
    | _ -> raise (Stuck exp)

(* Task 3.3 is found in `test/test_arith.ml` *)
