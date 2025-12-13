let epsilon : float =
  0.001

let close : float -> float -> bool =
  fun a b ->
    Float.abs (a -. b) < epsilon

(******************************************************************************)
(* Task 1 *)

(* Task 1.1 *)

(** [square x] is the square of the number [x]. *)
let square : float -> float =
  fun x ->
    (* failwith "TODO" *)
    x *. x

(******************************************************************************)
(* Task 2 *)

(* Task 2.1 *)

(** [babylonian_step n guess] is the revised guess for the square root of [n]
    produced by a step of the Babylonian method given the current [guess]. **)
let babylonian_step : float -> float -> float =
  fun n guess ->
    (* failwith "TODO" *)
    guess +. ( (n -. guess *. guess) /. (2. *. guess))

(* Task 2.2 *)

(** [babylonian n guess] is a close enough estimate for the square root of [n]
    produced by the Babylonian method given an initial [guess]. **)
let rec babylonian : float -> float -> float =
  fun n guess ->
    (* failwith "TODO" *)
    if close (n) (guess*.guess) then guess else babylonian (n) (babylonian_step (n) (guess))

(******************************************************************************)
(* Task 3 *)

(* Task 3.1 *)

(** [newton_step f f' guess] is the revised guess for a root of [f]
    produced by a step of Newton's method given the current [guess]. **)
let newton_step : (float -> float) -> (float -> float) -> float -> float =
  fun f f' guess ->
    (* failwith "TODO" *)
    guess -. ( (f (guess)) /. (f' (guess)) )

(* Task 3.2 *)

(** [newton f f' guess] is a close enough estimate for a root of [f]
    produced by Newton's method given an initial [guess]. **)
let rec newton : (float -> float) -> (float -> float) -> float -> float =
  fun f f' guess ->
    (* failwith "TODO" *)
    if close (f (guess)) (0.) then guess else newton (f) (f') (newton_step (f) (f') (guess)) 
