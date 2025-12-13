open OUnit2
open Hw0

let assert_close : float -> float -> unit =
  fun a b ->
    assert_equal ~cmp:close ~printer:string_of_float a b

let test_square : test_ctxt -> unit =
  fun _ ->
    assert_close 4.0 (square 2.0);
    assert_close 4.0 (square (-2.0));
    assert_close 1.21 (square 1.1)

let test_babylonian_step : test_ctxt -> unit =
  fun _ ->
    assert_close 10.0 (babylonian_step 100.0 10.0);
    assert_close 12.5 (babylonian_step 100.0 5.0);
    assert_close 35.6 (babylonian_step 612.0 10.0);
    assert_close 26.395 (babylonian_step 612.0 35.6)

let test_babylonian : test_ctxt -> unit =
  fun _ ->
    assert_close 10.0 (babylonian 100.0 50.0);
    assert_close 6.0 (babylonian 36.0 18.0);
    assert_close 6.0 (babylonian 36.0 72.0)

let test_newton_step : test_ctxt -> unit =
  fun _ ->
    (* Newton step is Babylonian step for sqrt *)

    List.iter
      ( fun (n, guess) ->
          assert_close
            (babylonian_step n guess)
            (newton_step (fun x -> (x *. x) -. n) (fun x -> 2.0 *. x) guess)
      )
      [(100.0, 10.0); (100.0, 5.0); (612.0, 10.0); (612.0, 35.6)];

    (* Find solution to cos x = x^3 *)

    let step =
      newton_step
        (fun x -> Float.cos x -. (x *. x *. x))
        (fun x -> -.Float.sin x -. (3.0 *. x *. x))
    in

    assert_close 1.112 (step 0.5);
    assert_close 0.909 (step 1.112);
    assert_close 0.867 (step 0.909)

let test_newton : test_ctxt -> unit =
  fun _ ->
    (* Newton is Babylonian for sqrt *)

    List.iter
      ( fun (n, guess) ->
          assert_close
            (babylonian n guess)
            (newton (fun x -> (x *. x) -. n) (fun x -> 2.0 *. x) guess)
      )
      [(100.0, 10.0); (100.0, 5.0); (612.0, 10.0); (612.0, 35.6)];

    (* Find solution to cos x = x^3 *)

    assert_close
      0.8654
      ( newton
          (fun x -> Float.cos x -. (x *. x *. x))
          (fun x -> -.Float.sin x -. (3.0 *. x *. x))
          5.0
      )

(* "Main" expression *)
let _ =
  run_test_tt_main
    ( "hw0" >:::
        [ "square" >:: test_square
        ; "babylonian_step" >:: test_babylonian_step
        ; "babylonian" >:: test_babylonian
        ; "newton" >:: test_newton
        ; "newton_step" >:: test_newton_step
        ]
    )
