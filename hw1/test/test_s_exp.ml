open OUnit2
open S_exp
open Lib.Arith

(******************************************************************************)
(* Tests for Task 1 *)

let test_string_of_s_exp : test_ctxt -> unit =
  fun _ ->
    List.iter
      ( fun (expected, input) ->
          assert_equal
            ~printer:(fun s -> s)
            expected
            (string_of_s_exp input)
      )
      [ ("()", Lst [])
      ; ("42", Num 42)
      ; ("a", Sym "a")
      ; ("(a b)", Lst [Sym "a"; Sym "b"])
      ; ("(+ 3 (* 4 5))", Lst [Sym "+"; Num 3; Lst [Sym "*"; Num 4; Num 5]])
      ]

(******************************************************************************)
(* Test runner *)

let _ =
  run_test_tt_main
    ( "s_exp" >:::
        [ "string_of_s_exp" >:: test_string_of_s_exp
        ]
    )
