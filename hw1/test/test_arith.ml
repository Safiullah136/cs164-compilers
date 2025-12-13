open OUnit2
open S_exp
open Lib.Arith

(******************************************************************************)
(* Tasks *)

(* Task 2.1 *)

let test_is_bin : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    assert_bool "((2)) is invalid." (not (is_bin (parse "((2))")));
    assert_bool "41 is valid." (is_bin (parse "41"));
    assert_bool "(+ 2 3) is valid." (is_bin (parse "(+ 2 3)"));
    assert_bool "(* 4 5) is valid." (is_bin (parse "(* 4 5)"));
    assert_bool "(+ (* 2 3) 5) is valid." (is_bin (parse "(+ (* 2 3) 5)"));
    assert_bool "(+ (2) 5) is invalid." (not (is_bin (parse "(+ (2) 5)")));
    assert_bool "(+ 5 (* 2 3)) is valid." (is_bin (parse "(+ 5 (* 2 3))"));
    assert_bool "(= 6 5) is invalid." (not (is_bin (parse "(= 6 5)")))

(* Task 2.3 *)

let test_interp_bin : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    assert_equal ~printer:string_of_int 5 (interp_bin (parse "(+ 4 1)"));
    assert_equal ~printer:string_of_int 5 (interp_bin (parse "5"));
    assert_equal ~printer:string_of_int 6 (interp_bin (parse "(* 2 3)"));
    assert_equal ~printer:string_of_int 11 (interp_bin (parse "(+ 3 (* 2 4))"));
    assert_equal ~printer:string_of_int 8 (interp_bin (parse "(* (+ 1 3) 2)"));
    assert_equal ~printer:string_of_int 24 (interp_bin (parse "(* (+ 1 3) (* 3 2))"));
    
    assert_raises (Stuck (parse "(5)")) (fun () -> interp_bin (parse "(5)"));
    assert_raises (Stuck (parse "(2)")) (fun () -> interp_bin (parse "(+ (2) 5)"));
    assert_raises (Stuck (parse "(= 6 5)")) (fun () -> interp_bin (parse "(= 6 5)"))

(* Task 2.5 *)

let test_interp_instr : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    assert_equal [5] (interp_instr [] (Push 5));
    assert_equal [8] (interp_instr [5; 3] (Add));
    assert_equal [8] (interp_instr [4; 2] (Mul));
    assert_equal [8; 5] (interp_instr [8] (Push 5));
    assert_equal [8; 6] (interp_instr [8; 2; 4] (Add));
    assert_equal [8; 6] (interp_instr [8; 3; 2] (Mul));

    assert_raises (ShortStack [5]) (fun () -> interp_instr [5] (Add));
    assert_raises (ShortStack []) (fun () -> interp_instr [] (Add))

let test_interp_program : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    assert_equal 5 (interp_program [Push 5]);

    assert_equal 8 (interp_program [Push 5; Push 3; Add]);
    assert_equal 14 (interp_program [Push 5; Push 3; Add; Push 6; Add]);
    assert_equal 12 (interp_program [Push 5; Push 3; Push 4; Add; Add]);
    assert_equal 14 (interp_program [Push 5; Push 3; Add; Push 4; Push 2; Add; Add]);

    assert_equal 15 (interp_program [Push 5; Push 3; Mul]);
    assert_equal 30 (interp_program [Push 5; Push 3; Mul; Push 2; Mul]);
    assert_equal 60 (interp_program [Push 5; Push 3; Push 4; Mul; Mul]);
    assert_equal 30 (interp_program [Push 5; Push 3; Mul; Push 1; Push 2; Mul; Mul]);

    assert_equal 16 (interp_program [Push 5; Push 3; Add; Push 2; Mul]);
    assert_equal 17 (interp_program [Push 5; Push 3; Mul; Push 2; Add]);
    assert_equal 35 (interp_program [Push 5; Push 3; Push 4; Add; Mul]);
    assert_equal 17 (interp_program [Push 5; Push 3; Push 4; Mul; Add]);
    assert_equal 24 (interp_program [Push 5; Push 3; Add; Push 1; Push 2; Add; Mul]);
    assert_raises (ShortStack [8]) (fun () -> interp_program [Push 5; Push 3; Add; Mul]);
    assert_raises (ShortStack []) (fun () -> interp_program [Mul])  

(* Task 2.7 *)

let test_compile_bin : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    assert_equal [Push 4; Push 1; Add] (compile_bin (parse "(+ 4 1)"));
    assert_equal [Push 5] (compile_bin (parse "5"));
    assert_equal [Push 2; Push 3; Mul] (compile_bin (parse "(* 2 3)"));
    assert_equal [Push 3; Push 2; Push 4; Mul; Add] (compile_bin (parse "(+ 3 (* 2 4))"));
    assert_equal [Push 1; Push 3; Add; Push 2; Mul] (compile_bin (parse "(* (+ 1 3) 2)"));
    assert_equal [Push 1; Push 3; Add; Push 3; Push 2; Mul; Mul] (compile_bin (parse "(* (+ 1 3) (* 3 2))"));
    
    assert_raises (Stuck (parse "(5)")) (fun () -> compile_bin (parse "(5)"));
    assert_raises (Stuck (parse "(2)")) (fun () -> compile_bin (parse "(+ (2) 5)"));
    assert_raises (Stuck (parse "(= 6 5)")) (fun () -> compile_bin (parse "(= 6 5)"))

(* Task 2.9 *)

let test_compile_versus_interp_bin : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    let exps = ["(+ 4 1)"; "5"; "(* 2 3)"; "(+ 3 (* 2 4))"; "(* (+ 1 3) 2)"; "(* (+ 1 3) (* 3 2))"] in
    assert_bool "Diff Test Failed." (List.for_all (fun prog -> (interp_program (compile_bin (parse prog)) == interp_bin (parse prog) ) ) exps)


(* Task 3.3 *)

let test_variadic : test_ctxt -> unit =
  fun _ ->
    (* failwith "TODO" *)
    let exps = ["(+ 4 1)"; "5"; "(* 2 3)"; "(+ 3 (* 2 4))"; "(* (+ 1 3) 2)"; "(* (+ 1 3) (* 3 2))"; "(+ 5 4 3 2 1)"; "(* 1 2 3 (+ 4 5))"; "(+ 2 3 (* 1 2 (+ 3 4)))"] in
    assert_bool "Diff Test Failed." (List.for_all (fun prog -> (interp_bin (desugar_variadic (parse prog)) == interp_variadic (parse prog) ) ) exps)


(******************************************************************************)
(* Test runner *)

let _ =
  run_test_tt_main
    ( "arith tests" >:::
        [ "is_bin" >:: test_is_bin
        ; "interp_bin" >:: test_interp_bin
        ; "interp_instr" >:: test_interp_instr
        ; "interp_program" >:: test_interp_program
        ; "compile_bin" >:: test_compile_bin
        ; "compiling vs. interpreting" >:: test_compile_versus_interp_bin
        ; "variadic" >:: test_variadic
        ]
    )
