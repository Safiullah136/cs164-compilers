open Util
open S_exp
open Shared
open Error
open Directive

(** Constants used for tagging values at runtime. *)

let num_shift = 2

let num_mask = 0b11

let num_tag = 0b00

let bool_shift = 7

let bool_mask = 0b1111111

let bool_tag = 0b0011111

type symtab =
  int Symtab.symtab

(** [operand_of_num x] returns the runtime representation of the number [x] as
    an operand for instructions. *)
let operand_of_num : int -> operand =
  fun x ->
    Imm ((x lsl num_shift) lor num_tag)

(** [operand_of_bool b] returns the runtime representation of the boolean [b] as
    an operand for instructions. *)
let operand_of_bool : bool -> operand =
  fun b ->
    Imm (((if b then 1 else 0) lsl bool_shift) lor bool_tag)

let zf_to_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setz (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let setl_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setl (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let stack_address : int -> operand =
  fun index ->
    MemOffset (Imm index, Reg Rsp)

(** [compile_primitive stack_index e prim] produces x86-64 instructions for the
     primitive operation named by [prim] given a stack index of [stack_index];
     if [prim] isn't a valid operation, it raises an error using the
     s-expression [e]. *)
let compile_primitive : int -> s_exp -> string -> directive list =
  fun stack_index e prim ->
    begin match prim with
      | "add1" ->
          [ Add (Reg Rax, operand_of_num 1)
          ]

      | "sub1" ->
          [ Sub (Reg Rax, operand_of_num 1)
          ]

      | "zero?" ->
          [ Cmp (Reg Rax, operand_of_num 0)
          ]
          @ zf_to_bool

      | "num?" ->
          [ And (Reg Rax, Imm num_mask)
          ; Cmp (Reg Rax, Imm num_tag)
          ]
          @ zf_to_bool

      | "not" ->
          [ Cmp (Reg Rax, operand_of_bool false)
          ]
          @ zf_to_bool

      | "+" ->
          [ Add (Reg Rax, stack_address stack_index)
          ]

      | "-" ->
          [ Mov (Reg R8, Reg Rax)
          ; Mov (Reg Rax, stack_address stack_index)
          ; Sub (Reg Rax, Reg R8)
          ]

      | "*" ->
          [ Sar (stack_address stack_index, Imm (num_shift - 1));
            Sar (Reg Rax, Imm (num_shift - 1));
            Mul (stack_address stack_index);
          ]

      | "/" ->
          [ Mov (Reg R8, Reg Rax); 
            Mov (Reg Rax, stack_address stack_index);
            Sar (Reg R8, Imm num_shift);
            Sar (Reg Rax, Imm num_shift);
            Cqo;
            Div (Reg R8);
            Shl (Reg Rax, Imm num_shift)
          ]
          

      | "=" ->
          [ Cmp (stack_address stack_index, Reg Rax)
          ]
          @ zf_to_bool

      | "<" ->
          [ Cmp (stack_address stack_index, Reg Rax)
          ]
          @ setl_bool

      | _ ->
          raise (Stuck e)
    end

(** [compile_expr tab stack_index e] produces x86-64 instructions for the
    expression [e] given a symtab of [tab] and stack index of [stack_index]. *)
let rec compile_expr : symtab -> int -> s_exp -> directive list =
  fun tab stack_index e ->
    begin match e with
      | Num x ->
          [ Mov (Reg Rax, operand_of_num x)
          ]

      | Sym "true" ->
          [ Mov (Reg Rax, operand_of_bool true)
          ]

      | Sym "false" ->
          [ Mov (Reg Rax, operand_of_bool false)
          ]

      | Sym var when Symtab.mem var tab ->
          [ Mov (Reg Rax, stack_address (Symtab.find var tab))
          ]

      | Lst (Sym "case" :: expr :: cases) ->
        let cases = get_cases cases in
        let continue_label = gensym "continue" in
        let case_label = gensym "case" in
        let not_default_label = gensym "not_default" in
        let default_label = gensym "default" in
        let sorted_cases = List.sort (fun l r -> (fst l - fst r)) cases in
        let len = List.length cases in
        let min = fst (List.nth sorted_cases 0) in
        let max = fst (List.nth sorted_cases (len - 1)) in
        let default = fst (List.nth cases (len - 1)) in
        let r = List.range min max in
        let dq_asm = List.concat_map (fun r -> 
          let case_no = if Option.is_some (List.assoc_opt r cases) then r else default in
          [DqLabel (case_label ^ (string_of_int case_no))] ) r
        in
        let cases_asm = List.concat_map (fun case -> [Label (case_label ^ (string_of_int (fst case)))] @ compile_expr tab stack_index (snd case) @ [Jmp continue_label] ) cases
        in
        compile_expr tab stack_index expr
        @ [Cmp (Reg Rax, operand_of_num min)]
        @ [Jl default_label]
        @ [Cmp (Reg Rax, operand_of_num max)]
        @ [Jg default_label]
        @ [Jmp not_default_label]
        @ [Label default_label]
        @ [Mov (Reg Rax, operand_of_num default)]
        @ [Label not_default_label]
        @ [Sub (Reg Rax, operand_of_num min)]
        @ [Shl (Reg Rax, Imm 1)]
        @ [LeaLabel (Reg R8, case_label)]
        @ [ComputedJmp (MemOffset(Reg R8, Reg Rax))]
        @ [Label case_label] 
        @ dq_asm
        @ cases_asm 
        @ [Label continue_label]

      | Lst [Sym "if"; test_expr; then_expr; else_expr] ->
          let else_label =
            gensym "else"
          in
          let continue_label =
            gensym "continue"
          in
          compile_expr tab stack_index test_expr
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je else_label]
            @ compile_expr tab stack_index then_expr
            @ [Jmp continue_label]
            @ [Label else_label]
            @ compile_expr tab stack_index else_expr
            @ [Label continue_label]

      | Lst [Sym "let"; Lst [Lst [Sym var; exp]]; body] ->
          compile_expr tab stack_index exp
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr
                (Symtab.add var stack_index tab)
                (stack_index - 8)
                body

      | Lst [Sym "let"; Lst l; body] ->
          let bindings = get_bindings l
          in
          let len = Symtab.cardinal tab
          in
          let old_tab = tab
          in
          let (tab, asm) = List.fold_left_map (fun tab b -> 
            let stack_i = stack_index - (Symtab.cardinal tab - len) * 8
            in
            ((Symtab.add (fst b) stack_i tab), (compile_expr old_tab stack_i (snd b)) @ [Mov (stack_address stack_i, Reg Rax)])) tab bindings
          in
          ((List.concat asm) @
          compile_expr tab (stack_index - (Symtab.cardinal tab - len) * 8) body)

      | Lst [Sym "and"; arg1; arg2] ->
          compile_expr tab stack_index (Lst [Sym "if"; arg1; arg2; Sym "false"])
          (* let false_label =
            gensym "false"
          in
          compile_expr tab stack_index arg1
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je false_label]
            @ compile_expr tab stack_index arg2
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je false_label]
            @ [Mov (Reg Rax, operand_of_bool true)]
            @ [Label false_label] *)

      | Lst [Sym "or"; arg1; arg2] ->
        compile_expr tab stack_index (Lst [Sym "if"; arg1; arg1; arg2;])
          (* let false_label =
            gensym "false"
          in
          let true_label =
            gensym "true"
          in
          compile_expr tab stack_index arg1
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Jne true_label]
            @ compile_expr tab stack_index arg2
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Jne true_label]
            @ [Jmp false_label]
            @ [Label true_label]
            @ [Mov (Reg Rax, operand_of_bool true)]
            @ [Label false_label] *)

      | Lst [Sym f; arg]->
          compile_expr tab stack_index arg
            @ compile_primitive stack_index e f

      | Lst [Sym f; arg1; arg2] ->
          compile_expr tab stack_index arg1
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr tab (stack_index - 8) arg2
            @ compile_primitive stack_index e f

      | _ ->
          raise (Stuck e)
    end

(** [compile e] produces x86-64 instructions, including frontmatter, for the
    expression [e]. *)
let compile : s_exp -> directive list =
  fun e ->
    [ Global "lisp_entry"
    ; Section "text"
    ; Label "lisp_entry"
    ]
    @ compile_expr Symtab.empty (-8) e
    @ [Ret]
