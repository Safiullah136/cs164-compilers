open Tokens
open Ast

exception ParseError of token list

(** [consume_token t toks] ensures that the head of [toks] is [t]. If it is, it
    returns the tail of [toks]. Otherwise, it raises a [ParseError].  *)
let consume_token : token -> token list -> token list =
  fun t toks ->
    begin match toks with
      | t' :: tail when t = t' ->
          tail

      | _ ->
          raise (ParseError toks)
    end

(** [call_or_prim f args toks] returns an expression corresponding to the
    application of [f] to [args]. If [f] is a primitive, the AST node for this
    will application will be [Prim0], [Prim1], or [Prim2]; otherwise, it will be
    [Call]. If the length of [args] does not match the arity of [f], this
    function will throw [ParseError toks]. *)
let call_or_prim : string -> expr list -> token list -> expr =
  fun f args toks ->
  begin match f with
    | "read_num" ->
        begin match args with
          | [] -> Prim0 ReadNum
          | _ -> raise (ParseError toks)
        end

    | "newline" ->
        begin match args with
          | [] -> Prim0 Newline
          | _ -> raise (ParseError toks)
        end

    | "add1" ->
        begin match args with
          | [arg] -> Prim1 (Add1, arg)
          | _ -> raise (ParseError toks)
        end

    | "sub1" ->
        begin match args with
          | [arg] -> Prim1 (Sub1, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_zero" ->
        begin match args with
          | [arg] -> Prim1 (IsZero, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_num" ->
        begin match args with
          | [arg] -> Prim1 (IsNum, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_pair" ->
        begin match args with
          | [arg] -> Prim1 (IsPair, arg)
          | _ -> raise (ParseError toks)
        end

    | "is_empty" ->
        begin match args with
          | [arg] -> Prim1 (IsEmpty, arg)
          | _ -> raise (ParseError toks)
        end

    | "left" ->
        begin match args with
          | [arg] -> Prim1 (Left, arg)
          | _ -> raise (ParseError toks)
        end

    | "right" ->
        begin match args with
          | [arg] -> Prim1 (Right, arg)
          | _ -> raise (ParseError toks)
        end

    | "print" ->
        begin match args with
          | [arg] -> Prim1 (Print, arg)
          | _ -> raise (ParseError toks)
        end

    | "pair" ->
        begin match args with
          | [arg1; arg2] -> Prim2 (Pair, arg1, arg2)
          | _ -> raise (ParseError toks)
        end

    | _ ->
        Call (f, args)
  end

let rec parse_program : token list -> program =
  fun toks ->
    let defns, toks = parse_defns toks in
    let body, toks = parse_expr toks in
    if List.length toks <> 0 then
      raise (ParseError toks)
    else
      {defns; body}

and parse_params : token list -> string list * token list = 
  fun toks -> 
    match toks with
    | RPAREN :: toks -> ([], toks)
    | COMMA :: ID x :: toks | (ID x) :: toks -> 
      let params, toks = parse_params toks in 
      ([x] @ params, toks)
    | _ -> raise (ParseError toks)
  
and parse_defn : token list -> defn * token list =
  fun toks -> 
    match toks with
    | (ID name) :: LPAREN :: toks ->
      let args, toks = parse_params toks in
      (match toks with
      | EQ :: toks -> 
        let body, toks = parse_expr toks in
        ({name; args; body}, toks)
      | _ -> raise (ParseError toks))
    | _ -> raise (ParseError toks)

and parse_defns : token list -> defn list * token list =
  fun toks ->
    match toks with 
    | FUNCTION :: toks  -> 
        let defn, toks = parse_defn toks in
        let defns, toks = parse_defns toks in
        ([defn] @ defns, toks) 
    | _ -> ([], toks)

and parse_args : token list -> expr list * token list = 
  fun toks -> 
    match toks with
    | RPAREN :: toks -> ([], toks)
    | COMMA :: toks | toks -> 
      let arg_expr, toks = parse_expr toks in 
      let rest_args_expr, toks = parse_args toks in
        ([arg_expr] @ rest_args_expr, toks)

and parse_term : token list -> expr * token list =
  fun toks ->
    match toks with
    | ID x :: LPAREN :: toks -> 
      let args, toks = parse_args toks in
        (call_or_prim x args toks, toks)
    | ID x :: toks -> 
      (match x with
      | "true" -> (True, toks)
      | "false" -> (False, toks)
      | "nil" -> (Nil, toks)
      | _ -> (Var x, toks)
      )
    | NUM n :: toks -> (Num n, toks) 
    | LPAREN :: toks -> 
      let ex, toks = parse_expr toks in
        (match toks with
        | RPAREN :: toks -> (ex, toks)
        | _ -> raise (ParseError toks)
        )
    | _ -> raise (ParseError toks)

and parse_infix2 : token list -> expr * token list =
  fun toks ->
    let term_expr, toks = parse_term toks in
      match toks with 
      | PLUS :: toks -> 
        let term2_expr, toks = parse_infix2 toks in
          (Prim2 (Plus, term_expr, term2_expr), toks)
      | MINUS :: toks ->
        let term2_expr, toks = parse_infix2 toks in
          (Prim2 (Minus, term_expr, term2_expr), toks)
      | _ -> (term_expr, toks)

and parse_infix1 : token list -> expr * token list =
  fun toks ->
    let infix2_expr, toks = parse_infix2 toks in
      match toks with
      | EQ :: toks -> 
        let infix1_expr, toks = parse_infix1 toks in
        (Prim2 (Eq, infix2_expr, infix1_expr), toks) 
      | LT :: toks -> 
        let infix1_expr, toks = parse_infix1 toks in
        (Prim2 (Lt, infix2_expr, infix1_expr), toks) 
      | _ -> (infix2_expr, toks)

and parse_rest_seq : token list -> expr * token list =
  fun toks -> 
    (match toks with 
    | SEMICOLON :: toks -> 
      let infix1_expr, toks = parse_infix1 toks in
      let seq_expr, toks = parse_rest_seq toks in
      (match seq_expr with
      | Do l -> (Do ([infix1_expr] @ l), toks) 
      | _ -> (Do [infix1_expr], toks)
      )
    | _ -> (Nil, toks))
and parse_seq : token list -> expr * token list =
  fun toks ->
    let infix1_expr_1, toks = parse_infix1 toks in
    let rest_seq, toks = parse_rest_seq toks in
    (match rest_seq with 
    | Do l -> (Do ([infix1_expr_1] @ l), toks)
    | _ -> (infix1_expr_1, toks)
    )

and parse_expr : token list -> expr * token list =
  fun toks ->
    match toks with
    | IF :: toks ->
      let test_expr, toks = parse_expr toks in 
        (match toks with 
        | THEN :: toks -> 
          let then_expr, toks = parse_expr toks in
            (match toks with 
            | ELSE :: toks -> 
              let else_expr, toks = parse_expr toks in
                (If (test_expr, then_expr, else_expr), toks)
            | _ -> raise (ParseError toks)) 
        | _ -> raise (ParseError toks))

    | LET :: ID x :: EQ :: toks ->
      let value_expr, toks = parse_expr toks in 
      (match toks with 
      | IN :: toks -> 
        let let_body_expr, toks = parse_expr toks in
          (Let (x, value_expr, let_body_expr), toks) 
      | _ -> raise (ParseError toks)
      ) 

    | _ -> parse_seq toks
    

let parse : string -> program =
  fun s ->
    s
      |> tokenize
      |> parse_program
