(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast
open System.Collections.Generic

let type_error fmt = throw_formatted TypeError fmt

exception CompositionError of string

exception UnificationError of string

type subst = (tyvar * ty) list

let rec is_typevar_into_type type_var t =
    let rec is_inner = is_typevar_into_type type_var

    match t with
    | TyVar name when type_var = name -> true
    | TyArrow(t1, t2) -> is_inner t1 || is_inner t2
    | TyTuple(head :: tail) -> is_inner head || is_inner (TyTuple tail)
    | _ -> false

// TODO implement this
let compose_subst (s1: subst) (s2: subst) : subst =

    let exists_conflict_subst =
        List.allPairs s1 s2
        |> List.filter (fun (sub1, sub2) -> fst sub1 = fst sub2 && snd sub1 <> snd sub2)
        |> List.isEmpty
        |> not

    if exists_conflict_subst then
        raise (CompositionError "Error while compose substitutions, domains are not disjoint")

    let substitutions = List.distinct s1 @ s2

    let exists_circularity =
        List.allPairs (List.map fst substitutions) (List.map snd substitutions)
        |> List.exists (fun (type_var, t) -> is_typevar_into_type type_var t)

    if exists_circularity then
        raise (CompositionError "Error while compose substitutions, found circularity")

    substitutions

// TODO implement this
let rec unify (t1: ty) (t2: ty) : subst =
    match t1, t2 with
    | TyName c1, TyName c2 when c1 = c2 -> []
    | TyVar type_var, t
    | t, TyVar type_var -> (type_var, t) :: []
    | TyArrow(t1, t2), TyArrow(t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)
    | TyTuple(t1 :: tail), TyTuple(t1' :: tail') -> compose_subst (unify t1 t1') (unify (TyTuple tail) (TyTuple tail'))
    | _ -> raise (UnificationError "Error while unify, some types are incoherent each other")

// TODO implement this
let rec apply_subst (t: ty) (s: subst) : ty =
    match t with
    | TyName constant_type -> TyName constant_type
    | TyVar type_var ->
        let t = List.tryFind (fun elm -> fst elm = type_var) s

        match t with
        | Some s -> snd s
        | None -> TyVar type_var
    | TyArrow(t1, t2) -> TyArrow(apply_subst t1 s, apply_subst t2 s)
    | TyTuple l -> TyTuple(l |> List.map (fun elm -> apply_subst elm s))

let ($) = compose_subst

// TODO implement this
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyVar type_var -> Set.empty.Add(type_var)
    | TyArrow(t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyTuple(head :: tail) -> Set.union (freevars_ty head) (freevars_ty (TyTuple tail))
    | TyTuple [] -> Set.empty

// TODO implement this
let freevars_scheme (Forall(tvs, t)) = Set.difference (freevars_ty t) tvs

// TODO implement this
let rec freevars_scheme_env (env: scheme env) =
    // env : (string * (Set<tyvar> * ty)) list
    match env with
    | head_scheme :: tail -> Set.union (freevars_scheme (snd head_scheme)) (freevars_scheme_env tail)
    | [] -> Set.empty


// basic environment: add builtin operators at will
//

let gamma0 =
    [ ("+", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("-", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("*", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("/", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("<", TyArrow(TyInt, TyArrow(TyInt, TyBool))) ]

// type inference
//

let rec typeinfer_expr (env: scheme env) (e: expr) : ty * subst =
    match e with
    | Lit(LInt _) -> TyInt, []
    | Lit(LBool _) -> TyBool, []
    | Lit(LFloat _) -> TyFloat, []
    | Lit(LString _) -> TyString, []
    | Lit(LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | BinOp(e1, op, e2) -> typeinfer_expr env (App(App(Var op, e1), e2))

    | IfThenElse(e1, e2, Some e3) ->
        // TODO optionally you can follow the original type inference rule and apply/compose substitutions incrementally (see Advanced Notes on ML, Table 4, page 5)
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let t2, s3 = typeinfer_expr env e2
        let t3, s4 = typeinfer_expr env e3
        let s5 = unify t2 t3
        let s = s5 $ s4 $ s3 $ s2 $ s1
        apply_subst t2 s, s




    // TODO complete this implementation

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// type checker
//
// optionally, a simple type checker (without type inference) could be implemented
// you might start implementing this for simplicity and eventually write the type inference once you gain familiarity with the code

let rec typecheck_expr (env: ty env) (e: expr) : ty =
    match e with
    | Lit(LInt _) -> TyInt
    | Lit(LFloat _) -> TyFloat
    | Lit(LString _) -> TyString
    | Lit(LChar _) -> TyChar
    | Lit(LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        try
            lookup env x
        with :? KeyNotFoundException ->
            type_error "typecheck_expr: variable identifier not defined (%s)" x

    | Let(x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Let(x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1

        if t <> t1 then
            type_error "type %O differs from type %O in let-binding" t1 t

        let env' = (x, t1) :: env
        typecheck_expr env' e2

    // TODO: aggiungere typechecking del let rec

    | Lambda(x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow(t, te)

    // TODO implementare il type checker per lambda non annotate
    | Lambda(x, None, e) -> type_error "unannotated lambdas are not supported by the type checker"

    | App(e1, e2) ->
        let t2 = typecheck_expr env e2

        match typecheck_expr env e1 with
        | TyArrow(ta, tb) ->
            if ta <> t2 then
                type_error "argument has type %O while function parameter has type %O in application" t2 ta

            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    | IfThenElse(e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %O" t1

        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3

        if t2 <> t3 then
            type_error "then and else branches have different types: %O and %O" t2 t3

        t2

    | IfThenElse(condition, expression, None) ->
        let t1 = typecheck_expr env condition

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %O" t1

        typecheck_expr env expression

    | BinOp(e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match (op, t1, t2) with
        | ("+", TyString, TyString) -> TyString
        | (_, TyInt, TyInt) -> TyInt
        | (_, TyInt, TyFloat) -> TyFloat
        | (_, TyFloat, TyInt) -> TyFloat
        | (_, TyFloat, TyFloat) -> TyFloat
        | (_, TyInt, _) -> type_error "right hand of (%s) operator is not an int or float: %O" op t2
        | (_, TyFloat, _) -> type_error "right hand of (%s) operator is not an int or float: %O" op t2
        | (_, _, TyInt) -> type_error "left hand of (%s) operator is not an int or float: %O" op t1
        | (_, _, TyFloat) -> type_error "left hand of (%s) operator is not an int or float: %O" op t1
        | ("+", TyString, _) -> type_error "right hand of (%s) operator is not a string: %O" op t2
        | _ -> type_error "the operator %s is not defined for the given types: %O - %O" op t1 t2

    | BinOp(left_expr, ("%" as op), right_expr) ->
        let left_type = typecheck_expr env left_expr

        if left_type <> TyInt then
            type_error "left hand of (%s) operator is not an int: %O" op left_type

        let right_type = typecheck_expr env right_expr

        if right_type <> TyInt then
            type_error "left hand of (%s) operator is not an int: %O" op right_type

        TyInt

    | BinOp(e1, ("=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        if t1 <> t2 then
            type_error "left and right hands of operator %s are different: %O and %O" op t1 t2

        TyBool

    | BinOp(e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match (t1, t2) with
        | (TyString, TyString) -> TyBool
        | (TyBool, TyBool) -> TyBool
        | (TyInt, TyInt) -> TyBool
        | (TyInt, TyFloat) -> TyBool
        | (TyFloat, TyInt) -> TyBool
        | (TyFloat, TyFloat) -> TyBool
        | (TyInt, _) -> type_error "right hand of (%s) operator is not an int or float: %O" op t2
        | (TyFloat, _) -> type_error "right hand of (%s) operator is not an int or float: %O" op t2
        | (TyString, _) -> type_error "right hand of (%s) operator is not a string: %O" op t2
        | (TyBool, _) -> type_error "right hand of (%s) operator is not a bool: %O" op t2
        | _ -> type_error "the operator %s is not defined for the given types: %O - %O" op t1 t2

    | BinOp(left_expr, ("and" | "or" as op), right_expr) ->
        let left_type = typecheck_expr env left_expr

        if left_type <> TyBool then
            type_error "left hand of (%s) operator is not a bool: %O" op left_type

        let right_type = typecheck_expr env right_expr

        if right_type <> TyBool then
            type_error "left hand of (%s) operator is not a bool: %O" op right_type

        TyBool

    | BinOp(_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp("not", e) ->
        let t = typecheck_expr env e

        if t <> TyBool then
            type_error "operand of not-operator is not a bool: %O" t

        TyBool

    | UnOp("-", expression) ->
        let expr_type = typecheck_expr env expression

        if expr_type <> TyInt && expr_type <> TyFloat then
            type_error "operand of minus operator is not of type int or float: %O" expr_type

        expr_type

    | UnOp(op, _) -> type_error "typecheck_expr: unsupported unary operator (%s)" op

    | Tuple es -> TyTuple(List.map (typecheck_expr env) es)


    // TODO optionally complete this implementation

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
