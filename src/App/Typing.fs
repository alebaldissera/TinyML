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

let mutable type_variable_index = 0

let create_type_variable () =
    type_variable_index <- type_variable_index + 1
    TyVar type_variable_index

type subst = (tyvar * ty) list

let mutable tyvar_counter = 0

let generate_tyvar () =
    tyvar_counter <- tyvar_counter + 1
    TyVar(tyvar_counter)

let rec is_typevar_into_type type_var t =
    let rec is_inner = is_typevar_into_type type_var

    match t with
    | TyVar name when type_var = name -> true
    | TyArrow(t1, t2) -> is_inner t1 || is_inner t2
    | TyTuple(head :: tail) -> is_inner head || is_inner (TyTuple tail)
    | _ -> false

let rec apply_subst (t: ty) (s: subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar type_var ->
        try
            s |> List.find (fun (subst_ty_var, _) -> subst_ty_var = type_var) |> snd
        with :? KeyNotFoundException ->
            t
    | TyArrow(t1, t2) -> TyArrow(apply_subst t1 s, apply_subst t2 s)
    | TyTuple l -> TyTuple(l |> List.map (fun elm -> apply_subst elm s))

// TODO implement this
let compose_subst (s1: subst) (s2: subst) : subst =

    // application of the first one to the codomain of the second one
    let composed_subst =
        (List.map (fun (type_var, t) -> (type_var, apply_subst t s1)) s2) @ s1
        |> List.distinct

    let conflicts =
        List.allPairs composed_subst composed_subst
        |> List.tryFind (fun (sub1, sub2) -> fst sub1 = fst sub2 && snd sub1 <> snd sub2)

    match conflicts with
    | Some((tyvar, tau1), (_, tau2)) ->
        raise (
            CompositionError(
                sprintf
                    "Error while compose substitutions. Variable type %s maps to type %s and %s"
                    (pretty_ty (TyVar tyvar))
                    (pretty_ty tau1)
                    (pretty_ty tau2)
            )
        )
    | None -> ()

    // search for circularity
    let circularity =
        composed_subst
        |> List.tryFind (fun (type_var, t) -> is_typevar_into_type type_var t)

    match circularity with
    | Some(type_var, t) ->
        raise (
            CompositionError(
                sprintf
                    "Circularity found during composition: type variable %s maps to type %s"
                    (pretty_ty (TyVar type_var))
                    (pretty_ty t)
            )
        )
    | None -> ()

    composed_subst

let ($) = compose_subst

let rec unify (t1: ty) (t2: ty) : subst =
    match t1, t2 with
    | TyName c1, TyName c2 when c1 = c2 -> []
    | TyVar type_var, t
    | t, TyVar type_var -> (type_var, t) :: []
    | TyArrow(t1, t2), TyArrow(t3, t4) -> (unify t1 t3) $ (unify t2 t4)
    | TyTuple(t1 :: tail), TyTuple(t1' :: tail') -> (unify t1 t1') $ (unify (TyTuple tail) (TyTuple tail'))
    | _ -> raise (UnificationError "Error while unify, some types are incoherent each other")


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

let gen env ty =
    Forall(freevars_ty ty - freevars_scheme_env env, ty)

// basic environment: add builtin operators at will
//

let inst (Forall(free_var, t)) =
    let polymorphic_var_subst =
        free_var |> Set.toList |> List.map (fun var -> (var, create_type_variable ()))

    apply_subst t polymorphic_var_subst

let rec apply_subst_scheme (Forall(tyvar, ty)) (subst: subst) =
    let theta' =
        List.filter (fun (scheme_tyvar: tyvar, _) -> not (Set.contains scheme_tyvar tyvar)) subst

    Forall(tyvar, apply_subst ty theta')

let rec apply_subst_env (env: scheme env) (subst: subst) =
    env |> List.map (fun (id, schema) -> (id, apply_subst_scheme schema subst))

let gamma0 =
    [ ("+", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("-", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("*", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("/", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("<", TyArrow(TyInt, TyArrow(TyInt, TyBool))) ]

let binary_operators =
    [ ("+",
       [ (TyInt, TyInt, TyInt)
         (TyFloat, TyFloat, TyFloat)
         (TyString, TyString, TyString) ])
      ("-", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("*", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("/", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("%", [ (TyInt, TyInt, TyInt) ])
      ("=",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      ("<",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      ("<=",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      (">",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      (">=",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      ("<>",
       [ (TyInt, TyInt, TyBool)
         (TyFloat, TyFloat, TyBool)
         (TyChar, TyChar, TyBool)
         (TyString, TyString, TyBool)
         (TyUnit, TyUnit, TyBool)
         (TyBool, TyBool, TyBool) ])
      ("and", [ (TyBool, TyBool, TyBool) ])
      ("or", [ (TyBool, TyBool, TyBool) ]) ]

let unary_operators =
    [ ("not", [ (TyBool, TyBool) ]); ("-", [ (TyInt, TyInt); (TyFloat, TyFloat) ]) ]

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

    | Var(identifier) ->
        try
            let var = lookup env identifier
            inst var, []
        with :? KeyNotFoundException ->
            unexpected_error "typeinfer_expr: variable identifier is not defined (%s)" identifier

    | App(left_expression, right_expression) ->
        printf "Inferring type for application"
        let tau1, theta1 = typeinfer_expr env left_expression
        let tau2, theta2 = typeinfer_expr (apply_subst_env env theta1) right_expression
        let type_var = create_type_variable ()
        let theta3 = unify tau1 (TyArrow(tau2, type_var))
        (apply_subst type_var theta3, theta3 $ theta2)

    | BinOp(e1, operator, e2) ->
        let tau1, theta1 = typeinfer_expr env e1
        let tau2, theta2 = typeinfer_expr env e2

        try
            let _, operation_types = List.find (fun (op, _) -> op = operator) binary_operators

            try
                let left_ty, right_ty, res_ty =
                    match (tau1, tau2) with
                    // check if the operator is defined for the two types
                    | (TyName _, TyName _) ->
                        List.find
                            (fun (left_ty, right_ty, _) -> ((left_ty = tau1) && (right_ty = tau2)))
                            operation_types
                    // check if the operator is defined for the right type so the algorithm can infer the left type
                    | (TyVar _, TyName _) -> List.find (fun (_, right_ty, _) -> tau2 = right_ty) operation_types
                    // check if the operator is defined for the left type so the algorithm can infer the roght type
                    | (TyName _, TyVar _) -> List.find (fun (left_ty, _, _) -> tau1 = left_ty) operation_types
                    //fallback to the first definition of the operator
                    | (TyVar _, TyVar _) -> operation_types.[0]
                    | _ -> unexpected_error "typeinfer_expr: unable to find or infer types for operator (%s)" operator

                let sub1 = unify left_ty tau1
                let sub2 = unify right_ty tau2

                let finsub = sub1 $ sub2 $ theta1 $ theta2
                apply_subst res_ty finsub, finsub

            with :? KeyNotFoundException ->
                unexpected_error
                    "typeinfer_expr: type of binary operator (%s) is not defined for type (%O, %O); available types: (%O)"
                    operator
                    tau1
                    tau2
                    operation_types
        with :? KeyNotFoundException ->
            unexpected_error "typeinfer_expr: undefined binary operator (%s)" operator

    | UnOp(operator, expression) -> unexpected_error "typeinfer_expr: unary operator (%s) not supported" operator
    // let tau, theta = typeinfer_expr env expression

    // let _, operation_types = List.find (fun (op, _)-> op = operator) unary_operators
    // try
    //     let _ = List.find (fun (ty) -> ty = tau) operation_types
    //     match operator with
    //     | "not" -> apply_subst TyBool theta, theta
    //     | "-" -> apply_subst tau theta, theta
    //     | _ -> unexpected_error "typeinfer_expr: unaray operator (%s) is not defined" operator

    // with :? KeyNotFoundException -> unexpected_error "typeinfer_expr: type of unary operator %s is not defined for type (%O); available types: (%O)" operator tau operation_types

    | IfThenElse(e1, e2, Some e3) ->
        // TODO optionally you can follow the original type inference rule and apply/compose substitutions incrementally (see Advanced Notes on ML, Table 4, page 5)
        let t1, s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let t2, s3 = typeinfer_expr env e2
        let t3, s4 = typeinfer_expr env e3
        let s5 = unify t2 t3
        let s = s5 $ s4 $ s3 $ s2 $ s1
        apply_subst t2 s, s

    | Lambda(parameter, type_annotation, expression) ->
        let parameter_type_var = create_type_variable ()

        let type_annotation_subst =
            match type_annotation with
            | None -> []
            | Some ty -> unify parameter_type_var ty

        let parameter_type_scheme: scheme =
            Forall(Set.empty, apply_subst parameter_type_var type_annotation_subst)

        let env' = (parameter, parameter_type_scheme) :: env
        let tau2, theta2 = typeinfer_expr env' expression

        let theta = theta2 $ type_annotation_subst
        let tau1 = apply_subst parameter_type_var theta

        apply_subst (TyArrow(tau1, tau2)) theta, theta

    | Let(identifier, type_annotation, value, in_expr) ->
        let (value_type, value_subst) = typeinfer_expr env value

        let subst1 =
            match type_annotation with
            | None -> []
            | Some t -> unify value_type t
            $ value_subst

        let env' = apply_subst_env env subst1
        let sigma1 = gen env' value_type
        let in_type, in_subst = typeinfer_expr ((identifier, sigma1) :: env') in_expr
        let final_subst = subst1 $ in_subst
        in_type, final_subst

    | LetRec(identifier, type_annotation, let_expression, in_expression) ->
        let identifier_var_type = create_type_variable ()
        let env' = (identifier, gen env identifier_var_type) :: env
        let tau1, theta1 = typeinfer_expr env let_expression

        let theta1 =
            ((match type_annotation with
              | None -> []
              | Some t -> unify tau1 t)
             $ theta1)

        let sigma1 = gen env' tau1
        let env'' = (identifier, sigma1) :: env'
        let tau2, theta2 = typeinfer_expr env'' in_expression
        let theta3 = unify identifier_var_type (apply_subst tau1 theta1)
        (tau2, theta1 $ theta2 $ theta3)

    | Tuple(values) ->
        let res = List.map (typeinfer_expr env) values
        let types = List.map (fun (ty, _) -> ty) res

        let subst =
            List.reduce (fun sub1 sub2 -> sub1 $ sub2) (List.map (fun (_, sub) -> sub) res)

        TyTuple(types), subst


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

    // Type checking of annotated let-rec binding
    | LetRec(identifier, Some type_annotation, let_expression, in_expression) ->
        // Since this is a let-rec, let's generate the new environment with the new identifier

        let env' = (identifier, type_annotation) :: env
        let let_expression_type = typecheck_expr env' let_expression

        // Check if the annotation and the type of the expression we are assigning are the same
        if let_expression_type <> type_annotation then
            type_error "type %O differs from type %O in let-rec-binding" type_annotation let_expression_type

        // Since this is a let-rec let's check if the expression we are assigning is a lambda.
        // We don't support recursive variables defined on literals
        match let_expression_type with
        | TyArrow(_, _) -> typecheck_expr env' in_expression
        | _ -> type_error "typecheck_expr: let-rec-binding are supported only for lambda, given %O" let_expression_type

    // Type inference of let-rec binding
    | LetRec(identifier, None, let_expression, expression) ->
        type_error "unannotated let-rec-binding are not supported by the type checker"

    | Lambda(parameter, Some parameter_type, expression) ->
        let env' = (parameter, parameter_type) :: env
        let expression_type = typecheck_expr env' expression
        TyArrow(parameter_type, expression_type)

    | Lambda(_, None, _) -> type_error "unannotated lambdas are not supported by the type checker"

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

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
