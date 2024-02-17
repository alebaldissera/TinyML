(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast
open System.Collections.Generic

let type_error fmt = throw_formatted TypeError fmt
let infer_error fmt = throw_formatted InferError fmt
let unification_error fmt = throw_formatted UnificationError fmt
let composition_error fmt = throw_formatted CompositionError fmt

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
        composition_error
            "Error while compose substitutions. Variable type %s maps to type %s and %s"
            (pretty_ty (TyVar tyvar))
            (pretty_ty tau1)
            (pretty_ty tau2)
    | None -> ()

    // search for circularity
    let circularity =
        composed_subst
        |> List.tryFind (fun (type_var, t) -> is_typevar_into_type type_var t)

    match circularity with
    | Some(type_var, t) ->
        composition_error
            "Circularity found during composition: type variable %s maps to type %s"
            (pretty_ty (TyVar type_var))
            (pretty_ty t)
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
    | _ ->
        unification_error
            "Error while unify, some types are incoherent each other. Unable to unify type (%s) with type (%s)"
            (pretty_ty t1)
            (pretty_ty t2)

let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyVar type_var -> Set.empty.Add(type_var)
    | TyArrow(t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyTuple(head :: tail) -> Set.union (freevars_ty head) (freevars_ty (TyTuple tail))
    | TyTuple [] -> Set.empty

let freevars_scheme (Forall(tvs, t)) = Set.difference (freevars_ty t) tvs

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

/// <summary>Apply a substitution to a scheme</summary>
/// <param name="Forall(tyvar, ty)">The scheme where apply the substitution</param>
/// <param name="subst">The substitution to apply</param>
/// <returns>A new scheme with the substitution applied</returns>
let rec apply_subst_scheme (Forall(tyvar, ty)) (subst: subst) =
    let theta' =
        List.filter (fun (scheme_tyvar: tyvar, _) -> not (Set.contains scheme_tyvar tyvar)) subst

    Forall(tyvar, apply_subst ty theta')


/// <summary>Apply a substitution to an environment</summary>
/// <param name="env">The environment to apply the substitution</param>
/// <param name="subst">The substitution to apply</param>
/// <returns>A new environment with the the substitution applied</returns>
let rec apply_subst_env (env: scheme env) (subst: subst) =
    env |> List.map (fun (id, schema) -> (id, apply_subst_scheme schema subst))

let gamma0 =
    [ ("+", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("-", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("*", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("/", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("<", TyArrow(TyInt, TyArrow(TyInt, TyBool))) ]

/// <summary>This list contains maps for operator which may implements name overloading. The tuple contains as fist element the operator, as second element a list containing a tuple with input types and output type for that operator.</summary>
let binary_operators =
    [ ("+",
       [ (TyInt, TyInt, TyInt)
         (TyFloat, TyFloat, TyFloat)
         (TyString, TyString, TyString) ])
      ("-", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("*", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("/", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
      ("%", [ (TyInt, TyInt, TyInt); (TyFloat, TyFloat, TyFloat) ])
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


/// <summary>A list of unary operator. The contained tuples have the operator as first element and a list of tuple with input type and output type as second element.</summary>
let unary_operators =
    [ ("not", [ (TyBool, TyBool) ]); ("-", [ (TyInt, TyInt); (TyFloat, TyFloat) ]) ]

/// <summary>Try to infer o deduce the type of an expression.</summary>
/// <param name="env">The current binding environment.</param>
/// <param name="e">The expression to infer types</param>
/// <returns>The type of the expression and a set of substitution.</returns>
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
            unexpected_error "variable identifier is not defined (%s)" identifier

    | App(left_expression, right_expression) ->
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

    | UnOp(operator, expression) -> //unexpected_error "typeinfer_expr: unary operator (%s) not supported" operator
        let tau, theta = typeinfer_expr env expression

        try
            let _, operation_types = unary_operators |> List.find (fun (op, _) -> op = operator)

            try
                let (in_type, out_type) =
                    match tau with
                    | TyName _ -> operation_types |> List.find (fun (in_type, _) -> tau = in_type)
                    // Fallback to the first defined type for such operator
                    | TyVar _ -> operation_types.[0]
                    | _ -> unexpected_error "typeinfer_expr: unable to find or infer types for operator (%s)" operator

                let sub = (unify in_type tau) $ theta
                apply_subst out_type sub, sub

            with :? KeyNotFoundException ->
                unexpected_error
                    "typeinfer_expr: type of unary operator %s is not defined for type (%O); available types: (%O)"
                    operator
                    tau
                    operation_types
        with :? KeyNotFoundException ->
            unexpected_error "typeinfer_expr: unary operator (%s) not defined" operator

    | IfThenElse(e1, e2, Some e3) ->
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
        let tau1, theta1 = typeinfer_expr env' let_expression

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
            type_error "variable identifier not defined (%s)" x

    | Let(x, type_annotation, e1, e2) ->
        let t1 = typecheck_expr env e1

        match type_annotation with
        | None -> ()
        | Some ty ->
            if ty <> t1 then
                type_error "type %s differs from type %s in let-binding" (pretty_ty t1) (pretty_ty ty)

        let env' = (x, t1) :: env
        typecheck_expr env' e2

    // Type checking of annotated let-rec binding
    | LetRec(identifier, Some type_annotation, let_expression, in_expression) ->
        // Since this is a let-rec, let's generate the new environment with the new identifier

        let env' = (identifier, type_annotation) :: env
        let let_expression_type = typecheck_expr env' let_expression

        // Check if the annotation and the type of the expression we are assigning are the same
        if let_expression_type <> type_annotation then
            type_error
                "type %s differs from type %s in let-rec-binding"
                (pretty_ty type_annotation)
                (pretty_ty let_expression_type)

        // Since this is a let-rec let's check if the expression we are assigning is a lambda.
        // We don't support recursive variables defined on literals
        match let_expression_type with
        | TyArrow(_, _) -> typecheck_expr env' in_expression
        | _ -> type_error "let-rec-binding are supported only for lambda, given %s" (pretty_ty let_expression_type)

    // Type inference of let-rec binding
    | LetRec(_, None, _, _) -> type_error "unannotated let-rec-binding are not supported by the type checker"

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
                type_error
                    "argument has type %s while function parameter has type %s in application"
                    (pretty_ty t2)
                    (pretty_ty ta)

            tb
        | t1 -> type_error "left hand of application is not an arrow type: %s" (pretty_ty t1)

    | IfThenElse(e1, e2, e3) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyBool then
            type_error "bool expected in if guard, but got %s" (pretty_ty t1)

        let t2 = typecheck_expr env e2

        match e3 with
        | None -> ()
        | Some expression ->
            let t3 = typecheck_expr env expression

            if t2 <> t3 then
                type_error "then and else branches have different types: %s and %s" (pretty_ty t2) (pretty_ty t3)


        t2

    | BinOp(left_expression, operator, right_expression) ->
        let left_type = typecheck_expr env left_expression
        let right_type = typecheck_expr env right_expression

        try
            let _, operator_types = binary_operators |> List.find (fun (op, _) -> op = operator)

            try
                let (_, _, out_type) =
                    operator_types
                    |> List.find (fun (l_type, r_type, _) -> l_type = left_type && r_type = right_type)

                out_type
            with :? KeyNotFoundException ->
                type_error
                    "operator (%s) undefined on types (%s) and (%s), available types: (%O)"
                    operator
                    (pretty_ty left_type)
                    (pretty_ty right_type)
                    operator_types

        with :? KeyNotFoundException ->
            type_error "undefined operator (%s)" operator

    | UnOp(operator, expression) ->
        let expression_type = typecheck_expr env expression

        try
            let _, operator_types = unary_operators |> List.find (fun (op, _) -> op = operator)

            try
                let _, out_type =
                    operator_types |> List.find (fun (in_type, _) -> in_type = expression_type)

                out_type
            with :? KeyNotFoundException ->
                type_error
                    "undefined unary operator (%s) on type (%s), available types: (%O)"
                    operator
                    (pretty_ty expression_type)
                    operator_types
        with :? KeyNotFoundException ->
            type_error "undefined unary operator (%s)" operator

    | Tuple elements -> TyTuple(elements |> List.map (typecheck_expr env))

    | _ -> unexpected_error "unsupported expression: %s [AST: %A]" (pretty_expr e) e
