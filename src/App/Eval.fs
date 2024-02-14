(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast
open System.Collections.Generic
// evaluator
//

let rec eval_expr (venv: value env) (e: expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Lambda(x, _, e) -> Closure(venv, x, e)

    | App(e1, e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2

        match v1 with
        | Closure(venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e
        | RecClosure(_, _, parameter, expression) ->
            let venv'' = (parameter, v2) :: venv
            eval_expr venv'' expression
        | _ -> unexpected_error "non-closure on left hand of application"

    | Var x ->
        try
            lookup venv x
        with :? KeyNotFoundException ->
            unexpected_error "eval_expr: variable identifier not defined (%s)" x

    | Let(identifier, _, let_expression, expression) ->
        let let_value = eval_expr venv let_expression
        let venv' = (identifier, let_value) :: venv
        eval_expr venv' expression

    | LetRec(let_identifier, _, let_expression, in_expression) ->

        match let_expression with
        | Lambda(parameter_identifier, _, expression) ->
            let venv' =
                (let_identifier, RecClosure(venv, let_identifier, parameter_identifier, expression))
                :: venv

            eval_expr venv' in_expression
        | _ -> unexpected_error "eval_expr: non lambda expression assigned to let-rec, given %O" let_expression

    | IfThenElse(condition, expression1, Some expression2) ->
        match eval_expr venv condition with
        | VLit(LBool true) -> eval_expr venv expression1
        | VLit(LBool false) -> eval_expr venv expression2
        | _ -> unexpected_error "eval_expr: non-boolean in if guard %s [AST: %A]" (pretty_expr e) e

    | IfThenElse(condition, expression1, None) ->
        match eval_expr venv condition with
        | VLit(LBool true) -> eval_expr venv expression1
        | VLit(LBool false) -> VLit(LUnit)
        | _ -> unexpected_error "eval_expr: non-boolean in if guard %s [AST: %A]" (pretty_expr e) e

    | BinOp(left_expression, ("+" | "-" | "*" | "/" as op), right_expression) ->
        let left_res = eval_expr venv left_expression
        let right_res = eval_expr venv right_expression

        match (op, left_res, right_res) with
        | ("+", VLit(LString l_value), VLit(LString r_value)) -> VLit(LString(l_value + r_value))
        // let the pattern matching of the types of the operand to the function
        | ("+", _, _) -> math_operation op (+) (+) venv left_res right_res
        | ("-", _, _) -> math_operation op (-) (-) venv left_res right_res
        | ("*", _, _) -> math_operation op (*) (*) venv left_res right_res
        | ("/", _, _) -> math_operation op (/) (/) venv left_res right_res
        | _ ->
            unexpected_error
                "eval_expr: illegal operands in binary operator (%s) %s - %s"
                op
                (pretty_value left_res)
                (pretty_value right_res)

    | BinOp(left_expression, "%", right_expression) ->
        let left_res = eval_expr venv left_expression
        let right_res = eval_expr venv right_expression

        match (left_res, right_res) with
        | (VLit(LInt l_value), (VLit(LInt r_value))) -> VLit(LInt(l_value % r_value))
        | _ ->
            unexpected_error
                "eval_expr: illegal operands in binary operator (%%) %s - %s"
                (pretty_value left_res)
                (pretty_value right_res)

    | BinOp(left_expression, ("=" | "<>" | "<" | ">" | "<=" | ">=" as op), right_expression) ->
        let left_res = eval_expr venv left_expression
        let right_res = eval_expr venv right_expression

        VLit(
            LBool(
                match (op, left_res, right_res) with
                // string comparisons
                | ("=", VLit(LString l_val), VLit(LString r_val)) -> l_val = r_val
                | ("<>", VLit(LString l_val), VLit(LString r_val)) -> l_val <> r_val
                | (">", VLit(LString l_val), VLit(LString r_val)) -> l_val > r_val
                | ("<", VLit(LString l_val), VLit(LString r_val)) -> l_val < r_val
                | (">=", VLit(LString l_val), VLit(LString r_val)) -> l_val >= r_val
                | ("<=", VLit(LString l_val), VLit(LString r_val)) -> l_val <= r_val

                // booleans comparison
                | ("=", VLit(LBool l_val), VLit(LBool r_val)) -> l_val = r_val
                | ("<>", VLit(LBool l_val), VLit(LBool r_val)) -> l_val <> r_val
                | (">", VLit(LBool l_val), VLit(LBool r_val)) -> l_val > r_val
                | ("<", VLit(LBool l_val), VLit(LBool r_val)) -> l_val < r_val
                | (">=", VLit(LBool l_val), VLit(LBool r_val)) -> l_val >= r_val
                | ("<=", VLit(LBool l_val), VLit(LBool r_val)) -> l_val <= r_val

                // Number requires som special treatment since there is two types of number
                // Pattern matching on the type of the variable happens inside the function,
                // there is a little bit of redundancy on the resolution of the type of the expression
                // but this results in a more readable code
                | ("=", _, _) -> number_comparison op (=) (=) left_res right_res
                | ("<>", _, _) -> number_comparison op (<>) (<>) left_res right_res
                | (">", _, _) -> number_comparison op (>) (>) left_res right_res
                | ("<", _, _) -> number_comparison op (<) (<) left_res right_res
                | (">=", _, _) -> number_comparison op (>=) (>=) left_res right_res
                | ("<=", _, _) -> number_comparison op (<=) (<=) left_res right_res
                | _ ->
                    unexpected_error
                        "eval_expr: illegal operands in binary operator (%s) %s - %s"
                        op
                        (pretty_value left_res)
                        (pretty_value right_res)
            )
        )

    | BinOp(_, op, _) -> unexpected_error "eval_expr: unsupported binary operator (%s)" op

    | UnOp(("-" | "not" as op), expression) ->
        let result = eval_expr venv expression

        match (op, result) with
        | ("-", VLit(LInt value)) -> VLit(LInt(-value))
        | ("-", VLit(LFloat value)) -> VLit(LFloat(-value))
        | ("not", VLit(LBool value)) -> VLit(LBool(not value))
        | _ -> unexpected_error "eval_expr: illegal operand in unary operator (%s) %s" op (pretty_value result)

    | UnOp(op, _) -> unexpected_error "eval_expr: unsupported unary operator (%s)" op
    // TODO complete this implementation

    | Tuple(expressions) -> VTuple(List.map (fun expr -> eval_expr venv expr) expressions)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// Apply a binary math operation with type escalation
and math_operation str_op int_operator float_operator env left_res right_res =


    match (left_res, right_res) with
    | (VLit(LInt l_value), VLit(LInt r_value)) -> VLit(LInt(int_operator l_value r_value))
    | (VLit(LInt l_value), VLit(LFloat r_value)) -> VLit(LFloat(float_operator (float l_value) r_value))
    | (VLit(LFloat l_value), VLit(LInt r_value)) -> VLit(LFloat(float_operator l_value (float r_value)))
    | (VLit(LFloat l_value), VLit(LFloat r_value)) -> VLit(LFloat(float_operator l_value r_value))
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary operator (%s) %s - %s"
            str_op
            (pretty_value left_res)
            (pretty_value right_res)

// Comparison on numbers
and number_comparison str_op int_comparison float_comparison left_res right_res =

    match (left_res, right_res) with
    | (VLit(LInt l_value), VLit(LInt r_value)) -> int_comparison l_value r_value
    | (VLit(LInt l_value), VLit(LFloat r_value)) -> float_comparison (float l_value) r_value
    | (VLit(LFloat l_value), VLit(LInt r_value)) -> float_comparison l_value (float r_value)
    | (VLit(LFloat l_value), VLit(LFloat r_value)) -> float_comparison l_value r_value
    | _ ->
        unexpected_error
            "eval_expr: illegal operands in binary operator (%s) %s - %s"
            str_op
            (pretty_value left_res)
            (pretty_value right_res)
