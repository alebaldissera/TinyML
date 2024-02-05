(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

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

        | _ -> unexpected_error "non-closure on left hand of application"

    | Var x -> lookup venv x

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


    // TODO complete this implementation

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
