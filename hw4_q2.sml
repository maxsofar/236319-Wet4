
use "hw4_q1.sml";

use "parser.sml";

exception LispError;

(* Helper function - feel free to delete *)
fun first (x, _) = x;

local
    fun tokenize x = 
        String.tokens (fn c: char => c = #" ") 
            (String.translate (fn #"(" => "( " | #")" => " )" | c => str c) x);

    (* Helper functions - feel free to delete *)
    (* ====================================== *)
    fun is_digit c = c >= #"0" andalso c <= #"9";

    fun is_number str =
        let
            fun check [] = true
            | check (c::cs) = is_digit c andalso check cs
            
            val chars = String.explode str
        in
            if List.null chars then false else check chars
        end;
        
    fun char_to_int c = ord(c) - ord(#"0")

    fun string_to_int str =
        let
            fun convert [] acc = acc
            | convert (c::cs) acc = convert cs (10 * acc + char_to_int c)
        in
            convert (String.explode str) 0
        end;

    fun sexp_to_int sexp =
        case sexp of
            ATOM (SYMBOL s) => string_to_int s
          | _ => raise LispError;
    (* ====================================== *)


in
    fun eval_sexp sexp env =
        case sexp of
          ATOM NIL => (ATOM NIL, env)
        | ATOM (SYMBOL s) => 
            if is_number s then
                (ATOM (SYMBOL s), env)
            else
                (find s env, env)
        | CONS (hd, tl) =>
            case hd of
                  ATOM (SYMBOL "cons") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                (CONS (eval_first_arg, eval_second_arg), env2)
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "car") =>
                    (case tl of
                        CONS (arg, ATOM NIL) =>
                            let
                                val (eval_arg, env1) = eval_sexp arg env
                            in
                                case eval_arg of
                                    CONS (first_arg, _) => (first_arg, env1)
                                | _ => raise LispError
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "cdr") =>
                    (case tl of
                        CONS (arg, ATOM NIL) =>
                            let
                                val (eval_arg, env1) = eval_sexp arg env
                            in
                                case eval_arg of
                                    CONS (_, second_arg) => (second_arg, env1)
                                | _ => raise LispError
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "quote") =>
                    (case tl of
                        CONS (arg, ATOM NIL) => (arg, env)  (* Return the argument as is *)
                    | _ => raise LispError)  (* Error if "quote" does not have exactly one argument *)
                | ATOM (SYMBOL "atom") =>
                    (case tl of
                        CONS (arg, ATOM NIL) =>
                            let
                                val (eval_arg, env1) = eval_sexp arg env
                            in
                                case eval_arg of
                                    ATOM _ => (ATOM (SYMBOL "t"), env1)
                                | _ => (ATOM NIL, env1)
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "null") =>
                    (case tl of
                        CONS (arg, ATOM NIL) =>
                            let
                                val (eval_arg, env1) = eval_sexp arg env
                            in
                                case eval_arg of
                                    ATOM NIL => (ATOM (SYMBOL "t"), env1)
                                | _ => (ATOM NIL, env1)
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "eq") =>
                    (case tl of
                        CONS (arg1, CONS (arg2, ATOM NIL)) =>
                            let
                                val (eval_arg1, env1) = eval_sexp arg1 env
                                val (eval_arg2, env2) = eval_sexp arg2 env1
                            in
                                case (eval_arg1, eval_arg2) of
                                    (ATOM a1, ATOM a2) => if a1 = a2 then (ATOM (SYMBOL "t"), env2) else (ATOM NIL, env2)
                                | _ => (ATOM NIL, env2)
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "cond") =>
                    let
                        fun eval_cond clauses env =
                            case clauses of
                                ATOM NIL => (ATOM NIL, env)  (* No more clauses, return NIL *)
                              | CONS (clause, rest) =>
                                (case clause of
                                    CONS (cond, CONS (result, ATOM NIL)) =>
                                        let
                                            val (eval_cond_result, env1) = eval_sexp cond env
                                        in
                                            case eval_cond_result of
                                                ATOM NIL => eval_cond rest env1  (* Condition is false, try next *)
                                              | _ => eval_sexp result env1  (* Condition is true, evaluate result *)
                                        end
                                  | _ => raise LispError)  (* Invalid clause structure *)
                              | _ => raise LispError  (* Invalid clauses structure *)
                    in
                        eval_cond tl env
                    end
                | ATOM (SYMBOL "+") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (Int.toString (string_to_int a + string_to_int b))), env2)
                                        else
                                            raise LispError
                                | _ => raise LispError
                            end
                    | _ => raise LispError)
                | ATOM (SYMBOL "-") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (Int.toString (string_to_int a - string_to_int b))), env2)
                                        else
                                            raise LispError
                                | _ => raise LispError
                            end
                    | _ => raise LispError)


                | ATOM (SYMBOL "*") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1

                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (Int.toString (string_to_int a * string_to_int b))), env2)
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

                | ATOM (SYMBOL "/") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            let
                                                val divisor = string_to_int b
                                            in
                                                if divisor <> 0 then
                                                    (ATOM (SYMBOL (Int.toString (string_to_int a div divisor))), env2)
                                                else
                                                    raise LispError
                                            end
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

                | ATOM (SYMBOL "mod") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            let
                                                val divisor = string_to_int b
                                            in
                                                if divisor <> 0 then
                                                    (ATOM (SYMBOL (Int.toString (string_to_int a mod divisor))), env2)
                                                else
                                                    raise LispError
                                            end
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)
                | ATOM (SYMBOL "=") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (if string_to_int a = string_to_int b then "t" else "nil")), env2)
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

                | ATOM (SYMBOL "/=") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (if string_to_int a <> string_to_int b then "t" else "nil")), env2)
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

                | ATOM (SYMBOL ">") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (if string_to_int a > string_to_int b then "t" else "nil")), env2)
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

                | ATOM (SYMBOL "<") =>
                    (case tl of
                        CONS (first_arg, CONS (second_arg, ATOM NIL)) =>
                            let
                                val (eval_first_arg, env1) = eval_sexp first_arg env
                                val (eval_second_arg, env2) = eval_sexp second_arg env1
                            in
                                case (eval_first_arg, eval_second_arg) of
                                    (ATOM (SYMBOL a), ATOM (SYMBOL b)) =>
                                        if is_number a andalso is_number b then
                                            (ATOM (SYMBOL (if string_to_int a < string_to_int b then "t" else "nil")), env2)
                                        else
                                            raise LispError
                                    | _ => raise LispError
                            end
                        | _ => raise LispError)

            
                | CONS (ATOM (SYMBOL "lambda"), lambda_tl) =>
                    (case lambda_tl of
                        CONS (parameters, CONS (body, ATOM NIL)) =>
                            let
                                (* Extract strings from a nested CONS list *)
                                fun extract_strings lst =
                                    case lst of
                                        CONS (ATOM (SYMBOL s), rest) => s :: extract_strings rest
                                    | ATOM NIL => []
                                    | _ => raise LispError

                                val parameter_names = extract_strings parameters
                                
                                (* Evaluate each value in the current environment *)
                                fun eval_values lst env =
                                    case lst of
                                        CONS (v, rest) => 
                                            let
                                                val (evaluated_sexp, _) = eval_sexp v env
                                            in
                                                evaluated_sexp :: eval_values rest env
                                            end
                                        | ATOM NIL => []
                                        | _ => raise LispError

                                val argument_values = eval_values tl env



                                (* Update the environment with the new parameter names and argument values *)

                                fun bindParamsToEnv (envList: (string -> SExp) list) (paramNames: string list) (argValues: SExp list) =
                                    let
                                        fun bindParams (env: (string -> SExp) list) (names: string list) (values: SExp list) =
                                            case (names, values) of
                                                ([], []) => env
                                            | (name::restNames, value::restValues) =>
                                                    bindParams (defineNested name env value) restNames restValues
                                            | _ => raise LispError
                                    in
                                        bindParams envList paramNames argValues
                                    end;
                                    
                                (* Create a new environment with the parameter names and argument values *)
                                val new_env = bindParamsToEnv env parameter_names argument_values

                                (* Evaluate the body of the function in the context of the new environment *)
                                val (result, _) = eval_sexp body new_env
                            in
                                (result, env)
                                (* (ATOM NIL, env) *)
                            end
                        | _ => raise LispError)

                (* | CONS (ATOM (SYMBOL "label"), label_tl) =>
                    (case label_tl of
                        CONS (ATOM (SYMBOL fname), CONS (lambda_expr as CONS (ATOM (SYMBOL "lambda"), _), args)) =>
                            let
                                (* val _ = print ("lambda_expr: " ^ (sexp_to_string (CONS (lambda_expr, tl))) ^ "\n") *)
                                (* val _ = print ("fname: " ^ fname ^ "\n") *)

                                (* Update the environment with the label pointing to the lambda expression *)
                                val new_env = defineNested fname env lambda_expr
                            in
                                (* Now evaluate the lambda expression or the rest of the S-expression with the updated environment *)
                                eval_sexp (CONS (lambda_expr, tl)) new_env
                            end
                        | _ => raise LispError)
                 | ATOM (SYMBOL label) =>
                    let

                        val func = find label env
                        val real_tl = case tl of
                            CONS (expr, _) => expr
                            | _ => raise LispError

                        val (fst, scnd) = eval_sexp real_tl env
                        val applied_func = CONS (func, fst)

                    in
                        eval_sexp applied_func env
                        
                    end *)
                
                | _ => raise LispError


     fun eval string_exp env =
        let
            val sexp = parse (tokenize string_exp)
            
        in
            (eval_sexp sexp env) handle LispError => (ATOM (SYMBOL "lisp-error"), env)
        end
end




