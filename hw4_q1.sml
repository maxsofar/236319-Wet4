datatype Atom = SYMBOL of string | NIL;
datatype SExp = ATOM of Atom | CONS of (SExp * SExp);

exception Undefined;
exception Empty;

fun initEnv() = fn (x: string) => if true then raise Undefined else ATOM(NIL);

fun define (name: string) (oldEnv: string -> 'a) value = fn (x: string) => if x = name then value else oldEnv x;

fun emptyNestedEnv() = [initEnv()];

fun pushEnv (env: 'a) (envList: 'a list) = env::envList;

fun popEnv (envList: 'a list) = if null envList then raise Empty else tl envList;

fun topEnv (envList: 'a list) = if null envList then raise Empty else hd envList;

fun defineNested (name: string) (envList: (string -> 'a) list) value = 
    pushEnv (define name (topEnv envList) value) (popEnv envList);

fun find (name: string) (envList: (string -> 'a) list) =
    if null envList then raise Undefined
    else
        let
            val topEnv = hd envList
        in
            topEnv name handle Undefined => find name (tl envList)
        end;


