open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> None
  | (var, value) :: t -> if x = var then Some value else lookup t x

let rec optimize env e = 
  match e with
  | Int x -> Int x
  | Bool b -> Bool b
  | ID id -> 
    (match lookup env id with
    | Some x -> x
    | None -> e)
  | Fun (var, exptype, expr) -> Fun (var, exptype, optimize (extend env var (ID var)) expr)
  | Not (e1) -> 
    (match e1 with
    | ID id -> 
      (match lookup env id with
      | Some Bool true -> Bool false
      | Some Bool false -> Bool true
      | _ -> raise (TypeError "not id isnt bool"))
    | Bool true -> Bool false
    | Bool false -> Bool true
    | _ -> raise (TypeError "incorrect not bool"))
  | Binop (op, e1, e2) -> 
    let e1opt = optimize env e1 in
    let e2opt = optimize env e2 in
    (match op with
    | Add -> if e1opt = Int 0 then e2opt else if e2opt = Int 0 then e1opt else
      (match e1opt, e2opt with
      | (Int x, Int y) -> Int (x+y)
      | (x, Int y) -> if y = 0 then x else Binop (Add, x, Int y)
      | (Int x, y) -> if x = 0 then y else Binop (Add, Int x, y)
      | _ -> raise (TypeError "add types incorrect"))
    | Sub -> if e2opt = Int 0 then e1opt else
      (match e1opt, e2opt with
      | (Int x, Int y) -> Int (x-y)
      | (x, Int y) -> if y = 0 then x else Binop (Sub, x, Int y)
      | (Int x, y) -> Binop (Sub, Int x, y)
      | _ -> raise (TypeError "sub types incorrect"))
    | Mult -> if e1opt = Int 0 || e2opt = Int 0 then Int 0 else
      (match e1opt, e2opt with
      | (Int x, Int y) -> Int (x*y)
      | (x, Int y) -> 
        if y = 0 then Int 0 else 
          if y = 1 then x else Binop (Mult, x, Int y)
      | (Int x, y) -> 
        if x = 0 then Int 0 else 
          if x = 1 then y else Binop (Mult, Int x, y)
      | _ -> raise (TypeError "mult types incorrect"))
    | Div -> if e1opt = Int 0 then Int 0 else
      (match e1opt, e2opt with
      | (Int x, Int y) -> if y = 0 then raise DivByZeroError else Int (x/y)
      | (x, Int y) -> 
        if y = 0 then raise DivByZeroError else 
          if y = 1 then x else Binop (Div, x, Int y)
      | (Int x, y) -> if x = 0 then Int 0 else Binop (Div, Int x, y)
      | _ -> raise (TypeError "div types incorrect"))
    | Greater -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x>y)
      | (Int x, y) -> Binop (Greater, Int x, y)
      | (x, Int y) -> Binop (Greater, x, Int y)
      | _ -> raise (TypeError "greater types incorrect"))
    | Less -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x<y)
      | (Int x, y) -> Binop (Less, Int x, y)
      | (x, Int y) -> Binop (Less, x, Int y)
      | _ -> raise (TypeError "less types incorrect"))
    | GreaterEqual -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x>=y)
      | (Int x, y) -> Binop (GreaterEqual, Int x, y)
      | (x, Int y) -> Binop (GreaterEqual, x, Int y)
      | _ -> raise (TypeError "greatereq types incorrect"))
    | LessEqual -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x<=y)
      | (Int x, y) -> Binop (LessEqual, Int x, y)
      | (x, Int y) -> Binop (LessEqual, x, Int y)
      | _ -> raise (TypeError "lesseq types incorrect"))
    | Equal -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x = y)
      | (Bool x, Bool y) -> Bool (x = y)
      | (x, y) -> Binop (Equal, x, y))
    | NotEqual -> 
      (match e1opt, e2opt with
      | (Int x, Int y) -> Bool (x <> y)
      | (Bool x, Bool y) -> Bool (x <> y)
      | (x, y) -> Binop (NotEqual, x, y))
    | Or -> 
      (match e1opt, e2opt with
      | (Bool x, Bool y) -> Bool (x||y)
      | (Bool x, y) -> if x = true then Bool true else Binop (Or, Bool x, y)
      | (x, Bool y) -> if y = true then Bool true else Binop (Or, x, Bool y)
      | _ -> raise (TypeError "or types incorrect"))
    | And -> 
      (match e1opt, e2opt with
      | (Bool x, Bool y) -> Bool (x&&y)
      | (Bool x, y) -> if x = false then Bool false else Binop (And, Bool x, y)
      | (x, Bool y) -> if y = false then Bool false else Binop (And, x, Bool y)
      | _ -> raise (TypeError "and types incorrect"))
    )
  | If (guard, tbranch, fbranch) -> 
    let opt_guard = optimize env guard in
    (match opt_guard with
    | Bool true -> optimize env tbranch
    | Bool false -> optimize env fbranch
    | _ -> If (opt_guard, optimize env tbranch, optimize env fbranch)) 

  | App (e1, e2) -> 
    let e1opt = optimize env e1 in
    let e2opt = optimize env e2 in
    (match e1opt with
    | Fun (a,b,c) -> optimize (extend env a e2opt) c
    | _ -> App (e1, e2))
  | Let (var, e1, e2) -> 
    let e1_opt = optimize env e1 in
    let new_env = extend env var e1_opt in
    optimize new_env e2
  | LetRec (var, exptype, e1, e2) -> 
    LetRec (var, exptype, optimize env e1, optimize (extend env var e1) e2)
  | Record fields -> 
    let lst = List.fold_left (fun a curr -> 
      match curr with
      | (Lab id, expr) -> (Lab id, optimize env expr) :: a
      | _ -> raise (TypeError "invalid record type")) [] fields in Record (List.rev lst)
  | Select (label, record) -> 
    (match label with
    | Lab id -> 
      (match record with
      | Record f -> 
        let lst = (List.fold_left (fun a x -> match x with
        | (Lab l, v2) -> if label = Lab l then [optimize env v2] @ a else a
        | _ -> raise (TypeError "invalid record field")) [] f) in 
        if List.length lst = 0 then raise (SelectError "no select label found") else 
          List.nth lst (List.length lst - 1)
      | ID x -> 
        let xlookup = lookup env x in 
        (match xlookup with
        | Some Record f -> optimize env (Select (Lab id, Record f))
        | _ -> failwith "goofy")  (*not too sure about this part*)
      | _ -> raise (TypeError "invalid record fiels"))
    | _ -> raise (TypeError "invalid select label type"))
