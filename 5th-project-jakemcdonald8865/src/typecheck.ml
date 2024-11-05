open Ast
open Utils

let extend env x v = (x, v) :: env

let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound type for " ^ x))
  | (var, value) :: t -> if x = var then value else lookup t x
let rec contains lst elt = List.fold_right(fun x a -> 
  if x = elt then true || a else false || a) lst false
let rec is_subtype t1 t2 = 
  match t1, t2 with
  | (TInt, TInt) -> true
  | (TBool, TBool) -> true
  | (TRec f1, TRec f2) -> 
    let length1 = List.length f1 in
    let length2 = List.length f2 in
    if (length1 < length2) then false else
      let if_contains = List.fold_right (fun curr a -> 
        if contains f1 curr then true && a else false && a) f2 true in if_contains
  | (TArrow (a, b), TArrow(c, d)) -> (is_subtype c a && is_subtype b d)
  | _ -> false

let rec typecheck gamma e = match e with
| Int x -> TInt
| Bool b -> TBool
| ID id -> lookup gamma id
| Fun (var, exptype, exp) -> 
  let new_gamma = extend gamma var exptype in
  let return_type = typecheck new_gamma exp in
  TArrow(exptype, return_type)
| Not e1 -> if typecheck gamma e1 = TBool then TBool else raise (TypeError "invalid not") 
| Binop (op, e1, e2) -> 
  let e1type = typecheck gamma e1 in
  let e2type = typecheck gamma e2 in
    (match op with
    | Add
    | Sub 
    | Mult
    | Div -> check_num_op e1type e2type
    | Greater
    | Less
    | GreaterEqual
    | LessEqual
    | Equal
    | NotEqual -> check_eq_op e1type e2type
    | Or
    | And -> check_bool_op e1type e2type
    )

| If (guard, tbranch, fbranch) -> 
  let type_guard = typecheck gamma guard in
  if type_guard = TBool then
    let type_tb = typecheck gamma tbranch in
    let type_fb = typecheck gamma fbranch in
    (if type_tb = type_fb then 
      type_tb 
      else raise (TypeError "if branches different types")) 
  else raise (TypeError "if guard not a bool")

| App (e1, e2) -> 
  let e1type = typecheck gamma e1 in
  let e2type = typecheck gamma e2 in
  (match e1type, e2type with
  | TArrow (a, b), x -> 
    if is_subtype x a then b else raise (TypeError "app issue1")
  | TArrow (TArrow (a, b), c), TArrow (d, e) -> 
    if is_subtype a d && is_subtype b e then c else raise (TypeError "app issue2")
  | _ -> raise (TypeError "app issue 3"))
| Let (var, e1, e2) -> 
  let e1type = typecheck gamma e1 in
  let new_gamma = extend gamma var e1type in
  typecheck new_gamma e2

| LetRec (var, exptype, e1, e2) -> 
  let new_gamma = extend gamma var exptype in
  let e1type = typecheck new_gamma e1 in
  if exptype = e1type then 
    let new_env = extend new_gamma var e1type in
    typecheck new_env e2 else raise(TypeError "goopy")
| Record fields -> if fields = [] then TRec [] else 
  TRec (List.fold_right (fun x a -> match x with
  | (Lab l, v2) -> (Lab l, typecheck gamma v2) :: a
  | _ -> raise (TypeError "invalid record field")) fields [])

| Select (label, record) -> 
  (match label with
  | Lab id -> 
    (match record with
    | Record f -> 
      let lst = (List.fold_left (fun a x -> 
        match x with
        | (Lab l, v2) -> if label = Lab l then [typecheck gamma v2] @ a else a
        | _ -> raise (TypeError "invalid record field")) [] f) in 
      if List.length lst = 0 then raise (SelectError "no select label found") else 
        List.nth lst (List.length lst - 1)
    | ID x -> 
      (match lookup gamma x with
      | TRec f -> 
        let lst = List.fold_right (fun curr a -> 
        match curr with
        | (Lab id2, x) -> if id = id2 then [x] @ a else a
        | _ -> raise (TypeError "invalid record field5")) f [] in
        List.nth lst 0
      | _ -> raise (TypeError "id in select isn't a record")) (*not too sure about this part*)
    | _ -> raise (TypeError "invalid record fiels"))
  | _ -> raise (TypeError "invalid select label type"))


| _ -> failwith "hi"


and check_num_op t1 t2 = match t1, t2 with
| (TInt, TInt) -> TInt
| _ -> raise (TypeError "num binop check failed")

and check_eq_op t1 t2 = match t1, t2 with
| (TInt, TInt) 
| (TBool, TBool) -> TBool
| _ -> raise (TypeError "equal binop check failed")

and check_bool_op t1 t2 = match t1, t2 with
| (TBool, TBool) -> TBool
| _ -> raise (TypeError "incorrect and/or types")

