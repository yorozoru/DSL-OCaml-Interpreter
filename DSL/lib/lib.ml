open Utils
include My_parser

exception AssertFail
exception DivByZero
exception RecWithoutArg
exception CompareFunVals

let rec fvs = function
  | TUnit | TInt | TFloat | TBool -> VarSet.empty
  | TVar x -> VarSet.of_list [x]
  | TList t -> fvs t
  | TOption t -> fvs t
  | TPair (t1, t2) -> VarSet.union (fvs t1) (fvs t2) 
  | TFun (t1, t2) -> VarSet.union (fvs t1) (fvs t2)
  let ty_subst t x =
    let rec go = function
      | TInt -> TInt
      | TBool -> TBool
      | TUnit -> TUnit
      | TFloat -> TFloat
      | TList t1 -> TList (go t1)
      | TOption t1 -> TOption (go t1)
      | TPair (t1, t2) -> TPair (go t1, go t2)
      | TVar y -> if x = y then t else TVar y
      | TFun (t1, t2) -> TFun (go t1, go t2)
    in go

    let ty_subst_c t x (t1, t2) = (ty_subst t x t1, ty_subst t x t2)
    let ty_subst_cs t x = List.map (ty_subst_c t x)
  
    let unify ty cs =
        let rec go = function
          | [] -> Some []
          | [(TVar "_out", t)] -> Some [("_out",t)]
          | (t1, t2) :: cs when t1 = t2 -> go cs
          | (TFun (t1, t2), TFun (t1', t2')) :: cs ->
            go ((t1, t1') :: (t2, t2') :: cs)
          | (TVar x, t) :: cs | (t, TVar x) :: cs ->
            if VarSet.mem x (fvs t)
            then None
            else (
              let subst = (x, t) in
              match go (ty_subst_cs t x cs) with
              | Some s -> Some (subst :: s)
              | None -> None
            )
          | _ -> None
        in 
        match go cs with
        | Some s ->
          let final_ty = List.fold_left (fun acc (x, ty) -> ty_subst ty x acc) ty s in
          Some (Forall (VarSet.to_list (fvs final_ty), final_ty))
        | None -> None


let rec instantiate (Forall(vars, ty)) =
  match vars with
  | [] -> ty 
  | x :: xs ->
    let fresh = TVar (gensym()) in
    ty_subst fresh x (instantiate (Forall (xs, ty)))

let rec eval_expr (env : dyn_env) (expr : expr) : value =
  match expr with
  | Unit  -> VUnit
  | True -> VBool true
  | False -> VBool false
  | Int n -> VInt n
  | Float f -> VFloat f
  | Nil -> VList []
  | ENone -> VNone
  | ESome e -> VSome (eval_expr env e)
  | OptMatch {matched; some_name; some_case; none_case} ->
    (
      match eval_expr env matched with
      | VSome v -> eval_expr (Env.add some_name v env) some_case
      | VNone -> eval_expr env none_case
      | _ -> failwith "Type error in option match"
    )
    | Bop (op, e1, e2) ->
      (let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      match op with
      | Add -> (match v1, v2 with
          | VInt n1, VInt n2 -> VInt (n1 + n2)
          | _ -> failwith "Type error in addition")
      | Sub -> (match v1, v2 with 
          | VInt n1, VInt n2 -> VInt (n1 - n2)
          | _ -> failwith "Type error in subtraction")
      | Mul -> (match v1, v2 with
          | VInt n1, VInt n2 -> VInt (n1 * n2)
          | _ -> failwith "Type error in multiplication")
      | Div -> (match v1, v2 with
          | _, VInt n2 when n2 = 0 -> raise DivByZero
          | VInt n1, VInt n2 -> VInt (n1 / n2)
          | _ -> failwith "Type error in division")
      | Mod -> (match v1, v2 with
          | _, VInt n2 when n2 = 0 -> raise DivByZero
          | VInt n1, VInt n2 -> VInt (n1 mod n2)
          | _ -> failwith "Type error in modulo")
      | AddF -> (match v1, v2 with
          | VFloat f1, VFloat f2 -> VFloat (f1 +. f2)
          | _ -> failwith "Type error in float addition")
      | SubF -> (match v1, v2 with
          | VFloat f1, VFloat f2 -> VFloat (f1 -. f2)
          | _ -> failwith "Type error in float subtraction")
      | MulF -> (match v1, v2 with
          | VFloat f1, VFloat f2 -> VFloat (f1 *. f2)
          | _ -> failwith "Type error in float multiplication")
      | DivF -> (match v1, v2 with
          | VFloat f1, VFloat f2 -> VFloat (f1 /. f2)
          | _ -> failwith "Type error in float division")
      | PowF -> (match v1, v2 with
          | VFloat f1, VFloat f2 -> VFloat (f1 ** f2)
          | _ -> failwith "Type error in float power")
      | And -> (match v1 with
          | VBool false -> VBool false
          | VBool true -> v2
          | _ -> failwith "Type error in and")
      | Or -> (match v1 with
          | VBool true -> VBool true
          | VBool false -> v2
          | _ -> failwith "Type error in or")
      | Lt | Lte | Gt | Gte | Eq | Neq -> 
          (match v1, v2 with
          | VClos _, _ | _, VClos _ -> raise CompareFunVals
          | _ ->
            match op with
            | Lt -> VBool (match v1,v2 with
                | VUnit, VUnit -> false 
                | VBool b1, VBool b2 -> b1 < b2
                | VInt n1, VInt n2 -> n1 < n2
                | VFloat f1, VFloat f2 -> f1 < f2
                | VList l1, VList l2 -> compare_lists l1 l2 < 0
                | VPair(a1,b1), VPair(a2,b2) -> 
                    let c = compare_values a1 a2 in
                    if c = 0 then compare_values b1 b2 < 0 else c < 0
                | VNone, VSome _ -> true
                | VSome _, VNone -> false 
                | VSome v1', VSome v2' -> compare_values v1' v2' < 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> failwith "Type error in comparison")
            | Lte -> VBool (match v1,v2 with
                | VUnit, VUnit -> true
                | VBool b1, VBool b2 -> b1 <= b2
                | VInt n1, VInt n2 -> n1 <= n2
                | VFloat f1, VFloat f2 -> f1 <= f2
                | VList l1, VList l2 -> compare_lists l1 l2 <= 0
                | VPair(a1,b1), VPair(a2,b2) ->
                    let c = compare_values a1 a2 in
                    if c = 0 then compare_values b1 b2 <= 0 else c <= 0
                | VNone, VNone -> true
                | VNone, VSome _ -> true
                | VSome _, VNone -> false
                | VSome v1', VSome v2' -> compare_values v1' v2' <= 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> failwith "Type error in comparison")
            | Gt -> VBool (match v1,v2 with
                | VUnit, VUnit -> false
                | VBool b1, VBool b2 -> b1 > b2
                | VInt n1, VInt n2 -> n1 > n2
                | VFloat f1, VFloat f2 -> f1 > f2
                | VList l1, VList l2 -> compare_lists l1 l2 > 0
                | VPair(a1,b1), VPair(a2,b2) ->
                    let c = compare_values a1 a2 in
                    if c = 0 then compare_values b1 b2 > 0 else c > 0
                | VNone, _ -> false
                | VSome _, VNone -> true
                | VSome v1', VSome v2' -> compare_values v1' v2' > 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> failwith "Type error in comparison")
            | Gte -> VBool (match v1,v2 with
                | VUnit, VUnit -> true
                | VBool b1, VBool b2 -> b1 >= b2
                | VInt n1, VInt n2 -> n1 >= n2
                | VFloat f1, VFloat f2 -> f1 >= f2
                | VList l1, VList l2 -> compare_lists l1 l2 >= 0
                | VPair(a1,b1), VPair(a2,b2) ->
                    let c = compare_values a1 a2 in
                    if c = 0 then compare_values b1 b2 >= 0 else c >= 0
                | VNone, VNone -> true
                | VNone, VSome _ -> false
                | VSome _, VNone -> true
                | VSome v1', VSome v2' -> compare_values v1' v2' >= 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> failwith "Type error in comparison")
            | Eq -> VBool (match v1,v2 with
                | VUnit, VUnit -> true
                | VBool b1, VBool b2 -> b1 = b2
                | VInt n1, VInt n2 -> n1 = n2
                | VFloat f1, VFloat f2 -> f1 = f2
                | VList l1, VList l2 -> compare_lists l1 l2 = 0
                | VPair(a1,b1), VPair(a2,b2) ->
                    compare_values a1 a2 = 0 && compare_values b1 b2 = 0
                | VNone, VNone -> true
                | VSome v1', VSome v2' -> compare_values v1' v2' = 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> false)
            | Neq -> VBool (match v1,v2 with
                | VUnit, VUnit -> false
                | VBool b1, VBool b2 -> b1 <> b2
                | VInt n1, VInt n2 -> n1 <> n2
                | VFloat f1, VFloat f2 -> f1 <> f2
                | VList l1, VList l2 -> compare_lists l1 l2 <> 0
                | VPair(a1,b1), VPair(a2,b2) ->
                    compare_values a1 a2 <> 0 || compare_values b1 b2 <> 0
                | VNone, VNone -> false
                | VSome v1', VSome v2' -> compare_values v1' v2' <> 0
                | VClos _, _ | _, VClos _ -> raise CompareFunVals
                | _ -> true)
            | _ -> failwith "Impossible case")
      | Concat -> (match v1, v2 with
          | VList l1, VList l2 -> VList (l1 @ l2)
          | _ -> failwith "Type error in concat")
      | Cons -> (match v2 with
          | VList l -> VList (v1::l)
          | _ -> failwith "Type error in cons")
      | _ -> failwith "Type error in operator")
    | ListMatch {matched; hd_name; tl_name; cons_case; nil_case} ->
      (match eval_expr env matched with
      | VList (h::t) -> 
      let env' = Env.add hd_name h (Env.add tl_name (VList t) env) in
      eval_expr env' cons_case
      | VList [] -> eval_expr env nil_case
      | _ -> failwith "Error in List Match")
    | PairMatch {matched; fst_name; snd_name; case} ->
       (match eval_expr env matched with
        | VPair (v1, v2) -> 
            let env' = Env.add fst_name v1 (Env.add snd_name v2 env) in
            eval_expr env' case
        | _ -> failwith "Type error in pair match")
    | Var x -> 
          (match Env.find_opt x env with
           | Some v -> v
           | None -> failwith ("Unbound variable: " ^ x))
    | Annot (e1,_) -> eval_expr env e1
    | Assert (e1) -> 
      (match eval_expr env e1 with
       | VBool true -> VUnit
       | VBool false -> raise AssertFail
       | _ -> failwith "Type error in assert")
    | If (e1,e2,e3) ->
      (match eval_expr env e1 with
      | VBool true -> eval_expr env e2
      | VBool false -> eval_expr env e3
      | _ -> failwith "Conditional failure")
    | Fun (x, _, body) -> VClos {name = None; arg = x; body; env}
    | App (e1, e2) ->
      (let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      match v1 with
       | VClos {name = None; arg; body; env = env'} ->
           eval_expr (Env.add arg v2 env') body
       | VClos {name = Some f; arg; body; env = env'} ->
           let env'' = Env.add f v1 env' in
           eval_expr (Env.add arg v2 env'') body
       | _ -> failwith "Type error in application")
    | Let {is_rec = false; name; value; body} ->
        (let v = eval_expr env value in
        eval_expr (Env.add name v env) body)
  
    | Let {is_rec = true; name; value; body} ->
        (let closure = eval_expr env value in
        match closure with
        | VClos {name = None; arg; body = fn_body; env = closure_env} ->
            let rec_closure = VClos {name = Some name; arg; body = fn_body; env = closure_env} in
            eval_expr (Env.add name rec_closure env) body
        | VClos {name = Some _; _} -> raise RecWithoutArg
        | _ -> failwith "Type error in recursive let")
    and compare_values v1 v2 =
      match v1, v2 with
      | VUnit, VUnit -> 0
      | VBool b1, VBool b2 -> compare b1 b2
      | VInt n1, VInt n2 -> compare n1 n2
      | VFloat f1, VFloat f2 -> compare f1 f2
      | VList l1, VList l2 -> compare_lists l1 l2
      | VPair (a1,b1), VPair (a2,b2) ->
          let c = compare_values a1 a2 in
          if c = 0 then compare_values b1 b2 else c
      | VNone, VNone -> 0
      | VNone, VSome _ -> -1
      | VSome _, VNone -> 1
      | VSome v1, VSome v2 -> compare_values v1 v2
      | _ -> failwith "Type error in comparison"
      and compare_lists l1 l2 =
        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | h1::t1, h2::t2 ->
            let c = compare_values h1 h2 in
            if c = 0 then compare_lists t1 t2 else c

let type_of (gamma : stc_env) (expr : expr) : ty_scheme option =
  let rec go gamma expr =
    match expr with
    | Unit -> (TUnit, [])
    | True | False -> (TBool, [])
    | Int _ -> (TInt, [])
    | Float _ -> (TFloat, [])
    | Nil -> 
        let fresh = TVar (gensym()) in
        (TList fresh, [])
    | ENone ->
        let fresh = TVar (gensym()) in
        (TOption fresh, [])
    | ESome e ->
       let t1, c1 = go gamma e in
       (TOption t1, (c1))
    | Assert e ->
      (match e with
      | False -> 
          let fresh = TVar (gensym()) in
          (fresh, [])
      | _ ->
          let t, c = go gamma e in
          (TUnit, (t, TBool) :: c))
    | If (e1, e2, e3) ->
        let t1, c1 = go gamma e1 in
        let t2, c2 = go gamma e2 in 
        let t3, c3 = go gamma e3 in
        (t2, (t1, TBool) :: (t2, t3) :: (c1 @ c2 @ c3))
    | Var x ->
      (match Env.find_opt x gamma with
      | Some (Forall (s, t)) ->
          (instantiate (Forall (s, t)), [])
      | None -> failwith ("Unbound variable: " ^ x))
    | App (e1, e2) ->
        let t1, c1 = go gamma e1 in
        let t2, c2 = go gamma e2 in
        let tv = TVar (gensym()) in
        (tv, (t1, TFun(t2, tv)) :: (c1 @ c2))
    | Let {is_rec; name; value; body} ->
        if is_rec then
          let fn_ty = TVar (gensym()) in
          let ret_ty = TVar (gensym()) in
          let gamma' = Env.add name (Forall ([], TFun(fn_ty, ret_ty))) gamma in
          let t1, c1 = go gamma' value in
          let t2, c2 = go (Env.add name (Forall ([], t1)) gamma) body in
          (t2, (t1, TFun(fn_ty, ret_ty)) :: (c1 @ c2))
        else
          let t1, c1 = go gamma value in
          let t2, c2 = go (Env.add name (Forall ([], t1)) gamma) body in
          (t2, c1 @ c2)
    | Fun (x, ty_opt, e) ->
        let args = match ty_opt with
          | Some t -> t
          | None -> TVar (gensym()) in
        let gamma' = Env.add x (Forall ([], args)) gamma in
        let ret_ty, c = go gamma' e in
        (TFun (args, ret_ty), c)
    | Annot (e, ty) ->
        let t, c = go gamma e in
        (ty, (t, ty) :: c)
    | Bop (op, e1, e2) ->
        (let t1, c1 = go gamma e1 in
        let t2, c2 = go gamma e2 in
        match op with
        | Add | Sub | Mul | Div | Mod -> 
            (TInt, (t1, TInt) :: (t2, TInt) :: (c1 @ c2))
        | AddF | SubF | MulF | DivF | PowF ->
            (TFloat, (t1, TFloat) :: (t2, TFloat) :: (c1 @ c2))
        | Lt | Lte | Gt | Gte | Eq | Neq ->
            (TBool, (t1, t2) :: (c1 @ c2))
        | And | Or ->
            (TBool, (t1, TBool) :: (t2, TBool) :: (c1 @ c2))
        | Cons ->
            (TList t1, (t2, TList t1) :: (c1 @ c2))
        | Concat ->
            let tv = TVar (gensym()) in
            (TList tv, (t1, TList tv) :: (t2, TList tv) :: (c1 @ c2))
        | Comma ->
            (TPair(t1, t2), c1 @ c2))
    | ListMatch {matched; hd_name; tl_name; cons_case; nil_case} ->
        let t, c = go gamma matched in
        let elem_ty = TVar (gensym()) in
        let gamma' = Env.add hd_name (Forall([],elem_ty))
                    (Env.add tl_name (Forall([],TList elem_ty)) gamma) in
        let t1, c1 = go gamma' cons_case in
        let t2, c2 = go gamma nil_case in
        (t2, (t, TList elem_ty) :: (t1, t2) :: (c @ c1 @ c2))

    | OptMatch {matched; some_name; some_case; none_case} ->
        let t, c = go gamma matched in
        let elem_ty = TVar (gensym()) in
        let gamma' = Env.add some_name (Forall([],elem_ty)) gamma in
        let t1, c1 = go gamma' some_case in
        let t2, c2 = go gamma none_case in
        (t2, (t, TOption elem_ty) :: (t1, t2) :: (c @ c1 @ c2))

    | PairMatch {matched; fst_name; snd_name; case} ->
           (let t, c = go gamma matched in
            let alpha = TVar (gensym ()) in
            let beta = TVar (gensym ()) in
            let gamma' = Env.add fst_name (Forall ([], alpha)) (Env.add snd_name (Forall ([], beta)) gamma) in
            let t', c' = go gamma' case in
            (t', (t, TPair (alpha, beta)) :: (c @ c')))
  in
  let ty, constrs = go gamma expr in
  unify ty constrs

let type_check =
  let rec go ctxt = function
  | [] -> Some (Forall ([], TUnit))
  | {is_rec;name;value} :: ls ->
    match type_of ctxt (Let {is_rec;name;value; body = Var name}) with
    | Some ty -> (
      match ls with
      | [] -> Some ty
      | _ ->
        let ctxt = Env.add name ty ctxt in
        go ctxt ls
    )
    | None -> None
  in go Env.empty


  let eval p =
    let rec nest = function
      | [] -> Unit
      | [{is_rec;name;value}] -> Let {is_rec;name;value;body = Var name}
      | {is_rec;name;value} :: ls -> Let {is_rec;name;value;body = nest ls}
    in eval_expr Env.empty (nest p)
let interp input =
  match parse input with
  | Some prog -> (
    match type_check prog with
    | Some ty -> Ok (eval prog, ty)
    | None -> Error TypeError
  )
  | None -> Error ParseError
