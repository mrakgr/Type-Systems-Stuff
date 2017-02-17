type VarName = string
type Term =
  | V of VarName
  | L of VarName * Term
  | A of Term * Term
  | I of int
  | Plus of Term * Term
  | IFZ of Term * Term * Term
  | Fix of Term

type TVarName = int
type Typ = TInt | TArr of Typ * Typ | TV of TVarName

type TVE = TVE of int * Map<TVarName,Typ>

let newtv (TVE(n, s)) = (TV n, TVE ((n+1), s))

let tve0 = TVE(0, Map.empty)
let tvlkup (TVE(_, s)) v = Map.tryFind v s
let tvext (TVE(c, s)) (tv,t) = TVE(c, (Map.add tv t s))

let rec tvsub tve = function
    | TArr(t1, t2) -> TArr(tvsub tve t1, tvsub tve t2)
    | TV v as t ->
        match tvlkup tve v with
        | Some t -> tvsub tve t
        | None -> t
    | t -> t

// chase through a substitution ‘shallowly’:
// stop at the last equivalent type variable
let tvchase tve = function
    | TV v as t ->
        match tvlkup tve v with
        | Some t -> tvsub tve t
        | None -> t
    | t -> t

type Result<'a,'b> = Succ of 'b | Fail of 'a

let either f s = function
    | Succ x -> s x
    | Fail x -> f x

let (|?>) x f = either Fail f x

let rec unify t1 t2 tve = 
    // If either t1 or t2 are type variables, they must be unbound
    let rec unify' t1 t2 tve =
        match t1, t2 with
        | _ when t1 = t2 -> Succ tve
        | TArr(t1a,t1r), TArr(t2a,t2r) -> 
            unify t1a t2a tve 
            |?> unify t1r t2r
        | TV v, t | t, TV v -> unifyv v t tve
        | t1, t2 -> Fail <| sprintf "constant mismatch: %A %A" t1 t2

    and unifyv v1 t2 tve =
//        I've rewriten occurs like so because the lookup might otherwise miss the case where
//        v1 and TV v2 are equal if it is called from outside of unifyv.
//        While Oleg's version works as intended, having the occurs function at the top level
//        definitely implies things about its structure that are false.
        let rec occurs v t tve =
            match t with
            | TInt -> false
            | TArr(t1,t2) -> occurs v t1 tve || occurs v t2 tve
            | TV v2 ->
                match tvlkup tve v2 with
                | None -> false // This is always false because of the `| TV v2 when v1 = v2 -> Succ tve` line
                | Some t -> occurs v t tve

        match t2 with
        | TV v2 when v1 = v2 -> Succ tve
        | _ when occurs v1 t2 tve -> Fail <| sprintf "occurs check: %A in %A" (TV v1) (tvsub tve t2)
        | _ -> Succ <| tvext tve (v1,t2) // record new constraint

    unify' (tvchase tve t1) (tvchase tve t2) tve

type TEnv = Map<VarName, Typ>

let lkup env x = 
    match Map.tryFind x env with
    | Some v -> v
    | None -> failwithf "Unbound variable %A" x

let env0() = Map.empty
let ext k v m = Map.add k v m

//teval' :: TEnv -> Term -> TVE -> (Typ,TVE)
let rec teval' tenv t tve =
  match t with
  | V x -> (lkup tenv x, tve)
  | L (x, e) ->
      let tx,tve = newtv tve
      let te,tve = teval' (ext x tx tenv) e tve
      (TArr(tx,te), tve)
  | A (e1, e2) ->
      let t1,tve = teval' tenv e1 tve
      let t2,tve = teval' tenv e2 tve
      let t1r,tve = newtv tve
      match unify t1 (TArr(t2, t1r)) tve with
      | Succ tve -> (t1r,tve)
      | Fail err -> failwith err
  | I n -> (TInt, tve)
  | Plus(e1, e2) ->
      let t1,tve = teval' tenv e1 tve
      let t2,tve = teval' tenv e2 tve
      match unify t1 TInt tve |?> unify t2 TInt with
      | Succ tve -> (TInt,tve)
      | Fail err -> failwithf "Trying to add non-integers: %s" err
  | Fix e ->
      let t,tve = teval' tenv e tve
      let ta,tve = newtv tve
      let tb,tve = newtv tve
      // It never occurred to me, but it maybe the `->` type arrows are right associative in ML?
      match unify t (TArr(TArr(ta, tb), TArr(ta,tb))) tve with
      | Succ tve -> (TArr(ta, tb),tve)
      | Fail err -> failwithf "Inappropriate type in Fix: %s" err
    | IFZ(c,tr,fa) ->
        let t_c, tve = teval' tenv c tve
        let t_tr, tve = teval' tenv tr tve
        let t_fa, tve = teval' tenv fa tve
        let _, tve = 
            match unify t_c TInt tve with
            | Succ tve -> TInt, tve
            | Fail err -> failwithf "Wrong type (%A) in the conditional of if: %s" t_c err
        match unify t_tr t_fa tve with
        | Succ tve -> t_tr,tve
        | Fail err -> failwith "The two branches of if do not match. The types are true(%A), false(%A): %s" t_tr t_fa err

let teval tenv e =
  let t,tve = teval' tenv e tve0
  tvsub tve t
