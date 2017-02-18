// From http://okmij.org/ftp/Computation/FLOLAC/lecture.pdf
// Interpreting Types as Abstract Values

type Result<'a,'b> = Succ of 'b | Fail of 'a

let either f s = function
    | Succ x -> s x
    | Fail x -> f x

let (|?>) x f = either Fail f x

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
        match t2 with
        | TV v2 when v1 = v2 -> Succ tve
        | _ when occurs v1 t2 tve -> Fail <| sprintf "occurs check: %A in %A" (TV v1) (tvsub tve t2)
        | _ -> Succ <| tvext tve (v1,t2) // record new constraint

    and occurs v t tve =
        match t with
        | TInt -> false
        | TArr(t1,t2) -> occurs v t1 tve || occurs v t2 tve
        | TV v2 ->
            match tvlkup tve v2 with
            | None -> v = v2 
            | Some t -> occurs v t tve

    unify' (tvchase tve t1) (tvchase tve t2) tve

type TEnv = Map<VarName, Typ>

let lkup env x = 
    match Map.tryFind x env with
    | Some v -> v
    | None -> failwithf "Unbound variable %A" x

let env0 = Map.empty
let ext k v m = Map.add k v m

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
        match unify t_c TInt tve with
        | Succ tve -> 
            match unify t_tr t_fa tve with
            | Succ tve -> t_tr,tve
            | Fail err -> failwithf "The two branches of if do not match. %s" err
        | Fail err -> failwithf "Wrong type in the conditional of ifz: %s" err


let teval tenv e =
    let t,tve = teval' tenv e tve0
    tvsub tve t

let (|+) a b = Plus(a,b)
let (|%) a b = A(a,b)
let L x f = L(x,f)
let IFZ c t f = IFZ(c,t,f)

let (vx,vy) = (V "x", V "y")

let test0 = teval' env0 ((L "x" (vx |+ (I 2))) |% (I 1)) tve0
// (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))
let term1 = L "x" (IFZ vx (I 1) (vx |+ (I 2)))
let test10 = teval' env0 term1 tve0
// (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))

let test1 = teval env0 term1 // TInt :> TInt

let tmul = 
    Fix (L "self" 
            (L "x" 
                (L "y"
                    (IFZ 
                        vx 
                        (I 0)
                        (((V "self") |% (vx |+ (I (-1))) |% vy) |+ vy)))))

let testm21 = teval env0 tmul // TInt :> TInt :> TInt
let testm22 = teval env0 (tmul |% (I 2)) // TInt :> TInt
let testm23 = teval env0 (tmul |% (I 2) |% (I 3)) // TInt
let testm24 = teval env0 (tmul |% (I (-1)) |% (I (-1))) // TInt

//let term4 = L "x" (IFZ vx (I 1) (vx |% (I 1)))
//let test4 = teval env0 term4
// *** Exception: Trying to compare a non-integer to 0:
// constant mismatch: TInt :> TV 1 and TInt

//let delta = L "y" (vy |% vy)
//let testd = teval env0 delta
// *** Exception: occurs check: TV 0 in TV 0 :> TV 1

let term2a = L "x" (L "y" (vx |% vy))
let test2a = teval env0 term2a
// (TV 1 :> TV 2) :> (TV 1 :> TV 2)

let termid = L "x" vx
let testid = teval env0 termid 
// TV 0 :> TV 0

let term2id = 
    L "f" 
        (L "y" 
            ((I 2) |+ ((termid |% (V "f")) |% ((termid |% vy) |+ (I 1)))))
let test2id = teval env0 term2id // (TInt :> TInt) :> (TInt :> TInt)

let termlet = 
    let c2 = L "f" (L "x" (V "f" |% (V "f" |% vx)))
    let inc = L "x" (vx |+ (I 1))
    let compose = 
        L "f" 
            (L "g" 
                (L "x"
                    (V "f" |% (V "g" |% vx))))
    c2 |% (compose |% inc |% inc) |% (I 10) |+ ((c2 |% (compose |% inc) |% termid) |% (I 100))

let testlet = teval env0 termlet