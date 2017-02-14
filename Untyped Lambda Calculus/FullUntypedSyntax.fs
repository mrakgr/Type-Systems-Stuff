[<AutoOpen>]
module FullUntyped.Syntax

type info = FI of string * int * int | UNKNOWN
type 'a withinfo = {i: info; v: 'a}

let dummyinfo = UNKNOWN
let createInfo f l c = FI(f, l, c)

(* ---------------------------------------------------------------------- *)
(* Datatypes *)

type term =
| TmTrue of info
| TmFalse of info
| TmIf of info * term * term * term
| TmVar of info * int * int
| TmAbs of info * string * term
| TmApp of info * term * term
| TmRecord of info * (string * term) list
| TmProj of info * term * string
| TmFloat of info * float
| TmTimesfloat of info * term * term
| TmString of info * string
| TmZero of info
| TmSucc of info * term
| TmPred of info * term
| TmIsZero of info * term
| TmLet of info * string * term * term

type binding =
| NameBind 
| TmAbbBind of term

type context = (string * binding) list

type command =
| Eval of info * term
| Bind of info * string * binding

(* ---------------------------------------------------------------------- *)
(* Context management *)

let emptycontext = []

let ctxlength ctx = List.length ctx

let addbinding ctx x bind = (x,bind)::ctx

let addname ctx x = addbinding ctx x NameBind

let rec isnamebound ctx x =
    match ctx with
    | [] -> false
    | (y,_)::rest ->
        if y=x then true
        else isnamebound rest x

let rec pickfreshname ctx x =
  if isnamebound ctx x then pickfreshname ctx (x + "'")
  else ((x,NameBind)::ctx), x

let printInfo = function
  | FI(f,l,c) -> sprintf "%s:%i.%i:" f l c
  | UNKNOWN -> "<Unknown file and line>: "

let error fi s = 
    failwithf "Error:%s\n%s\n" (printInfo fi) s

let index2name fi ctx x =
  try
    let (xn,_) = List.item x ctx
    xn
  with Failure _ ->
    let msg = sprintf "Variable lookup failure: offset: %d, ctx size: %d"
    error fi (msg x (List.length ctx))

let rec name2index fi ctx x =
  match ctx with
      [] -> error fi ("Identifier " + x + " is unbound")
    | (y,_)::rest ->
        if y=x then 0
        else 1 + (name2index fi rest x)

(* ---------------------------------------------------------------------- *)
(* Shifting *)

let tmmap onvar c t = 
    let rec walk c t = 
        match t with
        | TmTrue(fi) as t -> t
        | TmFalse(fi) as t -> t
        | TmIf(fi,t1,t2,t3) -> TmIf(fi,walk c t1,walk c t2,walk c t3)
        | TmVar(fi,x,n) -> onvar fi c x n
        | TmAbs(fi,x,t2) -> TmAbs(fi,x,walk (c+1) t2)
        | TmApp(fi,t1,t2) -> TmApp(fi,walk c t1,walk c t2)
        | TmProj(fi,t1,l) -> TmProj(fi,walk c t1,l)
        | TmRecord(fi,fields) ->
            TmRecord(fi,List.map (fun (li,ti) -> (li,walk c ti)) fields)
        | TmFloat _ as t -> t
        | TmTimesfloat(fi,t1,t2) -> TmTimesfloat(fi, walk c t1, walk c t2)
        | TmString _ as t -> t
        | TmZero(fi)      -> TmZero(fi)
        | TmSucc(fi,t1)   -> TmSucc(fi, walk c t1)
        | TmPred(fi,t1)   -> TmPred(fi, walk c t1)
        | TmIsZero(fi,t1) -> TmIsZero(fi, walk c t1)
        | TmLet(fi,x,t1,t2) -> TmLet(fi,x,walk c t1,walk (c+1) t2)
    walk c t

let termShiftAbove d c t =
    tmmap (fun fi c x n -> if x>=c then TmVar(fi,x+d,n+d) else TmVar(fi,x,n+d)) c t

let termShift d t = termShiftAbove d 0 t

let bindingshift d bind =
    match bind with
    | NameBind -> NameBind
    | TmAbbBind(t) -> TmAbbBind(termShift d t)

(* ---------------------------------------------------------------------- *)
(* Substitution *)

let termSubst j s t =
    tmmap (fun fi c x n -> if x=j+c then termShift c s else TmVar(fi,x,n)) 0 t

let termSubstTop s t = 
    termShift (-1) (termSubst 0 (termShift 1 s) t)

(* ---------------------------------------------------------------------- *)
(* Context management (continued) *)

let rec getbinding fi ctx i =
  try
    let (_,bind) = List.item i ctx
    bindingshift (i+1) bind 
  with Failure _ ->
    let msg = Printf.sprintf "Variable lookup failure: offset: %d, ctx size: %d"
    error fi (msg i (List.length ctx))
 
(* ---------------------------------------------------------------------- *)
(* Extracting file info *)

let tmInfo t = 
    match t with
    | TmTrue(fi) | TmFalse(fi) | TmIf(fi,_,_,_) | TmVar(fi,_,_)
    | TmAbs(fi,_,_) | TmApp(fi, _, _) | TmProj(fi,_,_) | TmRecord(fi,_)
    | TmFloat(fi,_) | TmTimesfloat(fi,_,_) | TmString(fi,_) | TmZero(fi)
    | TmSucc(fi,_) | TmPred(fi,_) | TmIsZero(fi,_) | TmLet(fi,_,_,_) -> fi 
