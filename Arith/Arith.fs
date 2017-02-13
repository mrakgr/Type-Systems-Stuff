type Info = FI of string * int64 * int64 | UNKNOWN

let dummyinfo = UNKNOWN
let createInfo f l c = FI(f, l, c)

type Term =
    | TmTrue of Info
    | TmFalse of Info
    | TmIf of Info * Term * Term * Term
    | TmZero of Info
    | TmSucc of Info * Term
    | TmPred of Info * Term
    | TmIsZero of Info * Term

//type Command =
//    | Eval of Info * Term

(* ---------------------------------------------------------------------- *)
(* Parser *)

open FParsec

let skipComments = pstring "/*" >>. skipManyTill skipAnyChar (pstring "*/")
let spaces, spaces1 = 
    // Y Combinator
    let rec y f x = f (y f) x
    let spaces' x = y (fun f -> x >>. optional (skipComments >>. f))
    spaces' spaces, spaces' spaces1

let parseTerm, parseTermImpl = createParserForwardedToRef()
let getInfo (s: CharStream) = Reply(createInfo s.Name s.Line s.Column)

let parseTermParenths = between (pchar '(') (pchar ')') parseTerm
let parseTermInner = 
    [|spaces >>. parseTermParenths; spaces1 >>. parseTerm|]
    |> Array.map attempt
    |> choice
let parseTermOuter = spaces >>. (parseTermParenths <|> parseTerm) .>> (skipChar ';' <|> eof)

let parseUnExpr x v = pstring x >>. getInfo |>> v
let parseBiExpr x v =
    pipe2 
        (pstring x >>. parseTermInner)
        getInfo 
        (fun t1 info -> v (info,t1))

let pTrue = parseUnExpr "true" TmTrue
let pFalse = parseUnExpr "false" TmFalse
let pZero = parseUnExpr "0" TmZero

let pIf = 
    pipe4 
        (pstring "if" >>. parseTermInner)
        (spaces1 >>. pstring "then" >>. parseTermInner)
        (spaces1 >>. pstring "else" >>. parseTermInner)
        getInfo
        (fun t1 t2 t3 info -> TmIf(info,t1,t2,t3))

let pSucc = parseBiExpr "succ" TmSucc
let pPred = parseBiExpr "pred" TmPred
let pIsZero = parseBiExpr "iszero" TmIsZero

parseTermImpl := choice [pTrue;pFalse;pZero;pIf;pSucc;pPred;pIsZero]

(* ---------------------------------------------------------------------- *)
(* Printers *)

let printInfo =
  (* In the text of the book, file positions in error messages are replaced
     with the string "Error:" *)
  function
    FI(f,l,c) -> sprintf "%s:%i.%i:" f l c
  | UNKNOWN -> "<Unknown file and line>: "

let rec printTerm = function
    | TmTrue(_) -> "true"
    | TmFalse(_) -> "false"
    | TmIf(_,t1,t2,t3) -> 
        sprintf "(if %s then %s else %s)" (printTerm t1) (printTerm t2) (printTerm t3)
    | TmZero(_) -> "0"
    | TmSucc(_,t) -> sprintf "succ(%s)" (printTerm t)
    | TmPred(_,t) -> sprintf "pred(%s)" (printTerm t)
    | TmIsZero(_,t) -> sprintf "iszero(%s)" (printTerm t)

// I will skip those error functions in arith that are not being used.

(* ---------------------------------------------------------------------- *)
(* Extracting file info *)

let tmInfo = function
    | TmTrue(fi) | TmFalse(fi) | TmIf(fi,_,_,_)
    | TmZero(fi) | TmSucc(fi,_) | TmPred(fi,_)
    | TmIsZero(fi,_) -> fi 

(* ---------------------------------------------------------------------- *)
(* Evaluation functions *)

exception NoRuleApplies

let rec isnumericval = function
    | TmZero(_) -> true
    | TmSucc(_,t1) -> isnumericval t1
    | _ -> false

let rec isval = function
    | TmTrue(_)  -> true
    | TmFalse(_) -> true
    | t when isnumericval t  -> true
    | _ -> false

let rec eval1 = function
  | TmIf(_,TmTrue(_),t2,t3) -> t2 // According to semantics specified on page 34, t2 is not evaled here.
  | TmIf(_,TmFalse(_),t2,t3) -> t3 // Nor is t3 here.
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 t1
      TmIf(fi, t1', t2, t3)
  | TmSucc(fi,t1) ->
      let t1' = eval1 t1
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 t1 in
      TmIsZero(fi, t1')
  | _ -> 
      raise NoRuleApplies

let rec eval t =
    try let t' = eval1 t
        in eval t'
    with NoRuleApplies -> t

(* ---------------------------------------------------------------------- *)
(* Main *)

// Unlike the Ocaml version which is ran from the command line, I'll just slap a GUI here.

let test = 
    """/* Examples for testing */
true;
if false then true else false; 

0; 
succ (pred 0);
iszero (pred (succ (succ 0)));"""

let evalAll test = 
    runParserOnString (many parseTermOuter) () "test" test
    |> function
        | Success(r,_,_) -> 
            List.map (eval >> printTerm) r
            |> String.concat ";\n"
        | Failure(x,_,_) -> x

open System
open System.Windows
open System.Windows.Input
open System.Windows.Controls
open System.Windows.Controls.Primitives
open System.Windows.Media
open System.Windows.Media.Imaging
open System.Windows.Shapes
open System.Windows.Documents
open System.Windows.Threading
open System.Windows.Data

open Bindings

[<STAThread; EntryPoint>]
let main args =
    let win = Window(Title="Arith",SizeToContent=SizeToContent.WidthAndHeight,MinWidth=500.0,MinHeight=300.0)
    let grid =
        Grid()
        |> addRowDefs
            [|
            RowDefinition(Height=GridLength.Auto)
            RowDefinition(Height=GridLength.Auto)
            RowDefinition(Height=GridLength.Auto)
            |]
        |> setAsContentFor win
    
    let btn_eval = 
        Button(Content="Evaluate",HorizontalAlignment=HorizontalAlignment.Center)
        |> addGrid grid 2 0

    let txt_eval = 
        TextBlock(Text="")
        |> addGrid grid 1 0
    
    let txt_code =
        TextBox(Text=test)
        |> addGrid grid 0 0

    btn_eval.Click.Add <| fun _ ->
        txt_eval.Text <- evalAll txt_code.Text

    Application().Run(win)