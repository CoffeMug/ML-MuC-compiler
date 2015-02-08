
functor UCLrValsFn(structure Token : TOKEN
			    structure Absyn : ABSYN
			    structure LexArg : LEXARG) : UC_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct
(* parser/uc.grm
 *)

(* represent left-recursive sequences *)
datatype 'a seq
  = SINGLE of 'a
  | SEQ of 'a seq * 'a

(* convert a left-recursive sequence to a normal list *)
fun seqToList2(SINGLE(x), xs) = x::xs
  | seqToList2(SEQ(seq,x), xs) = seqToList2(seq, x::xs)
fun seqToList(seq) = seqToList2(seq, [])


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\121\000\003\000\121\000\004\000\121\000\007\000\121\000\
\\008\000\121\000\009\000\121\000\010\000\121\000\016\000\107\000\
\\017\000\070\000\018\000\121\000\019\000\121\000\020\000\121\000\
\\021\000\121\000\023\000\121\000\024\000\121\000\028\000\121\000\000\000\
\\001\000\001\000\122\000\003\000\122\000\004\000\122\000\007\000\122\000\
\\008\000\122\000\009\000\122\000\010\000\122\000\018\000\122\000\
\\019\000\122\000\020\000\122\000\021\000\122\000\023\000\122\000\
\\024\000\122\000\028\000\122\000\000\000\
\\001\000\001\000\124\000\003\000\124\000\004\000\124\000\007\000\124\000\
\\008\000\124\000\009\000\124\000\010\000\124\000\018\000\124\000\
\\019\000\124\000\020\000\124\000\021\000\124\000\023\000\124\000\
\\024\000\124\000\028\000\124\000\000\000\
\\001\000\001\000\130\000\003\000\130\000\004\000\068\000\007\000\130\000\
\\008\000\130\000\020\000\061\000\021\000\060\000\023\000\130\000\
\\024\000\058\000\026\000\130\000\028\000\130\000\029\000\130\000\000\000\
\\001\000\001\000\131\000\003\000\131\000\004\000\068\000\007\000\131\000\
\\008\000\131\000\020\000\061\000\021\000\060\000\023\000\131\000\
\\024\000\058\000\026\000\131\000\028\000\131\000\029\000\131\000\000\000\
\\001\000\001\000\132\000\003\000\132\000\004\000\068\000\007\000\132\000\
\\008\000\132\000\020\000\061\000\021\000\060\000\023\000\132\000\
\\024\000\058\000\026\000\132\000\028\000\132\000\029\000\132\000\000\000\
\\001\000\001\000\133\000\003\000\133\000\004\000\068\000\007\000\133\000\
\\008\000\133\000\020\000\061\000\021\000\060\000\023\000\133\000\
\\024\000\058\000\026\000\133\000\028\000\133\000\029\000\133\000\000\000\
\\001\000\001\000\140\000\003\000\140\000\004\000\068\000\007\000\067\000\
\\008\000\066\000\009\000\065\000\010\000\064\000\018\000\063\000\
\\019\000\062\000\020\000\061\000\021\000\060\000\023\000\059\000\
\\024\000\058\000\028\000\140\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\026\000\108\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\026\000\116\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\028\000\101\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\028\000\109\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\028\000\110\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\029\000\057\000\000\000\
\\001\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\
\\029\000\100\000\000\000\
\\001\000\002\000\009\000\013\000\008\000\030\000\007\000\000\000\
\\001\000\002\000\009\000\013\000\008\000\030\000\024\000\000\000\
\\001\000\003\000\032\000\028\000\031\000\000\000\
\\001\000\006\000\000\000\000\000\
\\001\000\011\000\013\000\000\000\
\\001\000\011\000\013\000\012\000\052\000\014\000\051\000\015\000\050\000\
\\017\000\049\000\020\000\048\000\022\000\047\000\025\000\055\000\
\\027\000\046\000\029\000\045\000\031\000\044\000\000\000\
\\001\000\011\000\013\000\012\000\052\000\014\000\051\000\015\000\050\000\
\\017\000\049\000\020\000\048\000\022\000\047\000\025\000\102\000\
\\027\000\046\000\029\000\045\000\031\000\044\000\000\000\
\\001\000\011\000\013\000\012\000\052\000\014\000\051\000\015\000\050\000\
\\017\000\049\000\020\000\048\000\022\000\047\000\027\000\046\000\
\\029\000\045\000\031\000\044\000\000\000\
\\001\000\011\000\013\000\014\000\051\000\017\000\049\000\020\000\142\000\000\000\
\\001\000\011\000\013\000\014\000\051\000\017\000\049\000\020\000\048\000\
\\022\000\047\000\000\000\
\\001\000\011\000\013\000\014\000\051\000\017\000\049\000\020\000\048\000\
\\022\000\047\000\029\000\074\000\000\000\
\\001\000\011\000\013\000\014\000\097\000\017\000\049\000\020\000\048\000\
\\022\000\047\000\000\000\
\\001\000\014\000\026\000\026\000\025\000\000\000\
\\001\000\015\000\020\000\029\000\019\000\000\000\
\\001\000\017\000\072\000\000\000\
\\001\000\017\000\079\000\000\000\
\\001\000\026\000\036\000\000\000\
\\001\000\028\000\105\000\000\000\
\\001\000\029\000\014\000\000\000\
\\120\000\000\000\
\\121\000\016\000\071\000\017\000\070\000\000\000\
\\122\000\000\000\
\\123\000\000\000\
\\124\000\000\000\
\\125\000\000\000\
\\126\000\001\000\069\000\004\000\068\000\007\000\067\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\000\000\
\\127\000\004\000\068\000\007\000\067\000\008\000\066\000\009\000\065\000\
\\010\000\064\000\018\000\063\000\019\000\062\000\020\000\061\000\
\\021\000\060\000\023\000\059\000\024\000\058\000\000\000\
\\128\000\004\000\068\000\007\000\067\000\008\000\066\000\009\000\065\000\
\\010\000\064\000\018\000\063\000\019\000\062\000\020\000\061\000\
\\021\000\060\000\023\000\059\000\024\000\058\000\000\000\
\\129\000\004\000\068\000\009\000\065\000\010\000\064\000\018\000\063\000\
\\019\000\062\000\020\000\061\000\021\000\060\000\024\000\058\000\000\000\
\\134\000\004\000\068\000\021\000\060\000\000\000\
\\135\000\004\000\068\000\021\000\060\000\000\000\
\\136\000\000\000\
\\137\000\000\000\
\\138\000\000\000\
\\139\000\004\000\068\000\021\000\060\000\000\000\
\\140\000\004\000\068\000\007\000\067\000\008\000\066\000\009\000\065\000\
\\010\000\064\000\018\000\063\000\019\000\062\000\020\000\061\000\
\\021\000\060\000\023\000\059\000\024\000\058\000\000\000\
\\141\000\011\000\013\000\014\000\051\000\017\000\049\000\022\000\047\000\000\000\
\\154\000\011\000\013\000\014\000\097\000\017\000\049\000\020\000\048\000\
\\022\000\047\000\000\000\
\\155\000\003\000\104\000\000\000\
\\156\000\000\000\
\\157\000\000\000\
\\162\000\001\000\069\000\004\000\068\000\007\000\106\000\008\000\066\000\
\\009\000\065\000\010\000\064\000\018\000\063\000\019\000\062\000\
\\020\000\061\000\021\000\060\000\023\000\059\000\024\000\058\000\000\000\
\\163\000\000\000\
\\164\000\000\000\
\\165\000\000\000\
\\166\000\005\000\117\000\000\000\
\\167\000\000\000\
\\168\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\000\000\
\\174\000\000\000\
\\175\000\000\000\
\\176\000\002\000\009\000\013\000\008\000\030\000\007\000\000\000\
\\177\000\002\000\009\000\013\000\008\000\030\000\007\000\000\000\
\\178\000\000\000\
\\179\000\000\000\
\\180\000\000\000\
\\181\000\000\000\
\\182\000\000\000\
\\182\000\028\000\035\000\000\000\
\\183\000\016\000\017\000\000\000\
\\183\000\016\000\017\000\017\000\016\000\000\000\
\\184\000\000\000\
\\185\000\000\000\
\\186\000\002\000\009\000\013\000\008\000\030\000\007\000\000\000\
\\187\000\000\000\
\\188\000\000\000\
\\189\000\000\000\
\\190\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\000\000\
\"
val actionRowNumbers =
"\015\000\083\000\082\000\019\000\
\\087\000\076\000\075\000\074\000\
\\084\000\033\000\079\000\034\000\
\\069\000\028\000\016\000\027\000\
\\085\000\086\000\070\000\090\000\
\\017\000\019\000\077\000\081\000\
\\031\000\019\000\071\000\022\000\
\\072\000\089\000\015\000\092\000\
\\078\000\088\000\080\000\073\000\
\\020\000\057\000\067\000\024\000\
\\013\000\035\000\029\000\059\000\
\\025\000\023\000\051\000\024\000\
\\022\000\036\000\030\000\091\000\
\\068\000\066\000\040\000\058\000\
\\024\000\024\000\024\000\024\000\
\\024\000\024\000\024\000\024\000\
\\024\000\024\000\024\000\024\000\
\\052\000\024\000\024\000\014\000\
\\064\000\048\000\049\000\010\000\
\\021\000\024\000\045\000\043\000\
\\047\000\044\000\005\000\003\000\
\\004\000\006\000\042\000\050\000\
\\046\000\041\000\054\000\053\000\
\\032\000\056\000\000\000\001\000\
\\008\000\011\000\063\000\037\000\
\\065\000\012\000\026\000\039\000\
\\024\000\024\000\038\000\022\000\
\\022\000\055\000\007\000\009\000\
\\062\000\060\000\002\000\022\000\
\\061\000\018\000"
val gotoT =
"\
\\012\000\004\000\015\000\003\000\017\000\117\000\018\000\002\000\
\\019\000\001\000\000\000\
\\000\000\
\\012\000\004\000\015\000\003\000\019\000\008\000\000\000\
\\001\000\010\000\016\000\009\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\020\000\013\000\000\000\
\\000\000\
\\000\000\
\\010\000\016\000\000\000\
\\015\000\021\000\021\000\020\000\022\000\019\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\012\000\028\000\013\000\027\000\014\000\026\000\015\000\025\000\000\000\
\\000\000\
\\000\000\
\\001\000\032\000\016\000\031\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\032\000\016\000\009\000\000\000\
\\012\000\035\000\015\000\025\000\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\038\000\
\\009\000\037\000\011\000\036\000\000\000\
\\000\000\
\\000\000\
\\015\000\021\000\022\000\051\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\052\000\
\\009\000\037\000\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\054\000\006\000\039\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\071\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\073\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\074\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\075\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\038\000\
\\009\000\037\000\011\000\076\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\078\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\079\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\080\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\081\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\082\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\083\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\084\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\085\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\086\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\087\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\088\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\089\000\006\000\039\000\000\000\
\\001\000\094\000\002\000\093\000\003\000\092\000\004\000\091\000\
\\005\000\090\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\096\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\097\000\006\000\039\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\052\000\
\\009\000\037\000\000\000\
\\001\000\041\000\002\000\101\000\006\000\039\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\094\000\002\000\093\000\005\000\109\000\006\000\039\000\000\000\
\\000\000\
\\001\000\041\000\002\000\110\000\006\000\039\000\000\000\
\\001\000\041\000\002\000\111\000\006\000\039\000\000\000\
\\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\112\000\
\\009\000\037\000\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\113\000\
\\009\000\037\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\041\000\002\000\040\000\006\000\039\000\008\000\116\000\
\\009\000\037\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 118
val numrules = 77
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = LexArg.pos
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID' | ntVOID of unit | INTEGER_CONSTANT of  (int)
 | IDENT of  (string) | emp of  (Absyn.stmt)
 | formal of  (Absyn.varDec) | formals_list of  (Absyn.varDec seq)
 | function_parameters of  (Absyn.varDec list)
 | toplevel_declaration of  (Absyn.topDec)
 | toplevel_declaration_list of  (Absyn.topDec seq)
 | program of  (Absyn.program) | declarator of  (Absyn.declarator)
 | base_type of  (Absyn.baseTy)
 | declaration_list of  (Absyn.varDec seq)
 | declaration_list_opt of  (Absyn.varDec list)
 | declaration of  (Absyn.varDec) | statement_list of  (Absyn.stmt)
 | compound_statement of  ( ( Absyn.varDec list * Absyn.stmt ) )
 | simple_compound_statement of  (Absyn.stmt)
 | statement of  (Absyn.stmt) | binary_operator of  (Absyn.binop)
 | unary_operator of  (Absyn.unop)
 | assignment_expression of  (Absyn.exp)
 | argument_expression_list of  (Absyn.exp seq)
 | argument_expression_list_opt of  (Absyn.exp list)
 | expression of  (Absyn.exp) | identifier of  (Absyn.ident)
end
type svalue = MlyValue.svalue
type result = Absyn.program
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 1) => true | (T 4) => true | (T 11) => true | (T 12) => true | 
(T 26) => true | (T 29) => true | (T 30) => true | _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 5) => true | _ => false
val showTerminal =
fn (T 0) => "ANDAND"
  | (T 1) => "CHAR"
  | (T 2) => "COMMA"
  | (T 3) => "DIV"
  | (T 4) => "ELSE"
  | (T 5) => "EOF"
  | (T 6) => "EQ"
  | (T 7) => "EQEQ"
  | (T 8) => "GTEQ"
  | (T 9) => "GT"
  | (T 10) => "IDENT"
  | (T 11) => "IF"
  | (T 12) => "INT"
  | (T 13) => "INTEGER_CONSTANT"
  | (T 14) => "LBRACE"
  | (T 15) => "LBRACK"
  | (T 16) => "LPAREN"
  | (T 17) => "LT"
  | (T 18) => "LTEQ"
  | (T 19) => "MINUS"
  | (T 20) => "MUL"
  | (T 21) => "NOT"
  | (T 22) => "NOTEQ"
  | (T 23) => "PLUS"
  | (T 24) => "RBRACE"
  | (T 25) => "RBRACK"
  | (T 26) => "RETURN"
  | (T 27) => "RPAREN"
  | (T 28) => "SEMI"
  | (T 29) => "VOID"
  | (T 30) => "WHILE"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID'
end
val terms : term list = nil
 $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24)
 $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17)
 $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 12) $$ (T 11) $$ (T 9) $$ (T 8)
 $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 1) $$ (T 
0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    ():arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.IDENT IDENT, (IDENTleft as IDENT1left), (
IDENTright as IDENT1right))) :: rest671)) => let val  result = 
MlyValue.identifier (Absyn.IDENT(IDENT, IDENTleft, IDENTright))
 in ( LrTable.NT 0, ( result, IDENT1left, IDENT1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.identifier identifier, (identifierleft as 
identifier1left), (identifierright as identifier1right))) :: rest671))
 => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.VAR(identifier),identifierleft,identifierright))
 in ( LrTable.NT 1, ( result, identifier1left, identifier1right), 
rest671)
end
|  ( 2, ( ( _, ( MlyValue.INTEGER_CONSTANT INTEGER_CONSTANT, (
INTEGER_CONSTANTleft as INTEGER_CONSTANT1left), (INTEGER_CONSTANTright
 as INTEGER_CONSTANT1right))) :: rest671)) => let val  result = 
MlyValue.expression (
Absyn.EXP(Absyn.CONST(Absyn.INTcon(INTEGER_CONSTANT)),INTEGER_CONSTANTleft,INTEGER_CONSTANTright)
)
 in ( LrTable.NT 1, ( result, INTEGER_CONSTANT1left, 
INTEGER_CONSTANT1right), rest671)
end
|  ( 3, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.expression 
expression, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let
 val  result = MlyValue.expression (expression)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 4, ( ( _, ( _, _, (RBRACKright as RBRACK1right))) :: ( _, ( 
MlyValue.expression expression, _, _)) :: _ :: ( _, ( 
MlyValue.identifier identifier, (identifierleft as identifier1left), _
)) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.ARRAY(identifier,expression),identifierleft,RBRACKright)
)
 in ( LrTable.NT 1, ( result, identifier1left, RBRACK1right), rest671)

end
|  ( 5, ( ( _, ( _, _, (RPARENright as RPAREN1right))) :: ( _, ( 
MlyValue.argument_expression_list_opt argument_expression_list_opt, _,
 _)) :: _ :: ( _, ( MlyValue.identifier identifier, (identifierleft
 as identifier1left), _)) :: rest671)) => let val  result = 
MlyValue.expression (
Absyn.EXP(Absyn.FCALL(identifier,argument_expression_list_opt),identifierleft,RPARENright)
)
 in ( LrTable.NT 1, ( result, identifier1left, RPAREN1right), rest671)

end
|  ( 6, ( ( _, ( MlyValue.expression expression, _, (expressionright
 as expression1right))) :: ( _, ( MlyValue.unary_operator 
unary_operator, (unary_operatorleft as unary_operator1left), _)) :: 
rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.UNARY(unary_operator,expression),unary_operatorleft,expressionright)
)
 in ( LrTable.NT 1, ( result, unary_operator1left, expression1right), 
rest671)
end
|  ( 7, ( ( _, ( MlyValue.expression expression2, _, expression2right)
) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _))
 :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.ANDALSO,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 8, ( ( _, ( MlyValue.expression expression2, _, expression2right)
) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _))
 :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.EQ,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 9, ( ( _, ( MlyValue.expression expression2, _, expression2right)
) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _))
 :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.NE,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 10, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.LT,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 11, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.GT,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 12, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.LE,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 13, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.GE,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 14, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.SUB,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 15, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.ADD,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 16, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.DIV,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 17, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.BINARY(Absyn.MUL,expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 18, ( ( _, ( MlyValue.expression expression1, _, expression1right
)) :: ( _, ( _, (NOTleft as NOT1left), _)) :: rest671)) => let val  
result = MlyValue.expression (
Absyn.EXP(Absyn.UNARY(Absyn.NOT,expression1),NOTleft,expression1right)
)
 in ( LrTable.NT 1, ( result, NOT1left, expression1right), rest671)

end
|  ( 19, ( ( _, ( MlyValue.expression expression1, _, expression1right
)) :: ( _, ( _, (MINUSleft as MINUS1left), _)) :: rest671)) => let
 val  result = MlyValue.expression (
Absyn.EXP(Absyn.UNARY(Absyn.NEG,expression1),MINUSleft,expression1right)
)
 in ( LrTable.NT 1, ( result, MINUS1left, expression1right), rest671)

end
|  ( 20, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.expression (
Absyn.EXP(Absyn.ASSIGN(expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 1, ( result, expression1left, expression2right), 
rest671)
end
|  ( 21, ( ( _, ( _, MINUS1left, MINUS1right)) :: rest671)) => let
 val  result = MlyValue.unary_operator (Absyn.NEG)
 in ( LrTable.NT 5, ( result, MINUS1left, MINUS1right), rest671)
end
|  ( 22, ( ( _, ( _, NOT1left, NOT1right)) :: rest671)) => let val  
result = MlyValue.unary_operator (Absyn.NOT)
 in ( LrTable.NT 5, ( result, NOT1left, NOT1right), rest671)
end
|  ( 23, ( ( _, ( _, MUL1left, MUL1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.MUL)
 in ( LrTable.NT 6, ( result, MUL1left, MUL1right), rest671)
end
|  ( 24, ( ( _, ( _, DIV1left, DIV1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.DIV)
 in ( LrTable.NT 6, ( result, DIV1left, DIV1right), rest671)
end
|  ( 25, ( ( _, ( _, PLUS1left, PLUS1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.ADD)
 in ( LrTable.NT 6, ( result, PLUS1left, PLUS1right), rest671)
end
|  ( 26, ( ( _, ( _, MINUS1left, MINUS1right)) :: rest671)) => let
 val  result = MlyValue.binary_operator (Absyn.SUB)
 in ( LrTable.NT 6, ( result, MINUS1left, MINUS1right), rest671)
end
|  ( 27, ( ( _, ( _, LT1left, LT1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.LT)
 in ( LrTable.NT 6, ( result, LT1left, LT1right), rest671)
end
|  ( 28, ( ( _, ( _, GT1left, GT1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.GT)
 in ( LrTable.NT 6, ( result, GT1left, GT1right), rest671)
end
|  ( 29, ( ( _, ( _, LTEQ1left, LTEQ1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.LE)
 in ( LrTable.NT 6, ( result, LTEQ1left, LTEQ1right), rest671)
end
|  ( 30, ( ( _, ( _, GTEQ1left, GTEQ1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.GE)
 in ( LrTable.NT 6, ( result, GTEQ1left, GTEQ1right), rest671)
end
|  ( 31, ( ( _, ( _, EQEQ1left, EQEQ1right)) :: rest671)) => let val  
result = MlyValue.binary_operator (Absyn.EQ)
 in ( LrTable.NT 6, ( result, EQEQ1left, EQEQ1right), rest671)
end
|  ( 32, ( ( _, ( _, NOTEQ1left, NOTEQ1right)) :: rest671)) => let
 val  result = MlyValue.binary_operator (Absyn.NE)
 in ( LrTable.NT 6, ( result, NOTEQ1left, NOTEQ1right), rest671)
end
|  ( 33, ( ( _, ( _, ANDAND1left, ANDAND1right)) :: rest671)) => let
 val  result = MlyValue.binary_operator (Absyn.ANDALSO)
 in ( LrTable.NT 6, ( result, ANDAND1left, ANDAND1right), rest671)
end
|  ( 34, ( rest671)) => let val  result = 
MlyValue.argument_expression_list_opt ([])
 in ( LrTable.NT 2, ( result, defaultPos, defaultPos), rest671)
end
|  ( 35, ( ( _, ( MlyValue.argument_expression_list 
argument_expression_list, argument_expression_list1left, 
argument_expression_list1right)) :: rest671)) => let val  result = 
MlyValue.argument_expression_list_opt (
seqToList(argument_expression_list))
 in ( LrTable.NT 2, ( result, argument_expression_list1left, 
argument_expression_list1right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.assignment_expression assignment_expression
, assignment_expression1left, assignment_expression1right)) :: rest671
)) => let val  result = MlyValue.argument_expression_list (
SINGLE(assignment_expression))
 in ( LrTable.NT 3, ( result, assignment_expression1left, 
assignment_expression1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.assignment_expression assignment_expression
, _, assignment_expression1right)) :: _ :: ( _, ( 
MlyValue.argument_expression_list argument_expression_list, 
argument_expression_list1left, _)) :: rest671)) => let val  result = 
MlyValue.argument_expression_list (
SEQ(argument_expression_list, assignment_expression))
 in ( LrTable.NT 3, ( result, argument_expression_list1left, 
assignment_expression1right), rest671)
end
|  ( 38, ( ( _, ( MlyValue.INTEGER_CONSTANT INTEGER_CONSTANT, (
INTEGER_CONSTANTleft as INTEGER_CONSTANT1left), (INTEGER_CONSTANTright
 as INTEGER_CONSTANT1right))) :: rest671)) => let val  result = 
MlyValue.assignment_expression (
Absyn.EXP(Absyn.CONST(Absyn.INTcon(INTEGER_CONSTANT)),INTEGER_CONSTANTleft,INTEGER_CONSTANTright)
)
 in ( LrTable.NT 4, ( result, INTEGER_CONSTANT1left, 
INTEGER_CONSTANT1right), rest671)
end
|  ( 39, ( ( _, ( MlyValue.identifier identifier, (identifierleft as 
identifier1left), (identifierright as identifier1right))) :: rest671))
 => let val  result = MlyValue.assignment_expression (
Absyn.EXP(Absyn.VAR(identifier),identifierleft,identifierright))
 in ( LrTable.NT 4, ( result, identifier1left, identifier1right), 
rest671)
end
|  ( 40, ( ( _, ( MlyValue.expression expression2, _, expression2right
)) :: _ :: ( _, ( MlyValue.expression expression1, expression1left, _)
) :: rest671)) => let val  result = MlyValue.assignment_expression (
Absyn.EXP(Absyn.ASSIGN(expression1,expression2),expression1left,expression2right)
)
 in ( LrTable.NT 4, ( result, expression1left, expression2right), 
rest671)
end
|  ( 41, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( MlyValue.expression 
expression, _, expressionright)) :: _ :: ( _, ( MlyValue.identifier 
identifier, (identifierleft as identifier1left), _)) :: rest671)) =>
 let val  result = MlyValue.assignment_expression (
Absyn.EXP(Absyn.ARRAY(identifier,expression),identifierleft,expressionright)
)
 in ( LrTable.NT 4, ( result, identifier1left, RBRACK1right), rest671)

end
|  ( 42, ( ( _, ( MlyValue.expression expression, expression1left, 
expression1right)) :: rest671)) => let val  result = 
MlyValue.assignment_expression (expression)
 in ( LrTable.NT 4, ( result, expression1left, expression1right), 
rest671)
end
|  ( 43, ( ( _, ( MlyValue.simple_compound_statement 
simple_compound_statement, simple_compound_statement1left, 
simple_compound_statement1right)) :: rest671)) => let val  result = 
MlyValue.statement (simple_compound_statement)
 in ( LrTable.NT 7, ( result, simple_compound_statement1left, 
simple_compound_statement1right), rest671)
end
|  ( 44, ( ( _, ( _, _, (SEMIright as SEMI1right))) :: ( _, ( 
MlyValue.expression expression, (expressionleft as expression1left), _
)) :: rest671)) => let val  result = MlyValue.statement (
Absyn.STMT(Absyn.EFFECT(expression),expressionleft,SEMIright))
 in ( LrTable.NT 7, ( result, expression1left, SEMI1right), rest671)

end
|  ( 45, ( ( _, ( _, (SEMIleft as SEMI1left), (SEMIright as SEMI1right
))) :: rest671)) => let val  result = MlyValue.statement (
Absyn.STMT(Absyn.EMPTY,SEMIleft,SEMIright))
 in ( LrTable.NT 7, ( result, SEMI1left, SEMI1right), rest671)
end
|  ( 46, ( ( _, ( MlyValue.statement statement, statementleft, 
statement1right)) :: _ :: ( _, ( MlyValue.expression expression, _, _)
) :: _ :: ( _, ( _, IF1left, IFright)) :: rest671)) => let val  result
 = MlyValue.statement (
Absyn.STMT(Absyn.IF(expression,statement,NONE),IFright,statementleft))
 in ( LrTable.NT 7, ( result, IF1left, statement1right), rest671)
end
|  ( 47, ( ( _, ( MlyValue.statement statement2, statement2left, 
statement2right)) :: _ :: ( _, ( MlyValue.statement statement1, _, _))
 :: _ :: ( _, ( MlyValue.expression expression, _, _)) :: _ :: ( _, (
 _, IF1left, IFright)) :: rest671)) => let val  result = 
MlyValue.statement (
Absyn.STMT(Absyn.IF(expression,statement1,SOME statement2),IFright,statement2left)
)
 in ( LrTable.NT 7, ( result, IF1left, statement2right), rest671)
end
|  ( 48, ( ( _, ( MlyValue.statement statement, _, (statementright as 
statement1right))) :: _ :: ( _, ( MlyValue.expression expression, _, _
)) :: _ :: ( _, ( _, (WHILEleft as WHILE1left), _)) :: rest671)) =>
 let val  result = MlyValue.statement (
Absyn.STMT(Absyn.WHILE(expression,statement),WHILEleft,statementright)
)
 in ( LrTable.NT 7, ( result, WHILE1left, statement1right), rest671)

end
|  ( 49, ( ( _, ( _, _, (SEMIright as SEMI1right))) :: ( _, ( 
MlyValue.expression expression, _, _)) :: ( _, ( _, (RETURNleft as 
RETURN1left), _)) :: rest671)) => let val  result = MlyValue.statement
 (Absyn.STMT(Absyn.RETURN(SOME expression),RETURNleft, SEMIright))
 in ( LrTable.NT 7, ( result, RETURN1left, SEMI1right), rest671)
end
|  ( 50, ( ( _, ( _, _, (SEMIright as SEMI1right))) :: ( _, ( _, (
RETURNleft as RETURN1left), _)) :: rest671)) => let val  result = 
MlyValue.statement (
Absyn.STMT(Absyn.RETURN(NONE),RETURNleft, SEMIright))
 in ( LrTable.NT 7, ( result, RETURN1left, SEMI1right), rest671)
end
|  ( 51, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( 
MlyValue.statement_list statement_list, _, _)) :: ( _, ( _, 
LBRACE1left, _)) :: rest671)) => let val  result = 
MlyValue.simple_compound_statement (statement_list)
 in ( LrTable.NT 8, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 52, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( 
MlyValue.statement_list statement_list, _, _)) :: ( _, ( 
MlyValue.declaration_list_opt declaration_list_opt, _, _)) :: ( _, ( _
, LBRACE1left, _)) :: rest671)) => let val  result = 
MlyValue.compound_statement ((declaration_list_opt,statement_list))
 in ( LrTable.NT 9, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.statement statement, statement1left, 
statement1right)) :: rest671)) => let val  result = 
MlyValue.statement_list (statement)
 in ( LrTable.NT 10, ( result, statement1left, statement1right), 
rest671)
end
|  ( 54, ( ( _, ( MlyValue.statement statement, _, (statementright as 
statement1right))) :: ( _, ( MlyValue.statement_list statement_list, (
statement_listleft as statement_list1left), _)) :: rest671)) => let
 val  result = MlyValue.statement_list (
Absyn.STMT(Absyn.SEQ(statement_list, statement),statement_listleft,statementright)
)
 in ( LrTable.NT 10, ( result, statement_list1left, statement1right), 
rest671)
end
|  ( 55, ( ( _, ( _, _, SEMI1right)) :: ( _, ( MlyValue.declarator 
declarator, _, _)) :: ( _, ( MlyValue.base_type base_type, 
base_type1left, _)) :: rest671)) => let val  result = 
MlyValue.declaration (Absyn.VARDEC(base_type, declarator))
 in ( LrTable.NT 11, ( result, base_type1left, SEMI1right), rest671)

end
|  ( 56, ( rest671)) => let val  result = 
MlyValue.declaration_list_opt ([])
 in ( LrTable.NT 12, ( result, defaultPos, defaultPos), rest671)
end
|  ( 57, ( ( _, ( MlyValue.declaration_list declaration_list, 
declaration_list1left, declaration_list1right)) :: rest671)) => let
 val  result = MlyValue.declaration_list_opt (
seqToList(declaration_list))
 in ( LrTable.NT 12, ( result, declaration_list1left, 
declaration_list1right), rest671)
end
|  ( 58, ( ( _, ( MlyValue.declaration declaration, declaration1left, 
declaration1right)) :: rest671)) => let val  result = 
MlyValue.declaration_list (SINGLE(declaration))
 in ( LrTable.NT 13, ( result, declaration1left, declaration1right), 
rest671)
end
|  ( 59, ( ( _, ( MlyValue.declaration declaration, _, 
declaration1right)) :: ( _, ( MlyValue.declaration_list 
declaration_list, declaration_list1left, _)) :: rest671)) => let val  
result = MlyValue.declaration_list (SEQ(declaration_list, declaration)
)
 in ( LrTable.NT 13, ( result, declaration_list1left, 
declaration1right), rest671)
end
|  ( 60, ( ( _, ( _, CHAR1left, CHAR1right)) :: rest671)) => let val  
result = MlyValue.base_type (Absyn.CHARty)
 in ( LrTable.NT 14, ( result, CHAR1left, CHAR1right), rest671)
end
|  ( 61, ( ( _, ( _, INT1left, INT1right)) :: rest671)) => let val  
result = MlyValue.base_type (Absyn.INTty)
 in ( LrTable.NT 14, ( result, INT1left, INT1right), rest671)
end
|  ( 62, ( ( _, ( _, VOID1left, VOID1right)) :: rest671)) => let val  
result = MlyValue.base_type (Absyn.VOIDty)
 in ( LrTable.NT 14, ( result, VOID1left, VOID1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.identifier identifier, identifier1left, 
identifier1right)) :: rest671)) => let val  result = 
MlyValue.declarator (Absyn.VARdecl(identifier))
 in ( LrTable.NT 15, ( result, identifier1left, identifier1right), 
rest671)
end
|  ( 64, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( 
MlyValue.INTEGER_CONSTANT INTEGER_CONSTANT, _, _)) :: _ :: ( _, ( 
MlyValue.identifier identifier, identifier1left, _)) :: rest671)) =>
 let val  result = MlyValue.declarator (
Absyn.ARRdecl(identifier, SOME INTEGER_CONSTANT))
 in ( LrTable.NT 15, ( result, identifier1left, RBRACK1right), rest671
)
end
|  ( 65, ( ( _, ( _, _, RBRACK1right)) :: _ :: ( _, ( 
MlyValue.identifier identifier, identifier1left, _)) :: rest671)) =>
 let val  result = MlyValue.declarator (
Absyn.ARRdecl(identifier, NONE))
 in ( LrTable.NT 15, ( result, identifier1left, RBRACK1right), rest671
)
end
|  ( 66, ( ( _, ( MlyValue.toplevel_declaration_list 
toplevel_declaration_list, toplevel_declaration_list1left, 
toplevel_declaration_list1right)) :: rest671)) => let val  result = 
MlyValue.program (
Absyn.PROGRAM{decs = seqToList(toplevel_declaration_list),
			       source = Absyn.Source.dummy}
)
 in ( LrTable.NT 16, ( result, toplevel_declaration_list1left, 
toplevel_declaration_list1right), rest671)
end
|  ( 67, ( ( _, ( MlyValue.toplevel_declaration toplevel_declaration, 
toplevel_declaration1left, toplevel_declaration1right)) :: rest671))
 => let val  result = MlyValue.toplevel_declaration_list (
SINGLE(toplevel_declaration))
 in ( LrTable.NT 17, ( result, toplevel_declaration1left, 
toplevel_declaration1right), rest671)
end
|  ( 68, ( ( _, ( MlyValue.toplevel_declaration toplevel_declaration,
 _, toplevel_declaration1right)) :: ( _, ( 
MlyValue.toplevel_declaration_list toplevel_declaration_list, 
toplevel_declaration_list1left, _)) :: rest671)) => let val  result = 
MlyValue.toplevel_declaration_list (
SEQ(toplevel_declaration_list, toplevel_declaration))
 in ( LrTable.NT 17, ( result, toplevel_declaration_list1left, 
toplevel_declaration1right), rest671)
end
|  ( 69, ( ( _, ( MlyValue.compound_statement compound_statement, _, 
compound_statement1right)) :: ( _, ( MlyValue.function_parameters 
function_parameters, _, _)) :: ( _, ( MlyValue.identifier identifier,
 _, _)) :: ( _, ( MlyValue.base_type base_type, base_type1left, _)) ::
 rest671)) => let val  result = MlyValue.toplevel_declaration (
Absyn.FUNC{name=identifier,formals=function_parameters,
			    retTy=base_type,
			    locals= (#1) compound_statement,
			    body= (#2) compound_statement}
)
 in ( LrTable.NT 18, ( result, base_type1left, 
compound_statement1right), rest671)
end
|  ( 70, ( ( _, ( _, _, SEMI1right)) :: ( _, ( 
MlyValue.function_parameters function_parameters, _, _)) :: ( _, ( 
MlyValue.identifier identifier, _, _)) :: ( _, ( MlyValue.base_type 
base_type, base_type1left, _)) :: rest671)) => let val  result = 
MlyValue.toplevel_declaration (
Absyn.EXTERN{name=identifier,
			      retTy=base_type,
			      formals=function_parameters}
)
 in ( LrTable.NT 18, ( result, base_type1left, SEMI1right), rest671)

end
|  ( 71, ( ( _, ( MlyValue.declaration declaration, declaration1left, 
declaration1right)) :: rest671)) => let val  result = 
MlyValue.toplevel_declaration (Absyn.GLOBAL(declaration))
 in ( LrTable.NT 18, ( result, declaration1left, declaration1right), 
rest671)
end
|  ( 72, ( ( _, ( _, _, RPAREN1right)) :: _ :: ( _, ( _, LPAREN1left,
 _)) :: rest671)) => let val  result = MlyValue.function_parameters (
[])
 in ( LrTable.NT 19, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 73, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.formals_list
 formals_list, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) =>
 let val  result = MlyValue.function_parameters (
seqToList(formals_list))
 in ( LrTable.NT 19, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 74, ( ( _, ( MlyValue.formal formal, formal1left, formal1right))
 :: rest671)) => let val  result = MlyValue.formals_list (
SINGLE(formal))
 in ( LrTable.NT 20, ( result, formal1left, formal1right), rest671)

end
|  ( 75, ( ( _, ( MlyValue.formal formal, _, formal1right)) :: _ :: (
 _, ( MlyValue.formals_list formals_list, formals_list1left, _)) :: 
rest671)) => let val  result = MlyValue.formals_list (
SEQ(formals_list, formal))
 in ( LrTable.NT 20, ( result, formals_list1left, formal1right), 
rest671)
end
|  ( 76, ( ( _, ( MlyValue.declarator declarator, _, declarator1right)
) :: ( _, ( MlyValue.base_type base_type, base_type1left, _)) :: 
rest671)) => let val  result = MlyValue.formal (
Absyn.VARDEC(base_type, declarator))
 in ( LrTable.NT 21, ( result, base_type1left, declarator1right), 
rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID'
val extract = fn a => (fn MlyValue.program x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : UC_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun ANDAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID',p1,p2))
fun CHAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID',p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID',p1,p2))
fun DIV (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID',p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID',p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID',p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID',p1,p2))
fun EQEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID',p1,p2))
fun GTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID',p1,p2))
fun GT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID',p1,p2))
fun IDENT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.IDENT i,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID',p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID',p1,p2))
fun INTEGER_CONSTANT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 13
,(ParserData.MlyValue.INTEGER_CONSTANT i,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID',p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID',p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID',p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID',p1,p2))
fun LTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID',p1,p2))
fun MUL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID',p1,p2))
fun NOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID',p1,p2))
fun NOTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID',p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID',p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID',p1,p2))
fun RETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID',p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID',p1,p2))
fun SEMI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID',p1,p2))
fun VOID (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID',p1,p2))
fun WHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID',p1,p2))
end
end
