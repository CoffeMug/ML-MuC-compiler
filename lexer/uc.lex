(* lexer/uc.lex *)

(* parameters for ML-Yacc -- don't change *)
type arg = LexArg.lexarg
type pos = LexArg.pos
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

(* stack to keep track of block comments *)

val commentCount = ref 0

fun eof (lexarg) =
  let val pos = LexArg.readPos lexarg
  in
    if(!commentCount) = 0 then () else 
    let val msg = "Unclosed comment!" 
    in 
        LexArg.error2 lexarg (msg,pos,pos)

    end;
        Tokens.EOF(pos, pos)
end

(* HELPER FUNCTIONS HERE *)

fun inc(i) = i := !(i) + 1
fun dec(i) = i := !(i) - 1

%%

%header (functor UCLexFn(structure Tokens : UC_TOKENS
             structure LexArg : LEXARG) : ARG_LEXER);
 
%arg (lexarg);
%full
%s LINECOMMENT COMMENT;

alpha = [_A-Za-z];
digit = [0-9];
ch = [\']({alpha}|{digit}|[ ]|[?]|[:]|[;]|[,]|[<]|[=]|[>]|[@]|[!]|[#]|[$]|[%]|[(]|[)]|[+]|[-]|[.]|[/]|[*]|[&]|[[]|[]]|[{]|[}])[\'];
backslashn = [\'](/\\n/)[\'];
int = {digit}+;
alphdig = [_0-9a-zA-Z];
ident = {alpha}{alphdig}*;
ws = [\ \t];

%%

<INITIAL>"!=" => (Tokens.NOTEQ(yypos, yypos+1));
<INITIAL>"&&" => (Tokens.ANDAND(yypos, yypos+1));
<INITIAL>"<=" => (Tokens.LTEQ(yypos, yypos+1));
<INITIAL>"==" => (Tokens.EQEQ(yypos, yypos+1));
<INITIAL>">=" => (Tokens.GTEQ(yypos, yypos+1));

<INITIAL>"!" => (Tokens.NOT(yypos, yypos));
<INITIAL>"(" => (Tokens.LPAREN(yypos, yypos));
<INITIAL>")" => (Tokens.RPAREN(yypos, yypos));
<INITIAL>"*" => (Tokens.MUL(yypos, yypos));
<INITIAL>"+" => (Tokens.PLUS(yypos, yypos));
<INITIAL>"-" => (Tokens.MINUS(yypos, yypos));
<INITIAL>"," => (Tokens.COMMA(yypos, yypos));
<INITIAL>"/" => (Tokens.DIV(yypos, yypos));
<INITIAL>";" => (Tokens.SEMI(yypos, yypos));
<INITIAL>"<" => (Tokens.LT(yypos, yypos));
<INITIAL>"=" => (Tokens.EQ(yypos, yypos));
<INITIAL>">" => (Tokens.GT(yypos, yypos));
<INITIAL>"[" => (Tokens.LBRACK(yypos, yypos));
<INITIAL>"]" => (Tokens.RBRACK(yypos, yypos));
<INITIAL>"{" => (Tokens.LBRACE(yypos, yypos));
<INITIAL>"}" => (Tokens.RBRACE(yypos, yypos));
<INITIAL>"char" => (Tokens.CHAR(yypos, yypos+3));
<INITIAL>"else" => (Tokens.ELSE(yypos, yypos+3));
<INITIAL>"if"   => (Tokens.IF(yypos, yypos+1));
<INITIAL>"int"  => (Tokens.INT(yypos, yypos+2));
<INITIAL>"return" => (Tokens.RETURN(yypos, yypos+5));
<INITIAL>"void"   => (Tokens.VOID(yypos, yypos+3));
<INITIAL>"while"  => (Tokens.WHILE(yypos, yypos+4));


<INITIAL>"/*"     => (YYBEGIN COMMENT; inc (commentCount) ; continue());
<COMMENT>"*/"     => (YYBEGIN INITIAL; dec (commentCount); continue());
<INITIAL>"//"     => (YYBEGIN LINECOMMENT; continue());
<COMMENT,LINECOMMENT>.  => (continue());
<LINECOMMENT>"\n"       => (YYBEGIN INITIAL; LexArg.newLine(lexarg,yypos);LexArg.source(lexarg); continue());
<INITIAL,COMMENT>"\n"   => (LexArg.newLine(lexarg,yypos);LexArg.source(lexarg); continue());

<INITIAL>{ws}+ => (continue());
<INITIAL>{ident} => (Tokens.IDENT (yytext,yypos,yypos+ size yytext));
<INITIAL>{int} => (Tokens.INTEGER_CONSTANT(valOf(Int.fromString (yytext)),yypos,yypos+ size yytext));

<INITIAL>{ch} => 
   (let val a = String.substring(yytext,1,1)
        val b = String.sub (a,0)
        val c = Char.ord b
    in
        Tokens.INTEGER_CONSTANT(c,yypos, 0)
    end);

<INITIAL>{backslashn} => (Tokens.INTEGER_CONSTANT(10,yypos,0));

<INITIAL>. =>
    (let val msg = "Illegal character " ^ yytext
     in
       LexArg.error2 lexarg (msg,yypos,yypos);
       continue()
     end);
