%{
  open Errors
%}


/* Tokens declarations */
%token EOF
%token Plus Eq Lt Leq Gt Geq Minus Star Div
%token Fun Assign If Else While Do For
%token <int> Number
%token <char> Character
%token <string> String
%token <string> Ident
%token Comma Semicolon Colon LParen RParen LBrace RBrace LBracket RBracket Bang
%token Arrow Bigarrow
%token Skip Return Let
%token Public Private Static Extern
%token Const Volatile Restrict
%token <string> InlineC

/* Precedence and associativity specification */
%left Plus Minus
%left Lt Leq Gt Geq
%left Eq
%left Arrow

/* Starting symbol */
%start program
%type <Ast.command> program
%type <Ast.command> command
%type <Ast.perkdef> perkdef
%type <Ast.perkvardesc> perkvardesc
%type <Ast.perkfun> perkfun
%type <Ast.perktype_complete> perktype_complete
%type <Ast.perktype> perktype
%type <Ast.perktype> perkfuntype
%type <Ast.binop> binop
%type <Ast.unop> unop
%type <Ast.expr> expr
%type <Ast.perkident list> ident_list
%type <Ast.perktype_complete list> perktype_list

// %on_error_reduce command

%%

/* Grammar specification */

program:
  | c = command EOF { c }

command:
  | ic = InlineC                                                                                           { Ast.InlineC(ic) }
  | d = perkdef                                                                                            { Ast.Def d }
  | Fun pf = perkfun                                                                                       { Ast.Fundef pf }
  | i = Ident Assign e = expr                                                                              { Ast.Assign (i, e) }
  | If LParen e = expr RParen LBrace c1 = command RBrace Else LBrace c2 = command RBrace                   { Ast.IfThenElse (e, c1, c2) }
  | If LParen e = expr RParen LBrace c1 = command RBrace                                                   { Ast.IfThenElse (e, c1, Ast.Skip) }
  | While LParen e = expr RParen LBrace c = command RBrace                                                 { Ast.Whiledo (e, c) }
  | Do LBrace c = command RBrace While LParen e = expr RParen                                              { Ast.Dowhile (e, c) }
  | For LParen c1 = command Semicolon e2 = expr Semicolon c3 = command RParen LBrace body = command RBrace       { Ast.For (c1, e2, c3, body) }
  | LBrace c = command RBrace                                                                              { Ast.Block(c) }
  | e = expr                                                                                               { Ast.Expr(e) }
  | c1 = command Semicolon c2 = command                                                                    { Ast.Seq (c1, c2) }
  | c1 = command Semicolon                                                                                 { c1 }
  | Skip                                                                                                   { Ast.Skip }
  | Return e = expr                                                                                        { Ast.Return (e) }
  | error                                                                                                  { raise (ParseError("command expected")) }
  | command error                                                                                          { raise (ParseError("unexpected command (perhaps you are missing a ';'?)")) }


perkdef:
  | Let vd = perkvardesc Assign e = expr                                                                   { (vd, e) }
  | error { raise (ParseError("definition expected (e.g. let banana : int = 5)")) }

perkfun:
  | i = Ident LParen id_list = perkvardesc_list RParen Colon rt = perktype_complete LBrace c = command RBrace       { Ast.Fun (rt, i, id_list, c) }
  | i = Ident LParen RParen Colon rt = perktype_complete LBrace c = command RBrace                                  { Ast.Fun (rt, i, [], c) }
  

perkvardesc:
  | i = Ident Colon t = perktype_complete                                                                  { (t, i) }
  | error { raise (ParseError("variable descriptor expected (e.g. banana : int)")) }
  
%inline perkfuntype:
  | t1 = perktype_complete Arrow t2 = perktype_complete                                                    { Ast.Funtype ([t1], t2) }
  | LParen tl = perktype_list RParen Arrow tf = perktype_complete                                          { Ast.Funtype (tl, tf) }

expr:
  | Star e = expr                                                                                          { Ast.Pointer e }
  | e1 = expr LParen args = separated_list(Comma, expr) RParen                                             { Ast.Apply (e1, args) }
  | e1 = expr b = binop e2 = expr                                                                          { Ast.Binop (b, e1, e2) }
  | u = unop e = expr Comma                                                                                { Ast.Unop (u, e) }
  | LParen id_list = perkvardesc_list RParen Colon ret = perktype_complete Bigarrow LBrace c = command RBrace       { Ast.Lambda (ret, id_list, c) }
  | LParen RParen Colon ret = perktype_complete Bigarrow LBrace c = command RBrace                                  { Ast.Lambda (ret, [], c) }
  | n = Number                                                                                             { Ast.Int (n) }
  | c = Character                                                                                          { Ast.Char (c) }
  | s = String                                                                                             { Ast.String (s) }
  | i = Ident                                                                                              { Ast.Var(i) }
  | LParen e = expr RParen                                                                                 { e }
  | error { raise (ParseError("expression expected")) }
  | expr error                                                                                         { raise (ParseError("unexpected expression")) }
  | Ident error                                                                                     { raise (ParseError("unexpected expression. Perhaps you tried to use C-style types?")) }

%inline perktype_attribute:
  | Public                                                                                                 { Ast.Public }
  | Private                                                                                                { Ast.Private }
  | Static                                                                                                 { Ast.Static }
  | Extern                                                                                                 { Ast.Extern }

%inline perktype_qualifier:
  | Const                                                                                                  { Ast.Const }
  | Volatile                                                                                               { Ast.Volatile }
  | Restrict                                                                                               { Ast.Restrict }

perktype_complete:
  | t = perktype q = list(perktype_qualifier)                                                              { ([], t, q) }
  | t = perkfuntype q = list(perktype_qualifier)                                                           { ([], t, q) }
  | LParen t = perktype_complete RParen                                                                    { t }
  | error                                                                                                  { raise (ParseError("type expected")) }

perktype:
  | i = Ident                                                                                              { Ast.Basetype i }
  | LBracket t = perktype_complete RBracket                                                                { Ast.Arraytype (t, None) }
  | LBracket t = perktype_complete n = Number RBracket                                                     { Ast.Arraytype (t, Some n) }
  | t = perktype_complete Star                                                                             { Ast.Pointertype t }
  | error                                                                                                  { raise (ParseError("type expected")) }

%inline binop:
  | Plus                                                                                                   { Ast.Add }
  | Minus                                                                                                  { Ast.Sub }
  | Star                                                                                                   { Ast.Mul }
  | Div                                                                                                    { Ast.Div }
  | Eq                                                                                                     { Ast.Eq }
  | Lt                                                                                                     { Ast.Lt }
  | Leq                                                                                                    { Ast.Leq }
  | Gt                                                                                                     { Ast.Gt }
  | Geq                                                                                                    { Ast.Geq }

%inline unop:
  | Minus                                                                                                  { Ast.Neg }
  | Bang                                                                                                   { Ast.Not }


/* New nonterminals for disambiguated lists */

ident_list:
  | i = Ident { [i] }
  | il = ident_list Comma i = Ident { il @ [i] }
  | error { raise (ParseError("identifier expected")) }

perktype_list:
  | t = perktype_complete { [t] }
  | tl = perktype_complete Star t = perktype_list { tl :: t }
  | error { raise (ParseError("type expected")) }

perkvardesc_list:
  | t = perkvardesc { [t] }
  | tl = perkvardesc_list Comma t = perkvardesc { tl @ [t] }
  | error { raise (ParseError("variable descriptor expected")) }

spanish_inquisition:
  | error { raise (ParseError("Nobody expects the Spanish Inquisition!")) }
%%