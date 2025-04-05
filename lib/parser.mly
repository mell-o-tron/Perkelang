%{
  open Errors
  open Ast
%}


/* Tokens declarations */
%token EOF
%token Plus Eq Lt Leq Gt Geq Minus Star Div Ampersand PlusPlus MinusMinus Dot Ellipsis Question
%token Fun Assign If Else While Do For
%token <int> Integer
%token <float> Float
%token <char> Character
%token <string> String
%token <string> Ident
%token Comma Semicolon Colon LParen RParen LBrace RBrace LBracket RBracket Bang
%token Arrow Bigarrow As
%token Skip Return Let
%token Public Private Static Extern
%token Const Volatile Restrict
%token <string> InlineC
%token Import Open
%token Archetype Model Summon Banish
%token Nothing Something

/* Precedence and associativity specification */
%left Semicolon
%left Comma
%nonassoc Lt Leq Gt Geq
%nonassoc Eq
%left Arrow             /* For Bigarrow in lambda expressions */
%left Plus Minus
%left Star Div As
%right PlusPlus MinusMinus Bang Ampersand
                          /* The above line is intended for prefix operators.
                             (You would use %prec with these tokens in your grammar
                             so that, for example, a pointer dereference (prefix Star)
                             binds tighter than binary Star/Div.) */
%nonassoc POSTFIX         /* Intended for postfix operators (e.g. post ++/--)
                             via %prec POSTFIX in the corresponding rules */
%left Dot


/* Starting symbol */
%start program
%type <Ast.topleveldef_a list> program
%type <Ast.topleveldef_a> topleveldef
%type <Ast.command_a> command
%type <Ast.perkdef> perkdef
%type <Ast.perkvardesc> perkvardesc
%type <Ast.topleveldef_a> perkfun
%type <Ast.perktype> perktype
%type <Ast.perktype_partial> perkfuntype
%type <Ast.binop> binop
%type <Ast.preunop> preunop
%type <Ast.postunop> postunop
%type <Ast.expr_a> expr
%type <Ast.perkident list> ident_list
%type <Ast.perktype list> perktype_list

// %on_error_reduce command

%%

/* Grammar specification */

program:
  | defs = separated_list(Semicolon, topleveldef) option(Semicolon) EOF { defs }

topleveldef:
  | Import i = String                                                                                      { annotate_2_code $loc (Ast.Import ("<" ^ i ^ ">")) }
  | Open i = String                                                                                        { annotate_2_code $loc (Ast.Import ("\"" ^ i ^ "\"")) }
  | Extern id = Ident Colon t = perktype                                                                   { annotate_2_code $loc (Ast.Extern (id, t)) }
  | ic = InlineC                                                                                           { annotate_2_code $loc (Ast.InlineC(ic)) }
  | d = perkdef                                                                                            { annotate_2_code $loc (Ast.Def d) }
  | Archetype i = Ident LBrace l = perkvardesc_list RBrace                                                 { annotate_2_code $loc (Ast.Archetype (i, l)) }
  | Model i = Ident Colon il = ident_list LBrace l = perkdef_list RBrace                                   { annotate_2_code $loc (Ast.Model (i, il, l)) }
  | Model i = Ident LBrace l = perkdef_list RBrace                                                         { annotate_2_code $loc (Ast.Model (i, [], l)) }
  | Fun pf = perkfun                                                                                       { pf }

command:
  | ic = InlineC                                                                                           { annotate_2_code $loc (Ast.InlineCCmd(ic)) }
  | d = perkdef                                                                                            { annotate_2_code $loc (Ast.DefCmd d) }
  | l = expr Assign r = expr                                                                               { annotate_2_code $loc (Ast.Assign (l, r)) }
  | If LParen e = expr RParen LBrace c1 = command RBrace Else LBrace c2 = command RBrace                   { annotate_2_code $loc (Ast.IfThenElse (e, c1, c2)) }
  | If LParen e = expr RParen LBrace c1 = command RBrace                                                   { annotate_2_code $loc (Ast.IfThenElse (e, c1, annotate_dummy Ast.Skip)) }
  | While LParen e = expr RParen LBrace c = command RBrace                                                 { annotate_2_code $loc (Ast.Whiledo (e, c)) }
  | Do LBrace c = command RBrace While LParen e = expr RParen                                              { annotate_2_code $loc (Ast.Dowhile (e, c)) }
  | For LParen c1 = command Semicolon e2 = expr Semicolon c3 = command RParen LBrace body = command RBrace { annotate_2_code $loc (Ast.For (c1, e2, c3, body)) }
  | LBrace c = command RBrace                                                                              { annotate_2_code $loc (Ast.Block(c)) }
  | e = expr                                                                                               { annotate_2_code $loc (Ast.Expr(e)) }
  | c1 = command Semicolon c2 = command                                                                    { annotate_2_code $loc (Ast.Seq (c1, c2)) }
  | c1 = command Semicolon                                                                                 { c1 }
  | Skip                                                                                                   { annotate_2_code $loc (Ast.Skip) }
  | Return e = expr                                                                                        { annotate_2_code $loc (Ast.Return (e)) }
  | Banish i = Ident                                                                                       { annotate_2_code $loc (Banish i) }


  | error                                                                                                  { raise (ParseError("command expected")) }
  | command error                                                                                          { raise (ParseError("unexpected command (perhaps you are missing a ';'?)")) }
  | expr Assign error                                                                                      { raise (ParseError("expression expected on the right hand side of =")) }
  | For LParen command Semicolon expr Semicolon command RParen error                                       { raise (ParseError("missing braces after for guard"))}
  | If LParen expr RParen LBrace command RBrace Else error                                                 { raise (ParseError("missing braces after else"))}
  | If LParen expr RParen error                                                                            { raise (ParseError("missing braces after if guard"))}
  | While LParen expr RParen error                                                                         { raise (ParseError("missing braces after while guard"))}
  | Do error                                                                                               { raise (ParseError("missing braces after do"))}
  


perkdef:
  | Let vd = perkvardesc Assign e = expr                                                                   { (vd, e) }
  | error { raise (ParseError("definition expected (e.g. let banana : int = 5)")) }

perkfun:
  | i = Ident LParen id_list = perkvardesc_list RParen Colon rt = perktype LBrace c = command RBrace       { annotate_2_code $loc (Ast.Fundef (rt, i, id_list, c)) }
  | i = Ident LParen RParen Colon rt = perktype LBrace c = command RBrace                                  { annotate_2_code $loc (Ast.Fundef (rt, i, [], c)) }
  

perkvardesc:
  | i = Ident Colon t = perktype                                                                           { (t, i) }
  | i = Ident Colon                                                                                             { (([], Ast.Infer, []), i) }
  | error { raise (ParseError("variable descriptor expected (e.g. banana : int)")) }
  | Ident error { raise (ParseError("variable descriptor expected (e.g. banana : int)")) }

expr:
  | Star e = expr                                                                                          { annotate_2_code $loc (Ast.Pointer e) }
  | e1 = expr LParen args = separated_list(Comma, expr) RParen                                             { annotate_2_code $loc (Ast.Apply (e1, args)) }
  | e1 = expr b = binop e2 = expr                                                                          { annotate_2_code $loc (Ast.Binop (b, e1, e2)) }
  | u = preunop e = expr                                                                                   { annotate_2_code $loc (Ast.PreUnop (u, e)) }
  | e = expr u = postunop %prec POSTFIX                                                                    { annotate_2_code $loc (Ast.PostUnop (u, e)) }
  | LParen id_list = perkvardesc_list RParen Colon ret = perktype Bigarrow LBrace c = command RBrace       { annotate_2_code $loc (Ast.Lambda (ret, id_list, c)) }
  | LParen RParen Colon ret = perktype Bigarrow LBrace c = command RBrace                                  { annotate_2_code $loc (Ast.Lambda (ret, [], c)) }
  | n = Integer                                                                                            { annotate_2_code $loc (Ast.Int (n)) }
  | f = Float                                                                                              { annotate_2_code $loc (Ast.Float (f)) }
  | c = Character                                                                                          { annotate_2_code $loc (Ast.Char (c)) }
  | s = String                                                                                             { annotate_2_code $loc (Ast.String (s)) }
  | i = Ident                                                                                              { annotate_2_code $loc (Ast.Var(i)) }
  | LParen e = expr RParen                                                                                 { annotate_2_code $loc (Ast.Parenthesised e) }
  | e1 = expr LBracket e2 = expr RBracket                                                                  { annotate_2_code $loc (Ast.Subscript (e1, e2)) }
  | Summon i = Ident LParen l = expr_list RParen                                                           { annotate_2_code $loc (Summon (i, l)) }
  | Summon i = Ident LParen RParen                                                                         { annotate_2_code $loc (Summon (i, [])) }
  | e1 = expr Dot i = Ident                                                                                { annotate_2_code $loc (Ast.Access (e1, i)) }
  // | Nothing                                                                                                { annotate_2_code $loc (Ast.Nothing Ast.Infer) }
  // | Something e = expr                                                                                     { annotate_2_code $loc (Ast.Something (e, Ast.Infer)) }
  | LParen RParen                                                                                          { annotate_2_code $loc (Ast.Tuple ([], None)) }
  | LParen e = expr_list RParen                                                                            { annotate_2_code $loc (Ast.Tuple (e, None)) }
  | id = Ident As tl = separated_nonempty_list (Plus, perktype)                                            { annotate_2_code $loc (Ast.As (id, tl)) }

  | error                                                                                                  { raise (ParseError("expression expected")) }
  | expr error                                                                                             { raise (ParseError("unexpected expression")) }
  | Ident error                                                                                            { raise (ParseError("unexpected expression. Perhaps you tried to use C-style types?")) }
  | Summon Ident error                                                                                     { raise (ParseError("error while summoning")) }

%inline perktype_attribute:
  | Public                                                                                                 { Ast.Public }
  | Private                                                                                                { Ast.Private }
  | Static                                                                                                 { Ast.Static }

%inline perktype_qualifier:
  | Const                                                                                                  { Ast.Const }
  | Volatile                                                                                               { Ast.Volatile }
  | Restrict                                                                                               { Ast.Restrict }

%inline perkfuntype:
  | t1 = perktype Arrow t2 = perktype                                                                      { Ast.Funtype ([t1], t2) }
  | LParen RParen Arrow t = perktype                                                                       { Ast.Funtype ([], t) }
  | LParen tl = perktype_list RParen Arrow tf = perktype                                                   { Ast.Funtype (tl, tf) }

perktype:
  | t = perktype_partial q = list(perktype_qualifier)                                                      { ([], t, q) }
  | a = nonempty_list(perktype_attribute) t = perktype_partial q = list(perktype_qualifier)                { (a, t, q) }
  | t = perkfuntype q = list(perktype_qualifier)                                                           { ([], t, q) }
  | a = nonempty_list(perktype_attribute) t = perkfuntype q = list(perktype_qualifier)                     { (a, t, q) }
  | LParen t = perktype RParen                                                                             { t }
  | Ellipsis                                                                                               { ([], Ast.Vararg, []) }
  | error                                                                                                  { raise (ParseError("type expected")) }

perktype_partial:
  | i = Ident                                                                                              { Ast.Basetype i }
  | LBracket t = perktype RBracket                                                                         { Ast.Arraytype (t, None) }
  | LBracket t = perktype n = Integer RBracket                                                             { Ast.Arraytype (t, Some n) }
  | LParen tl = separated_nonempty_list (Star, perktype) RParen                                            { Ast.Tupletype(tl)}
  | LParen RParen                                                                                          { Ast.Tupletype [] }
  | t = perktype Star                                                                                      { Ast.Pointertype t }
  | t = perktype Question                                                                                  { Ast.Optiontype t }
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

%inline preunop:
  | Minus                                                                                                  { Ast.Neg }
  | Bang                                                                                                   { Ast.Not }
  | Ampersand                                                                                              { Ast.Reference }
  | Star                                                                                                   { Ast.Dereference }
  | PlusPlus                                                                                               { Ast.PreIncrement }
  | MinusMinus                                                                                             { Ast.PreDecrement }

%inline postunop:
  | PlusPlus                                                                                               { Ast.PostIncrement }
  | MinusMinus                                                                                             { Ast.PostDecrement }


/* New nonterminals for disambiguated lists */

expr_list:
  | e = expr { [e] }
  | el = expr_list Comma e = expr { el @ [e] }
  | error { raise (ParseError("expression expected")) }

ident_list:
  | i = Ident { [i] }
  | il = ident_list Comma i = Ident { il @ [i] }
  | error { raise (ParseError("identifier expected")) }
  | Ident error { raise (ParseError("unexpected identifier")) }

perktype_list:
  | t = perktype { [t] }
  | tl = perktype Comma t = perktype_list { tl :: t }
  | error { raise (ParseError("type expected")) }
  | perktype error { raise (ParseError("unexpected type")) }

perkdef_list:
  | t = perkdef { [t] }
  | tl = perkdef Comma t = perkdef_list { tl :: t }
  | error { raise (ParseError("definition expected")) }
  | perkdef error { raise (ParseError("unexpected definition")) }

perkvardesc_list:
  | t = perkvardesc { [t] }
  | tl = perkvardesc Comma t = perkvardesc_list { tl :: t }
  | error { raise (ParseError("variable descriptor expected")) }
  | perkvardesc error { raise (ParseError("unexpected variable descriptor")) }

spanish_inquisition:
  | error { raise (ParseError("Nobody expects the Spanish Inquisition!")) }
%%