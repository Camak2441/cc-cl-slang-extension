
/* Auxiliary code */

%{

let get_loc = Parsing.symbol_start_pos 

%}

/* Tokens and types */
%token<int> INT
%token<string> IDENT
%token EOF LPAREN RPAREN COMMA COLON SEMICOLON ADD SUB MUL DIV NOT EQUAL LT ANDOP OROP CONS
%token WHAT UNIT AND TRUE FALSE IF FI THEN ELSE LET REC IN BEGIN END BOOL INTTYPE UNITTYPE LISTTYPE SEQTYPE THUNKTYPE
%token ARROW BAR INL INR FST SND FUN NUF CASE OF REF ASSIGN BANG DOUBLEBANG WHILE DO OD APOSTROPHE EMPTY HEAD TAIL

%right CONS
%left ASSIGN              
%left ADD SUB                     /* lowest precedence */
%left MUL DIV ANDOP OROP EQUAL ARROW  LT /* medium precedence */
/*
%nonassoc THEN    
%nonassoc ELSE    
*/ 
%nonassoc UMINUS                  
/* Finally, the first tokens of simple_expr are above everything else. */
%nonassoc UNIT EMPTY INT WHAT IDENT TRUE FALSE LPAREN NOT BANG REF APOSTROPHE DOUBLEBANG HEAD TAIL/* highest precedence */
                   
%start start
%type <Past.type_expr> texpr
%type <Past.expr> simple_expr 
%type <Past.expr> expr1 
%type <Past.expr> expr 
%type <Past.expr list> exprlist
%type <Past.expr> start

%%

/* Grammar  */

start: 
| expr EOF { $1 }

/* problem 
   -e  (unary minus) 
    e e (application) 
    e1 - e2  (is the e1(-e2) or e1-e2???) 
*/

simple_expr: /* alternate name: expr2 */
| UNIT                               { Past.Unit (get_loc())}
| EMPTY                              { Past.Empty (get_loc())}
| INT                                { Past.Integer (get_loc(), $1) }
| WHAT                               { Past.What (get_loc())} 
| IDENT                              { Past.Var (get_loc(), $1) }
| TRUE                               { Past.Boolean (get_loc(), true)}
| FALSE                              { Past.Boolean (get_loc(), false)}
| LPAREN expr RPAREN                 { $2 }
| LPAREN expr COMMA expr RPAREN      { Past.Pair(get_loc(), $2, $4) }
| NOT simple_expr                    { Past.UnaryOp(get_loc(), Past.NOT, $2) }
| BANG simple_expr                   { Past.Deref(get_loc(), $2) }
| DOUBLEBANG simple_expr             { Past.Strict(get_loc(), $2) }
| HEAD simple_expr                   { Past.UnaryOp(get_loc(), Past.HEAD, $2) }
| TAIL simple_expr                   { Past.UnaryOp(get_loc(), Past.TAIL, $2) }
| REF simple_expr                    { Past.Ref(get_loc(), $2) }
| APOSTROPHE simple_expr             { Past.Lazy(get_loc(), $2)}

/*
    expr1 binds more tightly than expr, so
    (fun (x: int) -> x + x) 2 
    parses as: (fun (x: int) -> (x + x)) 2
    NOT: ((fun (x: int) -> x) + x) 2
*/

expr1:
| simple_expr                        { $1 }
| SUB expr1 %prec UNIT               { Past.UnaryOp(get_loc(), Past.NEG, $2) } 
| expr1 ADD expr1                    { Past.Op(get_loc(), $1, Past.ADD, $3) }
| expr1 SUB expr1                    { Past.Op(get_loc(), $1, Past.SUB, $3) }
| expr1 MUL expr1                    { Past.Op(get_loc(), $1, Past.MUL, $3) }
| expr1 DIV expr1                    { Past.Op(get_loc(), $1, Past.DIV, $3) }
| expr1 CONS expr1                   { Past.Op(get_loc(), $1, Past.CONS, $3) }
| expr1 LT expr1                     { Past.Op(get_loc(), $1, Past.LT, $3) }
| expr1 EQUAL expr1                  { Past.Op(get_loc(), $1, Past.EQ, $3) }
| expr1 ANDOP expr1                  { Past.Op(get_loc(), $1, Past.AND, $3) }
| expr1 OROP expr1                   { Past.Op(get_loc(), $1, Past.OR, $3) }
| expr1 ASSIGN expr1                 { Past.Assign(get_loc(), $1, $3) }
| expr1 simple_expr                  { Past.App (get_loc(), $1, $2) } 

expr:
| expr1                              { $1 }
| BEGIN exprlist END                 { Past.Seq(get_loc(), $2) }
| IF expr THEN expr ELSE expr        { Past.If(get_loc(), $2, $4, $6) }
| WHILE expr DO expr                 { Past.While(get_loc(), $2, $4) }
| FST expr %prec UMINUS              { Past.Fst(get_loc(), $2) }
| SND expr %prec UMINUS              { Past.Snd(get_loc(), $2) }
| INL texpr expr %prec UMINUS        { Past.Inl(get_loc(), $2, $3) }
| INR texpr expr %prec UMINUS        { Past.Inr(get_loc(), $2, $3) }
| FUN LPAREN IDENT COLON texpr RPAREN ARROW expr
                                     { Past.Lambda(get_loc(), ($3, $5, $8)) }
| FUN paramList ARROW expr
                                     { Past.MultiLambda(get_loc(), ($2, $4)) }
| LET IDENT COLON texpr EQUAL expr IN expr
                                     { Past.Let (get_loc(), $2, $4, $6, $8) }
| LET IDENT LPAREN IDENT COLON texpr RPAREN COLON texpr EQUAL expr IN expr 
                                     { Past.LetFun (get_loc(), $2, ($4, $6, $11), $9, $13) }
| LET IDENT paramList COLON texpr EQUAL expr IN expr 
                                     { Past.LetMultiFun (get_loc(), $2, ($3, $7), $5, $9) }
| CASE expr OF 
      INL LPAREN IDENT COLON texpr RPAREN ARROW expr 
  BAR INR LPAREN IDENT COLON texpr RPAREN  ARROW expr  
                                     { Past.Case (get_loc(), $2, ($6, $8, $11), ($15, $17, $20)) }

param:
| LPAREN IDENT COLON texpr RPAREN    { ($2, $4) }

paramList:
| param                              { [$1] }
| param paramList                    { $1 :: $2 }

exprlist:
|   expr                             { [$1] }
|   expr  SEMICOLON exprlist         { $1 :: $3  }

texpr: 
| stexpr                             { $1 }
| stexpr THUNKTYPE                   { Past.TEthunk $1}

stexpr:
| BOOL                               { Past.TEbool  }
| INTTYPE                            { Past.TEint  }
| UNITTYPE                           { Past.TEunit  }
| texpr LISTTYPE                     { Past.TElist ($1, false)}
| texpr SEQTYPE                      { Past.TElist ($1, true)}
| texpr ARROW texpr                  { Past.TEarrow ($1, $3)}
| texpr MUL texpr                    { Past.TEproduct ($1, $3)}
| texpr ADD texpr                    { Past.TEunion ($1, $3)}
| texpr REF                          { Past.TEref $1 } 
| LPAREN texpr RPAREN                { $2 } 

