%{     /* parse.y    Pascal Parser      Gordon S. Novak Jr.  ; 25 Jul 19   */

/* Copyright (c) 2019 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */
/* 30 Jul 13 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use: make parser */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <string.h>
#include <math.h>
#include <assert.h>
#include <stdbool.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"
#include "codegen.h"

static void binop_fix(TOKEN op, TOKEN lhs, TOKEN rhs);
static void binop_float(TOKEN op, TOKEN lhs, TOKEN rhs);
static void setarg(TOKEN tok, int *size, int padding);
static TOKEN reduce_array(TOKEN var, TOKEN dot, TOKEN field);
static int reduce_record(SYMBOL sym, TOKEN field);
static TOKEN array_ref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb);
static TOKEN array2d_ref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb);

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH


%%

program         : PROGRAM IDENTIFIER LPAREN idlist RPAREN SEMICOLON lblock DOT
                      { parseresult = makeprogram($2, $4, $7); }
                ;
lblock          : LABEL numlist SEMICOLON cblock { $$ = $4; }
                | cblock
                ;
numlist         : numlist COMMA NUMBER           { instlabel($3); }
                | NUMBER                         { instlabel($1); }
                ;
cblock          : CONST cdef_list tblock         { $$ = $3; }
                | tblock
                ;
cdef_list       : cdef SEMICOLON cdef_list
                | cdef SEMICOLON
                ;
cdef            : IDENTIFIER EQ constant         { instconst($1, $3); }
                ;
constant        : sign IDENTIFIER                { $$ = unaryop($1, findtype($2)); }
                | IDENTIFIER                     { $$ = findtype($1); }
                | sign NUMBER                    { $$ = mulint($2, $1->intval); }
                | NUMBER                         { $$ = findtype($1); }
                | STRING                         { $$ = $1; }
                ;
tblock          : TYPE tdef_list vblock          { $$ = $3; }
                | vblock
                ;
tdef_list       : tdef SEMICOLON tdef_list
                | tdef SEMICOLON
                ;
tdef            : IDENTIFIER EQ type             { insttype($1, $3); }
                ;
vblock          : VAR varspecs block             { $$ = $3; }
                | block
                ;
varspecs        : vargroup SEMICOLON varspecs
                | vargroup SEMICOLON
                ;
vargroup        : idlist COLON type              { instvars($1, $3); }
                ;
type            : simpletype
                | ARRAY LBRACKET simpletype_list RBRACKET OF type
                                                 { $$ = instarray($3, $6); }
                | RECORD field_list END          { $$ = instrec($1, $2); }
                | POINT IDENTIFIER               { $$ = instpoint($1, $2); }
                ;
simpletype      : IDENTIFIER                     { $$ = findtype($1); }
                | LPAREN idlist RPAREN           { $$ = instenum($2); }
                | constant DOTDOT constant       
                          { $$ = makesubrange($2, $1->intval, $3->intval); }
                ;
simpletype_list : simpletype COMMA simpletype_list
                                                  { $$ = instarray($1, $3); }
                | simpletype
                ;
block           : BEGINBEGIN statement endpart   { $$ = makeprogn($1, cons($2, $3)); }
                ;
statement       : BEGINBEGIN statement endpart
                          { $$ = makeprogn($1,cons($2, $3)); }
                | IF expression THEN statement endif
                          { $$ = makeif($1, $2, $4, $5); }
                | assignment
                | funcall
                | WHILE expression DO statement
                          { $$ = makewhile($1, $2, $3, $4); }
                | REPEAT statement_list UNTIL expression
                          { $$ = makerepeat($1, $2, $3, $4); }
                | FOR assignment TO expression DO statement
                          { $$ = makefor(1, $1, $2, $3, $4, $5, $6);}
                | GOTO NUMBER                    { $$ = dogoto($1, $2); }
                | label
                ;
assignment      : variable ASSIGN expression     { $$ = binop($2, $1, $3); }
                ;
statement_list  : statement SEMICOLON statement_list
                                                 { $$ = cons($1, $3); }
                | statement
                ;
label           : NUMBER COLON statement         { $$ = dolabel($1, $2, $3); }
                ;
endpart         : SEMICOLON statement endpart    { $$ = cons($2, $3); }
                | END                            { $$ = NULL; }
                ;
endif           : ELSE statement                 { $$ = $2; }
                | /* empty */                    { $$ = NULL; }
                ;
expression      : expression compare_op expr     { $$ = binop($2, $1, $3); }
                | expr
                ;
compare_op      : EQ                             { $$ = $1; }
                | LT                             { $$ = $1; }
                | GT                             { $$ = $1; }
                | NE                             { $$ = $1; }
                | GE                             { $$ = $1; }
                | IN                             { $$ = $1; }
                ;
expr            : sign term                      { $$ = unaryop($1, $2); }
                | term
                | expr plus_op term              { $$ = binop($2, $1, $3); }
                ;
plus_op         : PLUS                           { $$ = $1; }
                | MINUS                          { $$ = $1; }
                | OR                             { $$ = $1; }
                ;
term            : term times_op factor           { $$ = binop($2, $1, $3); }
                | factor
                ;
times_op        : TIMES                          { $$ = $1; }
                | DIVIDE                         { $$ = $1; }
                | DIV                            { $$ = $1; }
                | MOD                            { $$ = $1; }
                | AND                            { $$ = $1; }
                ;
factor          : unsigned_constant
                | variable
                | funcall
                | LPAREN expression RPAREN       { $$ = $2; }
                | NOT factor
                ;
unsigned_constant : NUMBER                       { $$ = $1; }
                | NIL                            { $$ = fillintc($1, 0); }
                | STRING                         { $$ = $1; }
                ;
variable        : IDENTIFIER                     { $$ = findid($1); }
                | variable LBRACKET expr_list RBRACKET
                                                 { $$ = arrayref($1, $2, $3, $4); }
                | variable DOT IDENTIFIER        { $$ = reducedot($1, $2, $3); }
                | variable POINT                 { $$ = dopoint($1, $2); }
                ;
funcall         : IDENTIFIER LPAREN expr_list RPAREN  { $$ = makefuncall($4, $1, $3); }
                ;
expr_list       : expression COMMA expr_list     { $$ = cons($1, $3); }
                | expression
                ;
field_list      : fields SEMICOLON field_list    { $$ = nconc($1, $3); }
                | fields                         { $$ = nconc(NULL, $1); }
                ;
fields          : idlist COLON type              { $$ = instfields($1, $3); }
                ;
idlist          : IDENTIFIER COMMA idlist        { $$ = cons($1, $3); }
                | IDENTIFIER                     { $$ = cons($1, NULL); }
                ;
sign            : PLUS                           { $$ = $1; }
                | MINUS                          { $$ = $1; }
                ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG          0           /* set bits here for debugging, 0 = off  */
#define DB_CONS        1           /* bit to trace cons */
#define DB_BINOP       2           /* bit to trace binop */
#define DB_MAKEIF      4           /* bit to trace makeif */
#define DB_MAKEWHILE   4           /* bit to trace makewhile */
#define DB_MAKEFOR     4           /* bit to trace makefor */
#define DB_FINDID      8           /* bit to trace findid */
#define DB_INSTCONST   8           /* bit to trace instconst */
#define DB_FINDTYPE   16           /* bit to trace findtype */
#define DB_INSTVARS   32           /* bit to trace instvars */
#define DB_INSTPOINT  32           /* bit to trace instpoint */
#define DB_REDUCEDOT  64           /* bit to trace reducedot */
#define DB_DOPOINT    64           /* bit to trace dopoint */
#define DB_ARRAYREF  128           /* bit to trace arrayref */
#define DB_PARSERES    0           /* bit to trace parseresult */

  int labelnumber = 0;  /* sequential counter for internal label numbers */
  int labels[64];

/* cons links a new item onto the front of a list.  Equivalent to a push.
   (cons 'a '(b c))  =  (a b c)    */
TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
/* nconc should return lista, or listb if lista is NULL. */
TOKEN nconc(TOKEN lista, TOKEN listb)
  { if (lista == NULL) return listb;
    TOKEN a = lista;
    while (a->link != NULL)
       { a = a->link;
       };
    a->link = listb;
    return lista;
  }

/* binop links a binary operator op to two operands, lhs and rhs. */
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */

    if (lhs->whichval == FUNCALLOP)
       { SYMBOL sym = searchst(lhs->operands->stringval);
         lhs->basicdt = sym->datatype->basicdt;
       };
    if (rhs->whichval == FUNCALLOP)
       { SYMBOL sym = searchst(rhs->operands->stringval);
         rhs->basicdt = sym->datatype->basicdt;
       };
    /* type propagation */
    op->basicdt = (lhs->basicdt > rhs->basicdt) ? lhs->basicdt : rhs->basicdt;
    if (op->whichval == ASSIGNOP && lhs->basicdt == INTEGER && rhs->basicdt == REAL)
       { binop_fix(op, lhs, rhs);
       }
    else if (op->whichval == ASSIGNOP && lhs->basicdt == REAL && rhs->basicdt == INTEGER)
       { makefloat(rhs);
       } /* TODO add < I X pg 141 ie compare ops) */
    else if (lhs->basicdt == INTEGER && rhs->basicdt == REAL)
       { op->basicdt = REAL;
         if (lhs->symentry && lhs->symentry->kind == CONSTSYM)
            { makefloat(lhs);
              return op;
            };
         binop_float(op, lhs, rhs);
       }
    else if (lhs->basicdt == REAL && rhs->basicdt == INTEGER)
       { op->basicdt = REAL;
         if (rhs->symentry && rhs->symentry->kind == CONSTSYM)
            { makefloat(rhs);
              return op;
            };
         binop_float(op, rhs, lhs); /* lhs and rhs flipped */
       }; /* remove ^ not necessary? (pg 141)  */
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }

/* binop assign coercion helper */
static void binop_fix(TOKEN op, TOKEN lhs, TOKEN rhs)
  { TOKEN tokcoer = makeop(FIXOP);
    tokcoer->basicdt = INTEGER;
    lhs->link = tokcoer;
    tokcoer->operands = rhs;
  }

/* binop operator coercion helper */
static void binop_float(TOKEN op, TOKEN lhs, TOKEN rhs)
  { TOKEN tokfloat = makeop(FLOATOP);
    tokfloat->basicdt = REAL;
    op->operands = rhs;
    rhs->link = tokfloat;
    tokfloat->operands = lhs;
  }

/* unaryop links a unary operator op to one operand, lhs */
TOKEN unaryop(TOKEN op, TOKEN lhs)
  { op->operands = lhs;
    op->basicdt = lhs->basicdt;
    return op;
  }

/* makeop makes a new operator token with operator number opnum.
   Example:  makeop(FLOATOP)  */
TOKEN makeop(int opnum)
  { TOKEN tok = (TOKEN) talloc();   /* = new token */
    tok->tokentype = OPERATOR;
    tok->whichval = opnum;
    return tok;
  }

/* makefloat forces the item tok to be floating, by floating a constant
   or by inserting a FLOATOP operator */
TOKEN makefloat(TOKEN tok)
  { tok->basicdt = REAL;
    tok->realval = 1.0 * tok->intval;
    return tok;
  }

/* makefix forces the item tok to be integer, by truncating a constant
   or by inserting a FIXOP operator */
// TOKEN makefix(TOKEN tok)
//   { tok->basicdt = INTEGER;
//     tok->intval = trunc(tok->realval);
//     return tok;
//   } /* TODO unused */

/* fillintc smashes tok, making it into an INTEGER constant with value num */
TOKEN fillintc(TOKEN tok, int num)
  { int toktype = tok->tokentype;
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    if (toktype == RESERVED && tok->whichval == (NIL - RESERVED_BIAS))
       { tok->basicdt = POINTER;
       };
    tok->symtype = NULL;
    tok->symentry = NULL;
    tok->operands = NULL;
    tok->link = NULL;
    tok->intval = num;
    return tok;
  }

/* makeintc makes a new integer number token with num as its value */
TOKEN makeintc(int num)
  { TOKEN tok = (TOKEN) talloc();
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = num;
    return tok;
  }

/* copytok makes a new token that is a copy of origtok */
TOKEN copytok(TOKEN origtok)
  { TOKEN tok = (TOKEN) talloc();   /* = new token */
    tok->tokentype = origtok->tokentype;
    tok->basicdt = origtok->basicdt;
    tok->symtype = origtok->symtype;
    tok->symentry = origtok->symtype;
    tok->operands = origtok->operands;
    tok->link = origtok->link;
    tok->tokenval = origtok->tokenval;
    return tok;
  }

/* makeif makes an IF operator and links it to its arguments.
   tok is a (now) unused token that is recycled to become an IFOP operator */
TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

/* makeprogn makes a PROGN operator and links it to the list of statements.
   tok is a (now) unused token that is recycled. */
TOKEN makeprogn(TOKEN tok, TOKEN statements)
  { tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = statements;
    return tok;
  }

/* makelabel makes a new label, using labelnumber++ */
TOKEN makelabel()
  { TOKEN toklabel = makeop(LABELOP);
    toklabel->operands = makeintc(labelnumber++);
    return toklabel;
  }

/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement)
  { int i;
    for (i = 0; i < 64; i++)
       { if (labels[i] == labeltok->intval) break;
       }
    labeltok->tokentype = OPERATOR;
    labeltok->whichval = LABELOP;
    labeltok->operands = makeintc(i);
    labeltok->link = statement;
    return makeprogn(tok, labeltok);
  }

/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num)
  { labels[labelnumber++] = num->intval;
  }

/* makegoto makes a GOTO operator to go to the specified label.
   The label number is put into a number token. */
TOKEN makegoto(int label)
  {  TOKEN tokgoto = makeop(GOTOOP);
     tokgoto->operands = makeintc(label);
     return tokgoto;
  }

/* dogoto is the action for a goto statement.
   tok is a (now) unused token that is recycled. */
TOKEN dogoto(TOKEN tok, TOKEN labeltok)
  { tok->tokentype = OPERATOR;
    tok->whichval = GOTOOP;
    int i;
    for (i = 0; i < 64; i++)
       { if (labels[i] == labeltok->intval)
            { labeltok->intval = i;
              break;
            }
       }
    tok->operands = labeltok;
    return tok;
  }

/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
  { tok->tokentype = OPERATOR;
    tok->whichval = FUNCALLOP;
    tok->operands = fn;
    if (strncmp(fn->stringval, "new", 16) == 0)
       { TOKEN tokas = makeop(ASSIGNOP);
         SYMBOL typesym = searchst(args->symtype->datatype->namestring);
         binop(tokas, args, tok);
         fn->link = makeintc(typesym->size);
         return tokas;
       };
    fn->link = args;
    if (strncmp(fn->stringval, "writeln", 16) == 0)
       { if (args->basicdt == 0) 
            { strcpy(fn->stringval, "writelni"); };
         if (args->basicdt == 1)
            { strcpy(fn->stringval, "writelnf"); };
       };
    return tok;
  }

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements)
  { TOKEN tokprogram = (TOKEN) talloc();
    tokprogram->tokentype = OPERATOR;
    tokprogram->whichval = PROGRAMOP;
    tokprogram->operands = name;
    TOKEN tokprogn = (TOKEN) talloc();
    name->link = makeprogn(tokprogn, args);
    tokprogn->link = statements;
    return tokprogram;
  }

/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement)
  { if (DEBUG & DB_MAKEWHILE)
        { printf("makewhile\n");
          dbugprinttok(tok);
          dbugprinttok(expr);
          dbugprinttok(tokb);
          dbugprinttok(statement);
        };
    TOKEN toklabel = makelabel();
    TOKEN toklab = makeprogn(tok, toklabel);
    TOKEN tokstat = makeprogn(tokb, statement);
    TOKEN tokif = makeop(IFOP);
    tokif->operands = expr;
    tokif->basicdt = expr->basicdt;
    expr->link = tokstat;
    tokstat->operands->link = makegoto(labelnumber - 1);
    toklabel->link = tokif;
    return toklab;
  }

/* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr)
  { TOKEN toklabel = makelabel();
    TOKEN toklab = makeprogn(tok, toklabel);
    TOKEN tokstat = makeprogn(tokb, statements);
    toklabel->link = tokstat;
    TOKEN tokif = (TOKEN) talloc();
    tokif->basicdt = BOOLETYPE;
    TOKEN toknoop = (TOKEN) talloc();
    makeif(tokif, expr, makeprogn(toknoop, NULL), makegoto(labelnumber - 1));
    tokstat->link = tokif;
    return toklab;
  }

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement)
  { if (sign > 0)
       { makeprogn(tok, asg);
         TOKEN tok1 = copytok(asg->operands);
         TOKEN tok2 = copytok(asg->operands);
         TOKEN toklabel = makelabel();
         asg->link = toklabel;
         /* tokb becomes if statement with goto */
         toklabel->link = tokb;
         TOKEN tokle = binop(makeop(LEOP), tok1, endexpr);
         /* tokc becomes progn containing thenpart and i++ and goto */
         makeif(tokb, tokle, makeprogn(tokc, statement), NULL);
         tokb->basicdt = BOOLETYPE;
         statement->link = makeplus(tok2, makeintc(1), makeop(PLUSOP));
         statement->link->link = makegoto(labelnumber - 1);
       };
 /* else
      { change sign in function call and implement downto
      } */
    if (DEBUG & DB_MAKEFOR)
       { printf("\nmakefor\n");
         dbugprinttok(tok);
         dbugprinttok(asg);
         dbugprinttok(tokb);
         dbugprinttok(endexpr);
         dbugprinttok(tokc);
         dbugprinttok(statement);
       };
    return tok;
  }

/* findid finds an identifier in the symbol table, sets up symbol table
   pointers, changes a constant to its number equivalent */
TOKEN findid(TOKEN tok) /* the ID token */
  {  if (DEBUG & DB_FINDID)
        { printf("findid\n");
          dbugprinttok(tok);
        };
     SYMBOL sym = searchst(tok->stringval);
     tok->symentry = sym;
     SYMBOL typ = sym->datatype;
     tok->symtype = typ;
     if (typ->kind == BASICTYPE ||
            typ->kind == POINTERSYM)
        { tok->basicdt = typ->basicdt; };
     if (sym->kind == CONSTSYM) /* set a constant to its number */
        { switch (sym->basicdt)
          { case INTEGER:
            case BOOLETYPE:
              tok->tokentype = NUMBERTOK;
              tok->intval = sym->constval.intnum;
              break;
            case REAL:
            case POINTER:
              tok->tokentype = NUMBERTOK;
              tok->realval = sym->constval.realnum;
              break;
            case STRINGTYPE:
              strcpy(tok->stringval, sym->constval.stringconst);
              break;
          };
        };
     return tok;
  }

/* instconst installs a constant in the symbol table */
void  instconst(TOKEN idtok, TOKEN consttok)
  {  if (DEBUG & DB_INSTCONST)
        { printf("instconst\n");
          dbugprinttok(idtok);
          dbugprinttok(consttok);
        };
     SYMBOL typesym = consttok->symtype;
     SYMBOL sym = insertsym(idtok->stringval);
     sym->kind = CONSTSYM;
     sym->datatype = typesym;
     sym->size = typesym->size;
     sym->basicdt = typesym->basicdt;
     switch (sym->basicdt)
        { case INTEGER:
          case BOOLETYPE:
            sym->constval.intnum = consttok->intval;
            break;
          case REAL:
          case POINTER:
            sym->constval.realnum = consttok->realval;
            break;
          case STRINGTYPE:
            strcpy(sym->constval.stringconst, consttok->stringval);
            break;
        };
  }

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high)
  { SYMBOL sym = symalloc();
    sym->kind = SUBRANGE;
    sym->basicdt = INTEGER;
    sym->size = basicsizes[INTEGER];
    sym->lowbound = low;
    sym->highbound = high;
    tok->symtype = sym;
    return tok;
  }

/* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist)
  { TOKEN tokid = idlist;
    int high = 0;
    while (tokid)
       { SYMBOL sym = insertsym(tokid->stringval);
         sym->kind = CONSTSYM;
         sym->basicdt = INTEGER;
         sym->datatype = searchst("integer");
         sym->size = basicsizes[INTEGER];
         sym->constval.intnum = high;
         tokid->symentry = sym;
         tokid = tokid->link;
         high++;
       };
    return makesubrange(idlist, 0, high - 1);;
  }

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok)
  { if (DEBUG & DB_FINDTYPE)
       { printf("findtype\n");
         dbugprinttok(tok);
       };
    if (tok->tokentype == NUMBERTOK)
       { switch (tok->basicdt)
            { case INTEGER:
                tok->symtype = searchst("integer");
                break;
              case REAL:
              case POINTER:
                tok->symtype = searchst("real");
                break;
              case STRINGTYPE:
                tok->symtype = searchst("char");
                break;
              case BOOLETYPE:
                tok->symtype = searchst("boolean");
                break;
            };
       }
    else
       { SYMBOL sym = searchst(tok->stringval);
         tok->symtype = sym;
         if (sym->kind == TYPESYM)
            { 
              tok->symtype = sym->datatype;
            };
       };
    return tok;
  }

/* wordaddress pads the offset n to be a multiple of wordsize.
   wordsize should be 4 for integer, 8 for real and pointers,
   16 for records and arrays */
int   wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }

/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type. */
void  instvars(TOKEN idlist, TOKEN typetok)
  {  if (DEBUG & DB_INSTVARS)
        { printf("instvars\n");
          dbugprinttok(idlist);
          dbugprinttok(typetok);
        };
     SYMBOL typesym = typetok->symtype;
     int align = alignsize(typesym);
     SYMBOL sym;
     while (idlist != NULL) /* for each id */
        { sym = insertsym(idlist->stringval);
          sym->kind = VARSYM;
          sym->offset = /* "next" */
              wordaddress(blockoffs[blocknumber], align);
          sym->size = typesym->size;
          blockoffs[blocknumber] = /* "next" */
              sym->offset + sym->size;
          sym->datatype = typesym;
          sym->basicdt = typesym->basicdt;
          idlist = idlist->link;
        };
  }

/* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok)
  { SYMBOL sym = insertsym(typename->stringval);
    SYMBOL typesym = typetok->symtype;
    sym->kind = TYPESYM;
    sym->datatype = typesym;
    sym->size = typesym->size;
    sym->lowbound = typesym->lowbound;
    sym->highbound = typesym->highbound;
  }

/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename)
  { SYMBOL sym = symalloc();
    sym->kind = POINTERSYM;
    sym->basicdt = POINTER;
    sym->datatype = makesym(typename->stringval);
    sym->size = basicsizes[POINTER];
    tok->symtype = sym;
    if (DEBUG & DB_INSTPOINT) {
       printf("instpoint\n");
       dbugprinttok(tok);
       dbugprinttok(typename);
    }
    return tok;
  }

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type.  rectok is just a trash token to be
   used to return the result in its symtype */
TOKEN instrec(TOKEN rectok, TOKEN argstok)
  { int size = 0;
    int padding = 0;
    TOKEN tok = argstok;
    while (tok->link != NULL)
       { setarg(tok, &size, padding);
         padding = size % RECORDALIGN;
         /* records/arrays alinged to 16, real/pointers to 8 */
         if (tok->symentry->size % RECORDALIGN != 0 && padding == 0)
            { tok->link->symentry->offset = padding; }
         tok->symentry->link = tok->link->symentry;
         tok = tok->link;
       };
    setarg(tok, &size, padding);
    padding = 0;
    int align = size % (RECORDALIGN + RECORDALIGN);
    if (align != 0)
       { padding = (RECORDALIGN + RECORDALIGN) - align; };
    SYMBOL recordsym = symalloc();
    recordsym->kind = RECORDSYM;
    recordsym->datatype = argstok->symentry;
    recordsym->size = size + padding;
    rectok->symtype = recordsym;
    return rectok;
  }

static void setarg(TOKEN tok, int *size, int padding)
  { tok->symentry->offset += *size + padding;
    *size += tok->symentry->size + padding;
  }

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok)
  { SYMBOL typesym = typetok->symtype;
    TOKEN tokid = idlist;
    while (tokid)
       { SYMBOL sym = makesym(tokid->stringval);
         sym->kind = ARGSYM;
         sym->datatype = typesym;
         sym->size = typesym->size;
         tokid->symentry = sym;
         tokid = tokid->link;
       }
    return idlist;
  }

/* makeplus makes a + operator.
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok)
  { tok = (tok) ? tok : (TOKEN) talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = PLUSOP;
    TOKEN tokas = makeop(ASSIGNOP);
    tokas->operands = lhs;
    TOKEN tok1 = copytok(lhs);
    lhs->link = binop(tok, tok1, rhs);
    tokas->basicdt = tok->basicdt;
    return tokas;
  }

/* addoffs adds offset, off, to an aref expression, exp */
TOKEN addoffs(TOKEN exp, TOKEN off)
  { exp->intval = off->intval;
    return exp;
  }

/* mulint multiplies expression exp by integer n */
TOKEN mulint(TOKEN exp, int n)
  { int dt = exp->basicdt;
    if (dt == INTEGER || dt == BOOLETYPE) exp->intval *= n;
    if (dt == REAL || dt == POINTER) exp->realval *= n;
    return exp;
  }

/* makearef makes an array reference operation.
   off is be an integer constant token
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok)
  { tok = (tok) ? tok : (TOKEN) talloc();
    if (var && var->whichval != AREFOP) {
      tok->tokentype = OPERATOR;
      tok->whichval = AREFOP;
      tok->operands = var;
      var->link = off;
      return tok;
    }
    addoffs(var->operands->link, off);
    return var;
  }

/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field)
  { if (DEBUG & DB_REDUCEDOT)
       { printf("reducedot\n");
         dbugprinttok(var);
         dbugprinttok(dot);
         dbugprinttok(field);
       };
    int offset = 0;
    TOKEN varid = var;
    TOKEN varog = var;
    if (var->whichval == POINTEROP && var->operands->whichval == AREFOP) var = var->operands;
    if (var->whichval == AREFOP)
       { if (var->operands->symtype && var->operands->symtype->kind == ARRAYSYM)
            { return reduce_array(var, dot, field); };
         while (var->operands)
            { if (var->operands->symtype && var->operands->symtype->kind == RECORDSYM) break;
              var = var->operands;
            };
         var = var->operands;
       };
    assert( var->symtype->kind == RECORDSYM );
    SYMBOL sym = var->symtype->datatype;
    while (strncmp(sym->namestring, field->stringval, 16))
       { if (sym->datatype->kind == RECORDSYM)
            { int result = reduce_record(sym->datatype->datatype, field);
              if (result != -1)
                 { offset = sym->offset + result;
                    TOKEN tokoff = fillintc(field, offset);
                    TOKEN tokresult = makearef(varid, tokoff, dot);
                    if (sym->datatype->kind == RECORDSYM)
                       { varid->basicdt = sym->datatype->datatype->datatype->basicdt;
                       }
                    else if (sym->kind == BASICTYPE) varid->basicdt = sym->datatype->kind;
                    return tokresult;
                 }
            };
         sym = sym->link;
         offset = sym->offset;
       };
    TOKEN tokoff;
    if (sym->datatype->kind == RECORDSYM)
       { tokoff = fillintc(field, sym->offset);
         varog = makearef(varog, tokoff, dot);
         return varog;
       };
    tokoff = fillintc(field, offset);
    varid = makearef(varid, tokoff, dot);
    if (sym->datatype->kind == RECORDSYM)
       { varid->basicdt = sym->datatype->datatype->datatype->basicdt;
       }
    else if (sym->datatype->kind == BASICTYPE) varid->basicdt = sym->datatype->basicdt;
    return varid;
  }

static TOKEN reduce_array(TOKEN var, TOKEN dot, TOKEN field)
  { int offset = 0;
    SYMBOL sym = var->operands->symtype->datatype->datatype;
    while (strncmp(sym->namestring, field->stringval, 16))
      { if (sym->datatype->kind == RECORDSYM)
            { int result = reduce_record(sym->datatype->datatype, field);
              if (result != -1)
                { offset = sym->offset + result;
                  break;
                };
            };
        sym = sym->link;
        offset = sym->offset;
      };
    if (!var->operands->link->operands)
       { var->operands->link->intval += offset;
         return var;
       }
    else /* IDENTIFIERTOK */
       { dot->tokentype = OPERATOR;
         dot->whichval = PLUSOP;
         if (var->operands->symtype->lowbound == 1)
            { offset = (-1 * var->operands->symtype->offset) + offset;
            }
         else
            { offset = (var->operands->link->operands->symtype->size - var->operands->symtype->lowbound)
                        * var->operands->symtype->offset;
              offset *= -1;
              offset += sym->offset;
            };
         binop(dot, var->operands->link, fillintc(field, offset));
         var->operands->link = dot;
         return var;
       };
  }

static int reduce_record(SYMBOL sym, TOKEN field)
  { while (sym && strncmp(sym->namestring, field->stringval, 16))
       { sym = sym->link;
       }
    if (sym) return sym->offset;
    return -1;
  }

/* arrayref processes an array reference a[i]
   subs is a list of subscript expressions.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb)
  { if (DEBUG & DB_ARRAYREF)
       { printf("arrayref\n");
         dbugprinttok(arr);
         dbugprinttok(tok);
         dbugprinttok(subs);
         dbugprinttok(tokb);
       };
    assert( arr->symtype->kind == ARRAYSYM );
    if (!subs->link) return array_ref(arr, tok, subs, tokb);
    return array2d_ref(arr, tok, subs, tokb);
  }

static TOKEN array_ref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb)
  { int offset = 0;
    SYMBOL typesym = arr->symtype->datatype;
    if (subs->tokentype == NUMBERTOK)
       { offset = (typesym->size * (subs->intval - arr->symtype->lowbound));
         return makearef(arr, fillintc(tokb, offset), tok);
       }
    else /* IDENTIFIERTOK */
       { TOKEN tokmult = makeop(TIMESOP);
         binop(tokmult, subs, fillintc(tokb, typesym->size));
         return makearef(arr, tokmult, tok);
       }
  }


static TOKEN array2d_ref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb)
  { int offset = 0;
    SYMBOL typesym = arr->symtype->datatype;
    if (subs->tokentype == NUMBERTOK)
       { offset = (subs->intval - arr->symtype->lowbound) * typesym->size;
         offset += (subs->link->intval - typesym->lowbound) * typesym->datatype->size;
         return makearef(arr, fillintc(tokb, offset), tok);
       }
    else /* IDENTIFIERTOK */
       { TOKEN tokplus = makeop(PLUSOP);
         TOKEN tokmult = makeop(TIMESOP);
         if (arr->symentry->datatype->lowbound == 1)
            { offset = subs->link->symentry->size * -1;
              offset *= ((typesym->highbound - typesym->lowbound + 1) - (subs->link->intval));
            }
         else
            { offset = (subs->symtype->size - typesym->highbound) * typesym->size;
              offset *= -1;
              offset += (subs->link->intval - typesym->lowbound) * typesym->datatype->size;
            };
         binop(tokmult, subs, fillintc(tokb, typesym->size));
         binop(tokplus, tokmult, makeintc(offset));
         return makearef(arr, tokplus, tok);
       };
  }

/* dopoint handles a ^ operator.  john^ becomes (^ john) with type record
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok)
  { if (DEBUG & DB_DOPOINT)
       { printf("dopoint\n");
         dbugprinttok(var);
         dbugprinttok(tok);
       }
    if (var->whichval == AREFOP) return var;
    var->symtype->datatype = searchst(var->symtype->datatype->namestring);
    assert( var->symtype->kind == POINTERSYM );
    assert( var->symtype->datatype->kind == TYPESYM );
    tok->symtype = var->symtype->datatype->datatype;
    tok->operands = var;
    return tok;
  }

/* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok)
  { if (bounds->symtype->kind == ARRAYSYM)
       { assert (bounds->symtype->datatype->kind == SUBRANGE );
          SYMBOL sym = symalloc();
          sym->kind = ARRAYSYM;
          sym->datatype = bounds->symtype->datatype;
          SYMBOL rangesym = typetok->symtype;
          sym->size = (rangesym->highbound - rangesym->lowbound + 1)
                      * sym->datatype->size;
          sym->offset = bounds->symtype->size;
          bounds->symtype->size = (rangesym->highbound - rangesym->lowbound + 1)
                      * bounds->symtype->size;
          sym->lowbound = rangesym->lowbound;
          sym->highbound = rangesym->highbound;
          bounds->symtype->datatype = sym;
          return bounds;
       }
    assert( bounds->symtype->kind == SUBRANGE );
    SYMBOL sym = symalloc();
    sym->kind = ARRAYSYM;
    sym->datatype = typetok->symtype;
    SYMBOL rangesym = bounds->symtype;
    sym->size = (rangesym->highbound - rangesym->lowbound + 1)
                * typetok->symtype->size;
    sym->offset = typetok->symtype->size;
    sym->lowbound = rangesym->lowbound;
    sym->highbound = rangesym->highbound;
    typetok->symtype = sym;
    return typetok;
  }

void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

int main(void)          /*  */
  { int res;
    memset(labels, 0, sizeof(labels));
    initsyms();
    res = yyparse();
    printst();       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
  }
