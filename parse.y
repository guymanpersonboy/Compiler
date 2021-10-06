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
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"
#include "pprint.h"

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
lblock          : LABEL numlist SEMICOLON cblock
                | cblock
                ;
numlist         : NUMBER COMMA numlist
                | NUMBER
                ;
cblock          : CONST cdef_list tblock
                | tblock
                ;
cdef_list       : cdef SEMICOLON cdef_list
                | cdef SEMICOLON
                ;
cdef            : IDENTIFIER EQ constant
                ;
constant    /*  : sign? IDENTIFIER
                | sign? NUMBER  */
                : STRING  /* change : back to | later */
                ;
tblock          : TYPE tdef_list vblock
                | vblock
                ;
tdef_list       : tdef SEMICOLON tdef_list
                | tdef SEMICOLON
                ;
tdef            : IDENTIFIER EQ type
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
                | RECORD field_list END
                | POINT IDENTIFIER
                ;
simpletype      : IDENTIFIER                     { $$ = findtype($1); }
                | LPAREN idlist RPAREN
                | constant DOTDOT constant
                ; /* $1->symtype returns type */
simpletype_list : simpletype COMMA simpletype_list
                | simpletype
                ;
block           : BEGINBEGIN statement endpart
                      { $$ = makeprogn($1, cons($2, $3)); }
                ;
statement       : BEGINBEGIN statement endpart
                          { $$ = makeprogn($1,cons($2, $3)); }
                | IF expression THEN statement endif
                          { $$ = makeif($1, $2, $4, $5); }
                | variable ASSIGN expression /* assignment */
                          { $$ = binop($2, $1, $3); }
                | funcall
                | WHILE expression DO statement
                | REPEAT statement_list UNTIL expression
                | FOR IDENTIFIER ASSIGN expression TO expression DO statement
                          /* (int sign, tok, asg, tokb, endexpr, tokc, statement) */
                          { $$ = makefor(1, $2, $4, $5, $6, $7, $8);}
                | GOTO NUMBER
                | label
                ;
statement_list  : statement SEMICOLON statement_list
                | statement
                ;
label           : NUMBER COLON statement
                ;
endpart         : SEMICOLON statement endpart    { $$ = cons($2, $3); }
                | END                            { $$ = NULL; }
                ;
endif           : ELSE statement                 { $$ = $2; }
                | /* empty */                    { $$ = NULL; }
                ;
expression      : expression compare_op expr
                | expr
                ;
compare_op      : EQ | LT | GT| NE | GE | IN
                ;
expr            : /* sign? v also change to plus_op */ term
                | expr PLUS term                 { $$ = binop($2, $1, $3); }
                | /* sign? */ term
                ;
plus_op         : PLUS | MINUS | OR
                ;
term            : term TIMES factor              { $$ = binop($2, $1, $3); }
                | factor /* TODO change TIMES to times_op */
                ;
times_op        : TIMES | DIVIDE | DIV | MOD | AND
                ;
factor          : unsigned_constant
                | variable
                | funcall
                | LPAREN expression RPAREN          { $$ = $2; }
                | NUMBER
                | NOT factor
                ;
unsigned_constant : NUMBER | NIL | STRING
                ;
variable        : IDENTIFIER                     { $$ = findid($1); }
                | variable LBRACKET expr_list RBRACKET
                | variable DOT IDENTIFIER
                | variable POINT
                ;
funcall         : IDENTIFIER LPAREN expr_list RPAREN  { $$ = makefuncall($4, $1, $3); }
                ;
expr_list       : expression COMMA expr_list
                | expression
                ;
field_list      : fields SEMICOLON field_list
                | fields
                ;
fields          : idlist COLON type
                ;
idlist          : IDENTIFIER COMMA idlist        { $$ = cons($1, $3); }
                | IDENTIFIER                     { $$ = cons($1, NULL); }
                ;
sign            : PLUS | MINUS
                ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG          0           /* set bits here for debugging, 0 = off  */
#define DB_CONS        1           /* bit to trace cons */
#define DB_BINOP       1           /* bit to trace binop */
#define DB_MAKEIF      2           /* bit to trace makeif */
#define DB_MAKEPROGN   2           /* bit to trace makeprogn */
#define DB_MAKEPROGRAM 4           /* bit to trace makeprogram */
#define DB_MAKEFOR     4           /* bit to trace makefor */
#define DB_FINDID      8           /* bit to trace findid */
#define DB_FINDTYPE    8           /* bit to trace findtype */
#define DB_INSTVARS   16           /* bit to trace instvars */
#define DB_PARSERES   16           /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */

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

/* binop links a binary operator op to two operands, lhs and rhs. */
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
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
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
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
  {

  }

/* instlabel installs a user label into the label table */
void  instlabel (TOKEN num)
  {

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
  {

  }

/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
  {  tok->tokentype = OPERATOR;
     tok->whichval = FUNCALLOP;
     tok->operands = fn;
     fn->link = args;
     return tok;
  }

/* makeprogram makes the tree structures for the top-level program */
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements)
  {  TOKEN tokprogram = (TOKEN) talloc();
     tokprogram->tokentype = OPERATOR;
     tokprogram->whichval = PROGRAMOP;
     tokprogram->operands = name;
     TOKEN tokprogn = (TOKEN) talloc();
     name->link = makeprogn(tokprogn, args);
     tokprogn->link = statements;
     if (DEBUG & DB_MAKEPROGRAM)
        { printf("\nmakeprogram\n");
          dbugprinttok(tokprogram);
          dbugprinttok(name);
          dbugprinttok(tokprogn);
          dbugprinttok(args);
          dbugprinttok(statements);
        }
    return tokprogram;
  }

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement)
  {  TOKEN tokprogn = (TOKEN) talloc();
     if (sign > 0)
        { TOKEN tokas = makeop(ASSIGNOP);
          makeprogn(tokprogn, tokas);
          /* build the tokas binop as (:= i start) */
          binop(tokas, findid(tok), asg);
          TOKEN toklabel = makelabel();
          tokas->link = toklabel;
          /* tokb becomes if statement with goto */
          toklabel->link = tokb;
          TOKEN tokle = binop(makeop(LEOP), tok, endexpr);
          /* tokc becomes progn containing thenpart and i++ and goto */
          makeif(tokb, tokle, makeprogn(tokc, statement), NULL);
          statement->link = makeplus(tok, makeintc(1), makeop(PLUSOP));
          statement->link->link = makegoto(labelnumber - 1);
        } /* else
        { // TODO change sign in function call and implement downto
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
     return tokprogn;
  }

/* findid finds an identifier in the symbol table, sets up symbol table
   pointers, changes a constant to its number equivalent */
TOKEN findid(TOKEN tok) /* the ID token */
  {  SYMBOL sym = searchst(tok->stringval);
     tok->symentry = sym;
     SYMBOL typ = sym->datatype;
     tok->symtype = typ;
     if (typ->kind == BASICTYPE ||
            typ->kind == POINTERSYM)
        { tok->basicdt = typ->basicdt; };
     if (DEBUG & DB_FINDID)
        { printf("instvars\n");
          dbugprinttok(tok);
        };
     return tok;
  }

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok)
  {  SYMBOL sym = searchst(tok->stringval);
     tok->symtype = sym;
     if (DEBUG & DB_FINDTYPE)
        { printf("findtype\n");
          dbugprinttok(tok);
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

/* makeplus makes a + operator.
   tok (if not NULL) is a (now) unused token that is recycled. */
TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok)
  {  tok = (tok) ? tok : (TOKEN) talloc();
     tok->tokentype = OPERATOR;
     tok->whichval = PLUSOP;
     TOKEN tokas = makeop(ASSIGNOP);
     tokas->operands = lhs;
     lhs->link = tok;
     tok->operands = lhs;
     lhs->link = rhs;
     return tokas;
  }

void yyerror (char const *s)
{
  fprintf (stderr, "%s\n", s);
}

int main(void)          /*  */
  { int res;
    initsyms();
    res = yyparse();
    printst();       /* to shorten, change to:  printstlevel(1);  */
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
    /* uncomment following to call code generator. */
     /* 
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
      */
  }
