/* codgen.c       Generate Assembly Code for x86         07 May 18   */

/* Christopher Carrasco
   Fall 2021 */

/* Copyright (c) 2018 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include "token.h"
#include "symtab.h"
#include "lexan.h"
#include "genasm.h"
#include "codegen.h"
#include "pprint.h"

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0
/* used for op code instructions */
#define SD_OFFSET 9
#define Q_OFFSET 16
// TODO UNARYQ_OFFSET 15
// TODO JUMP_OFFSET 6 /* subtract jumpmap by this so size is only 6 (EQOP) */

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */

static bool regused[FMAX + 1];   /* registers in use */
static int regkind[RDI + 1];    /* in: kind of data. out: reg */
static int instmap[NOTOP + 1];   /* in: op number. out: op code inst */
static int jumpmap[GTOP + 1];    /* in: op number. out: op code jump */

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel)
  {  TOKEN name, code;
     name = pcode->operands;
     code = name->link->link;
     nextlabel = maxlabel + 1;
     stkframesize = asmentry(name->stringval,varsize);
     int i;
     for (i = 0; i < FMAX + 1; i++) { regused[i] = false; };
     regkind[WORD] = EAX;
     regkind[FLOAT] = XMM0;
     regkind[ADDR] = RAX;
     regkind[RDI] = EDI;

     instmap[PLUSOP] = ADDL;
     instmap[MINUSOP] = SUBL;
     instmap[TIMESOP] = IMULL;
     instmap[DIVIDEOP] = DIVL;
     instmap[ANDOP] = ANDL;
     instmap[OROP] = ORL;
     instmap[NOTOP] = NOTQ; // TODO: add NOTL 11 to genasm.h?

     jumpmap[EQOP] = JE;
     jumpmap[NEOP] = JNE;
     jumpmap[LTOP] = JL;
     jumpmap[LEOP] = JLE;
     jumpmap[GEOP] = JGE;
     jumpmap[GTOP] = JG;
     genc(code);
     asmexit(name->stringval);
  }

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  { int num, reg = -1;
    if (DEBUGGEN)
       { printf("genarith\n");
	       dbugprinttok(code);
        //  if (code->operands) dbugprinttok(code->operands);
        //  if (code->operands->link) dbugbprinttok(code->operands->link);
       };
    switch ( code->tokentype )
      { case NUMBERTOK:
          switch (code->basicdt)
            { case INTEGER:
                num = code->intval;
                reg = getreg(WORD);
                if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE )
                  asmimmed(MOVL, num, reg);
                break;
              case REAL:
                reg = getreg(FLOAT);
                makeflit(code->realval, nextlabel);
                asmldflit(MOVSD, nextlabel++, reg);
                break;
            }
          break;
        case IDENTIFIERTOK:
          switch (code->basicdt)
            { case REAL:
                reg = getreg(FLOAT);
                break;
              case POINTER:
                reg = getreg(ADDR);
                break;
            }
          break;
        case OPERATOR:
          switch (code->basicdt)
            { case INTEGER:
                reg = getreg(WORD);
                if (code->whichval == FUNCALLOP)
                   { if (strncmp(code->operands->stringval, "new", 16) == 0)
                     { asmimmed(MOVL, code->operands->link->intval, reg);
                     }
                     else if (strncmp(code->operands->stringval, "iround", 16) == 0)
                     { unused(reg);
                       reg = getreg(FLOAT);
                     };
                   };
                break;
              case REAL:
                reg = getreg(FLOAT);
                break;
            }
          break;
      };
    return reg;
  }

// TODO replace all literal RBP with asmld/asmst ?
/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  { TOKEN tok, lhs, rhs, expr;
    int reg, offs;
    SYMBOL sym;
    if (DEBUGGEN)
       { printf("genc\n");
         dbugprinttok(code);
       };
    if ( code->tokentype != OPERATOR )
       { printf("Bad code token");
         dbugprinttok(code);
       };
    switch ( code->whichval )
      { case PROGNOP:
          tok = code->operands;
          while ( tok != NULL )
            { genc(tok);
              tok = tok->link;
            };
          break;

        case ASSIGNOP:
          lhs = code->operands;
          rhs = lhs->link;
          reg = genarith(rhs);              /* generate rhs into a register */
          if (lhs->symentry)
             { sym = lhs->symentry;
               offs = sym->offset - stkframesize; /* net offset of the var   */
             }
          else if (lhs->operands && lhs->operands->symentry)
             { sym = lhs->operands->symentry;
               offs = sym->offset - stkframesize;
             }
          // TODO lsh->symentry already exists for test24?
          // TODO just pust this code where needed?
          // if (rhs->operands && rhs->operands->symentry)
          //    { sym = rhs->operands->symentry;
          //      offs = sym->offset - stkframesize;
          //    }
          switch (code->basicdt)            /* store value into lhs  */
            { case INTEGER:
                if (rhs->tokentype == OPERATOR)
                   { if (rhs->operands->link) /* binop rhs */
                        { TOKEN rhsrhs = rhs->operands->link;
                          int reg1 = getreg(WORD);
                          if (rhs->whichval == FUNCALLOP)
                             { offs = rhsrhs->symentry->offset - stkframesize;
                               asmldr(MOVSD, offs, RBP, reg, rhsrhs->stringval);
                               asmcall(rhs->operands->stringval);
                               asmstr(MOVL, reg1, offs + FLOATSIZE, RBP, lhs->stringval);
                               break;
                             };
                          reg1 = (reg == reg1) ? reg+1 : reg1;
                          if (rhs->whichval == AREFOP)
                             { sym = rhs->operands->operands->symentry;
                               int offs1 = sym->offset - stkframesize;
                               // TODO: call moveop on john is a pointer
                               asmld(MOVQ, offs1, reg, sym->namestring);
                               // TODO maybe bring outside of else-if along with the lhs version
                               if (rhs->whichval == AREFOP && rhs->operands && rhs->operands->whichval == POINTEROP)
                                  { strncpy(rhs->operands->stringval, "^.", 16);
                                  };
                               asmldr(MOVL, rhs->operands->link->intval, reg, reg1, rhs->operands->stringval);
                               asmst(MOVL, reg1, offs, lhs->stringval);
                               break;
                             };
                          asmldr(MOVL, offs, RBP, reg, rhs->operands->stringval);
                          if (rhsrhs->tokentype == NUMBERTOK)
                            { asmimmed(MOVL, rhsrhs->intval, reg1);
                            }
                          else /* IDENTIFIERTOK */
                            { asmldr(MOVL, offs + WORDSIZE, RBP, reg1, rhsrhs->stringval);
                            };
                          /* op code instructions */
                          asmrr(instmap[rhs->whichval], reg1, reg);
                        }
                     else /* unaryop */
                        { printf("TODO: INTEGER unaryop");
                        };
                   }
                else if (lhs->whichval == AREFOP && rhs->tokentype == NUMBERTOK)
                   { int reg1 = getreg(WORD);
                     offs = lhs->operands->link->intval;
                     sym = lhs->operands->operands->symentry;
                     int offs1 = sym->offset - stkframesize;
                     // TODO call moveop on test25 john is pointer uses movq
                     asmld(MOVQ, offs1, reg1, sym->namestring);
                     // TODO maybe bring outside of else-if
                     if (lhs->whichval == AREFOP && lhs->operands && lhs->operands->whichval == POINTEROP)
                        { strncpy(lhs->operands->stringval, "^.", 16);
                        };
                     asmstr(MOVL, reg, offs, reg1, lhs->operands->stringval);
                     break;
                   }
                asmst(MOVL, reg, offs, lhs->stringval);
                break;
              case REAL:
                if (rhs->tokentype == OPERATOR)
                   { if (rhs->operands->link) /* binop rhs */
                        { TOKEN rhsrhs = rhs->operands->link;
                          if (rhs->whichval == FUNCALLOP)
                             { offs = rhsrhs->symentry->offset - stkframesize;
                               asmldr(MOVSD, offs, RBP, reg, rhsrhs->stringval);
                               asmcall(rhs->operands->stringval);
                               asmstr(MOVSD, reg, offs + FLOATSIZE, RBP, lhs->stringval);
                               break;
                             };
                          if (funcallin(rhs->operands)) /* binop rhs lhs is funcall */
                             { TOKEN rhslhs = rhs->operands;
                               unused(reg);
                               reg = genarith(rhslhs);
                               offs = rhslhs->operands->link->symentry->offset - stkframesize;
                               // TODO call moveop to find correct MOV for rhslhs?
                               asmldr(MOVSD, offs, RBP, reg, rhslhs->operands->link->stringval);
                               asmcall(rhslhs->operands->stringval);
                               /* assume rhsrhs is a funcall */
                               asmsttemp(reg);
                               unused(reg);
                             };
                          if (funcallin(rhsrhs)) /* binop rhs rhs is funcall */
                             { reg = genarith(rhsrhs);
                               offs = rhsrhs->operands->link->symentry->offset - stkframesize;
                               // TODO call moveop to find correct MOV for rhsrhs?
                               asmldr(MOVSD, offs, RBP, reg, rhsrhs->operands->link->stringval);
                               asmcall(rhsrhs->operands->stringval);
                               int reg1 = genarith(rhs);
                               /* assume rhslhs was a funcall */
                               // TODO call moveop to find correct MOV for rhs?
                               asmldtemp(reg1);
                               /* finish rhs funcall binop */
                               asmrr(instmap[rhs->whichval] + SD_OFFSET, reg, reg1);
                               asmstr(MOVSD, reg1, offs + FLOATSIZE, RBP, lhs->stringval);
                               break;
                             };
                          if (rhs->whichval == AREFOP) /* aref rhs */
                             { reg = genaref(code, -1);
                               int reg1 = genarith(lhs);
                               sym = rhs->operands->symentry;
                               int offs1 = sym->offset - stkframesize;
                               // TODO call moveop to find correct MOV?
                               asmldrr(MOVSD, offs1, reg, reg1, rhs->operands->stringval);
                               asmst(MOVSD, reg1, offs, lhs->stringval);
                               break;
                             };
                          makeflit(rhsrhs->realval, nextlabel);
                          asmldr(MOVSD, offs, RBP, reg, rhs->operands->stringval);
                          int reg1 = getreg(FLOAT);
                          asmldflit(MOVSD, nextlabel++, reg1);
                          asmrr(instmap[rhs->whichval] + SD_OFFSET, reg1, reg);
                        }
                     else /* unaryop */
                        { asmldr(MOVSD, offs + FLOATSIZE, RBP, reg, rhs->operands->stringval);
                          int reg1 = getreg(FLOAT);
                          asmfneg(reg, reg1);
                          asmstr(MOVSD, reg, offs, RBP, lhs->stringval);
                          break;
                        };
                   }
                else if (rhs->tokentype == IDENTIFIERTOK)
                   { asmldr(MOVL, offs + FLOATSIZE, RBP, EAX, rhs->symentry->namestring);
                     asmfloat(EAX, reg);
                   }
                else if (rhs->tokentype == NUMBERTOK)
                   { if (lhs->tokentype == OPERATOR && lhs->whichval == AREFOP)
                        { if (genaref(code, reg) == -1) /* rhs is a REAL */
                             { offs = lhs->operands->operands->symentry->offset - stkframesize;
                               asmld(MOVQ, offs, getreg(RAX), lhs->operands->operands->symentry->namestring);
                               
                               break;
                             };
                          asmstrr(MOVSD, reg, offs, RAX, lhs->operands->stringval);
                          break;
                        };
                   };
                asmstr(MOVSD, reg, offs, RBP, lhs->stringval);
                break;
              case POINTER:
                if (funcallin(code))
                   { asmrr(MOVL, reg, getreg(RDI));
                     asmcall(rhs->operands->stringval);
                     asmstr(MOVQ, reg, offs, RBP, sym->namestring);
                     break;
                   };
                // TODO offs + FLOATSIZE?
                asmldr(MOVQ, offs + FLOATSIZE, RBP, reg, rhs->stringval);
                asmstr(MOVQ, reg, offs, RBP, lhs->stringval);
                break;
            };
          break;

        case FUNCALLOP:
          lhs = code->operands;
          rhs = lhs->link;
          int regd;
          switch ( rhs->tokentype )
            { case IDENTIFIERTOK:
                reg = getreg(WORD);
                regd = getreg(RDI);
                offs = rhs->symentry->offset - stkframesize; /* net offset of the var   */
                asmldr(MOVL, offs, RBP, reg, rhs->stringval);
                asmrr(MOVL, reg, regd);
                asmcall(lhs->stringval);
                break;
              case STRINGTOK:
                asmlitarg(nextlabel, getreg(RDI));
                asmcall(lhs->stringval);
                makeblit(rhs->stringval, nextlabel++);
                break;
            };
          break;

        case GOTOOP:
          /*     ***** fix this *****   */
          break;

        case LABELOP:
          asmlabel(code->operands->intval);
          clearreg();
          break;

        case IFOP:
          expr = code->operands;
          lhs = expr->operands;
          rhs = lhs->link;
          sym = lhs->symentry;              /* assumes lhs is a simple var  */
          offs = sym->offset - stkframesize; /* net offset of the var   */
          TOKEN statement = expr->link;     /* while loop statement */
          TOKEN tokgoto;
          int reg1;
          switch ( code->basicdt )
            { case BOOLETYPE: /* either for-loop or repeat statement */
                /* for loop if section */
                reg = getreg(WORD);
                reg1 = getreg(WORD);
                bool same = reg == reg1;
                reg1 = (same) ? reg+1 : reg1;
                asmldr(MOVL, offs, RBP, reg, lhs->stringval);
                asmimmed(MOVL, rhs->intval, reg1);
                asmrr(CMPL, reg1, reg);
                asmjump(jumpmap[expr->whichval], nextlabel++);
                if (same) /* repeat statement */
                   { asmjump(JMP, code->operands->link->link->operands->intval);
                     asmjump(JMP, nextlabel);
                     /* end repeat */
                     asmlabel(nextlabel - 1);
                     asmlabel(nextlabel);
                     break;
                   }
                asmjump(JMP, nextlabel);
                /* statement section */
                tokgoto = statement->operands->link->link;
                asmlabel(nextlabel - 1);
                genc(statement);
                asmjump(JMP, tokgoto->operands->intval);
                /* endfor */
                asmlabel(nextlabel);
                break;
              case INTEGER: /* while-loop not set as BOOLETYPE */
              case REAL:    /* assumes while-loop always uses MOVQ */
              case POINTER:
                /* while-loop if section */
                reg = genarith(statement->operands->operands->link); /* generate statement rhs into a register */
                reg1 = getreg(WORD); /* assumes the statement deals with INTEGER only */
                asmldr(MOVQ, offs, RBP, reg, expr->operands->stringval);
                asmimmed(MOVQ, rhs->intval, reg1);
                asmrr(CMPQ, reg1, reg);
                asmjump(jumpmap[expr->whichval], nextlabel++);
                asmjump(JMP, nextlabel);
                /* statement section */
                tokgoto = statement->operands->link;
                asmlabel(nextlabel - 1);
                genc(statement);
                asmjump(JMP, tokgoto->operands->intval);
                /* endwhile */
                asmlabel(nextlabel);
                break;
            };
          break;
	    };
  }

/* Clear register used tables to mark all registers free.  */
void clearreg()
  { int i;
    for (i = 0; i < FMAX; i++)
      { regused[i] = false; };
  }

/* Mark a register unused */
void unused(int reg)
  {
    regused[reg] = false;
  }

/* Mark a register used */
void used(int reg)
  {
    regused[reg] = true;
  }

/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind)
  { int reg = regkind[kind];
    if (regused[reg])
       { reg++;
       };
    if (regused[reg])
       { reg--;
       };
    used(reg);
    return reg;
  }

/* Make a register non-volatile by moving it if necessary.
   Result is the (possibly new) register number.   */
int nonvolatile(int reg)
  {
    return reg;
  }

/* Save caller-saves floating point registers on stack if in use */
void savereg()
  {

  }

/* Restore caller-saves floating point registers from stack if in use */
void restorereg()
  {

  }

/* test if there is a function call within code: 1 if true, else 0 */
int funcallin(TOKEN code)
  { if (code->tokentype != OPERATOR) return false;
    if (code->whichval == FUNCALLOP)
       { return true;
       };
    if (code->operands->link && code->operands->link->whichval == FUNCALLOP)
       { return true;
       };
    return false;
  }

/* find the op number that is equivalent to named function, if any */
int findfunop(char str[])
  {
    return -1;
  }

/* Generate code for a function call */
int genfun(TOKEN code)
  {
    return -1;
  }

/* find the correct MOV op depending on type of code */
int moveop(TOKEN code)
  {
    return -1;
  }

/* Generate code for array references and pointers */
/* In Pascal, a (^ ...) can only occur as first argument of an aref. */
/* If storereg < 0, generates a load and returns register number;
   else, generates a store from storereg. */
int genaref(TOKEN code, int storereg)
  { if (DEBUGGEN)
       { printf("genaref\n");
         dbugbprinttok(code);
         printf("  storereg %d\n", storereg);
       }
    if (storereg < 0)
       { TOKEN rhsrhs = code->operands->link->operands->link;
         storereg = genarith(rhsrhs);
         asmop(CLTQ);
         return storereg;
       }
    TOKEN lhsrhs = code->operands->operands->link;
    if (// TODO: code->operands->link->basicdt == INTEGER
        || code->operands->operands->tokentype == IDENTIFIERTOK)
       { genarith(lhsrhs);
         asmop(CLTQ);
       }
    else
      { return -1;
      };
    return storereg;
  }
