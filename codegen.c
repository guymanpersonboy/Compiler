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

static bool regused[FMAX + 1];  /* registers in use */
static int regkind[RDI + 1];    /* in: kind of data. out: reg */
static int instmap[NOTOP + 1];  /* in: op number. out: op code inst */
static int jumpmap[GTOP + 1];   /* in: op number. out: op code jump */
static int movemap[POINTER + 1];   /* for use in moveop() */

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

     movemap[INTEGER] = MOVL;
     movemap[REAL] = MOVQ;
     movemap[POINTER] = MOVSD;
     genc(code);
     asmexit(name->stringval);
  }

/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
  { int num, reg = -1;
    int dt = code->basicdt;
    if (DEBUGGEN)
       { printf("genarith\n");
	       dbugprinttok(code);
        //  if (code->operands) dbugprinttok(code->operands);
        //  if (code->operands->link) dbugbprinttok(code->operands->link);
       };
    switch ( code->tokentype )
      { case NUMBERTOK:
          if (dt == INTEGER)
             { num = code->intval;
               reg = getreg(WORD);
               if ( num >= MINIMMEDIATE && num <= MAXIMMEDIATE )
                  asmimmed(MOVL, num, reg);
             };
          if (dt == REAL)
             { reg = getreg(FLOAT);
               makeflit(code->realval, nextlabel);
               asmldflit(MOVSD, nextlabel++, reg);
             };
          break;
        case IDENTIFIERTOK:
          if (dt == REAL)
             reg = getreg(FLOAT);
          if (dt == POINTER)
             reg = getreg(ADDR);
          break;
        case OPERATOR:
          if (dt == INTEGER)
             { reg = getreg(WORD);
               if (code->whichval == FUNCALLOP)
                  { if (strncmp(code->operands->stringval, "new", 16) == 0)
                       { asmimmed(MOVL, code->operands->link->intval, reg);
                         break;
                       };
                    if (strncmp(code->operands->stringval, "iround", 16) == 0)
                       { unused(reg);
                         reg = getreg(FLOAT);
                       };
                  };
             };
          if (dt == REAL)
             reg = getreg(FLOAT);
          break;
      };
    return reg;
  }

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
             };
          switch (code->basicdt)            /* store value into lhs  */
            { case INTEGER:
                if (rhs->tokentype == OPERATOR)
                   { if (rhs->operands->link) /* binop rhs */
                        { TOKEN rhsrhs = rhs->operands->link;
                          int reg1 = getreg(WORD);
                          if (rhs->whichval == FUNCALLOP)
                             { int offs1 = rhsrhs->symentry->offset - stkframesize;
                               asmld(MOVSD, offs1, reg, rhsrhs->stringval);
                               asmcall(rhs->operands->stringval);
                               asmst(MOVL, reg1, offs, lhs->stringval);
                               break;
                             };
                          reg1 = (reg == reg1) ? reg+1 : reg1;
                          if (rhs->whichval == AREFOP)
                             { sym = rhs->operands->operands->symentry;
                               int offs1 = sym->offset - stkframesize;
                               // TODO: call moveop on john is a pointer
                               asmld(MOVQ, offs1, reg, sym->namestring);
                               asmldr(MOVL, rhs->operands->link->intval, reg, reg1, "^.");
                               asmst(MOVL, reg1, offs, lhs->stringval);
                               break;
                             };
                          asmld(MOVL, offs, reg, rhs->operands->stringval);
                          if (rhsrhs->tokentype == NUMBERTOK)
                            { asmimmed(MOVL, rhsrhs->intval, reg1);
                            }
                          else /* IDENTIFIERTOK */
                            { asmld(MOVL, offs + WORDSIZE, reg1, rhsrhs->stringval);
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
                             { int offs1 = rhsrhs->symentry->offset - stkframesize;
                               asmld(MOVSD, offs1, reg, rhsrhs->stringval);
                               asmcall(rhs->operands->stringval);
                               asmst(MOVSD, reg, offs, lhs->stringval);
                               break;
                             };
                          if (funcallin(rhs->operands)) /* binop rhs lhs is funcall */
                             { TOKEN rhslhs = rhs->operands;
                               unused(reg);
                               reg = genarith(rhslhs);
                               offs = rhslhs->operands->link->symentry->offset - stkframesize;
                               // TODO call moveop to find correct MOV for rhslhs?
                               asmld(MOVSD, offs, reg, rhslhs->operands->link->stringval);
                               asmcall(rhslhs->operands->stringval);
                               /* assume rhsrhs is a funcall */
                               asmsttemp(reg);
                               unused(reg);
                             };
                          if (funcallin(rhsrhs)) /* binop rhs rhs is funcall */
                             { reg = genarith(rhsrhs);
                               offs = rhsrhs->operands->link->symentry->offset - stkframesize;
                               // TODO call moveop to find correct MOV for rhsrhs?
                               asmld(MOVSD, offs, reg, rhsrhs->operands->link->stringval);
                               asmcall(rhsrhs->operands->stringval);
                               int reg1 = genarith(rhs);
                               /* assume rhslhs was a funcall */
                               asmldtemp(reg1);
                               /* finish rhs funcall binop */
                               asmrr(instmap[rhs->whichval] + SD_OFFSET, reg, reg1);
                               offs = sym->offset - stkframesize;
                               // TODO call moveop to find correct MOV for rhs?
                               asmst(MOVSD, reg1, offs, lhs->stringval);
                               break;
                             };
                          if (rhs->whichval == AREFOP) /* aref rhs */
                             { sym = rhs->operands->symentry;
                               if (sym)
                                  { reg = genaref(code, -1);
                                    int reg1 = genarith(lhs);
                                    int offs1 = sym->offset - stkframesize;
                                    // TODO call moveop to find correct MOV?
                                    asmldrr(MOVSD, offs1, reg, reg1, rhs->operands->stringval);
                                    asmst(MOVSD, reg1, offs, lhs->stringval);
                                    break;
                                  };
                               /* test 28 */
                               int reg1 = getreg(WORD);
                               int reg2 = getreg(WORD);
                               rhs = rhs->operands->operands;
                               int offs1 = rhs->symentry->offset - stkframesize;
                               // TODO: call moveop
                               asmld(MOVQ, offs1, reg1, rhs->stringval);
                               asmldr(MOVQ, rhs->operands->intval, reg1, reg2, "^.");
                               asmldr(MOVSD, rhsrhs->intval, reg2, reg, "^.");
                               asmst(MOVSD, reg, offs, lhs->stringval);
                               break;
                             };
                          makeflit(rhsrhs->realval, nextlabel);
                          asmld(MOVSD, offs, reg, rhs->operands->stringval);
                          int reg1 = getreg(FLOAT);
                          asmldflit(MOVSD, nextlabel++, reg1);
                          asmrr(instmap[rhs->whichval] + SD_OFFSET, reg1, reg);
                        }
                     else /* unaryop */
                        { int offs1 = rhs->operands->symentry->offset - stkframesize;
                          asmld(MOVSD, offs1, reg, rhs->operands->stringval);
                          int reg1 = getreg(FLOAT);
                          asmfneg(reg, reg1);
                          asmst(MOVSD, reg, offs, lhs->stringval);
                          break;
                        };
                   }
                else if (rhs->tokentype == IDENTIFIERTOK)
                   { int offs1 = rhs->symentry->offset - stkframesize;
                     asmld(MOVL, offs1, EAX, rhs->symentry->namestring);
                     asmfloat(EAX, reg);
                   }
                else if (rhs->tokentype == NUMBERTOK)
                   { if (lhs->tokentype == OPERATOR && lhs->whichval == AREFOP)
                        { reg = genaref(code, reg);
                          if (code->operands->operands->tokentype != IDENTIFIERTOK)
                             { rhs = lhs->operands->operands;
                               offs = rhs->symentry->offset - stkframesize;
                               int reg1 = getreg(WORD);
                               asmld(MOVQ, offs, reg1, rhs->stringval);
                               /* secret NUMBERTOK */
                               int offs1 = rhs->operands->intval;
                               int reg2 = getreg(WORD);
                               asmldr(MOVQ, offs1, reg1, reg2, "^.");
                               asmstr(MOVSD, reg, lhs->operands->link->intval, reg2, "^.");
                               break;
                             };
                          asmstrr(MOVSD, reg, offs, RAX, lhs->operands->stringval);
                          break;
                        };
                   };
                asmst(MOVSD, reg, offs, lhs->stringval);
                break;
              case POINTER:
                if (funcallin(code))
                   { asmrr(MOVL, reg, getreg(RDI));
                     asmcall(rhs->operands->stringval);
                     asmst(MOVQ, reg, offs, sym->namestring);
                     break;
                   };
                int offs1 = rhs->symentry->offset - stkframesize;
                asmld(MOVQ, offs1, reg, rhs->stringval);
                asmst(MOVQ, reg, offs, lhs->stringval);
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
                asmld(MOVL, offs, reg, rhs->stringval);
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
          asmjump(JMP, code->operands->intval);
          asmlabel(nextlabel);
          break;

        case LABELOP:
          asmlabel(code->operands->intval);
          break;

        case IFOP:
          expr = code->operands;
          lhs = expr->operands;
          rhs = lhs->link;
          sym = lhs->symentry;              /* assumes lhs is a simple var  */
          offs = sym->offset - stkframesize; /* net offset of the var   */
          TOKEN statement = expr->link;     /* while loop statement */
          int reg1;
          switch ( code->basicdt )
            { case BOOLETYPE: /* either for-loop or repeat statement */
                /* for loop if section */
                reg = getreg(WORD);
                reg1 = getreg(WORD);
                asmld(MOVL, offs, reg, lhs->stringval);
                asmimmed(MOVL, rhs->intval, reg1);
                asmrr(CMPL, reg1, reg);
                asmjump(jumpmap[expr->whichval], nextlabel++);
                TOKEN tokrep = expr->link->link;
                if (tokrep && tokrep->operands) /* repeat statement */
                   { asmjump(JMP, tokrep->operands->intval);
                     asmjump(JMP, nextlabel);
                     /* end repeat */
                     asmlabel(nextlabel - 1);
                     asmlabel(nextlabel);
                     break;
                   }
                asmjump(JMP, nextlabel);
                /* statement and goto section */
                asmlabel(nextlabel - 1);
                genc(statement);
                break;
              case INTEGER: /* while-loop not set as BOOLETYPE */
              case REAL:    /* assumes while-loop always uses MOVQ */
              case POINTER:
                /* while-loop if section */
                reg = genarith(statement->operands->operands->link); /* generate statement rhs into a register */
                reg1 = getreg(WORD); /* assumes the statement deals with INTEGER only */
                asmld(MOVQ, offs, reg, expr->operands->stringval);
                asmimmed(MOVQ, rhs->intval, reg1);
                asmrr(CMPQ, reg1, reg);
                asmjump(jumpmap[expr->whichval], nextlabel++);
                asmjump(JMP, nextlabel);
                /* statement and goto section */
                asmlabel(nextlabel - 1);
                genc(statement);
                break;
            };
          break;
	    };

    clearreg();
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
    regused[reg] = true;
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
  { return movemap[code->basicdt];
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
       };
    if (storereg < 0)
       { TOKEN rhsrhs = code->operands->link->operands->link;
         storereg = genarith(rhsrhs);
         asmop(CLTQ);
         return storereg;
       };
    TOKEN lhsrhs = code->operands->operands->link;
    if (code->operands->operands && code->operands->operands->tokentype == IDENTIFIERTOK)
       { genarith(lhsrhs);
         asmop(CLTQ);
       };
    return storereg;
  }
