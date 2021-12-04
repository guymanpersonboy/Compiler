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
/* TODO UNARYQ_OFFSET 15 */

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */

bool regused[FMAX + 1];   /* registers in use */
static int regkind[ADDR + 1];    /* in: kind of data. out: reg */
static int instmap[NOTOP + 1];   /* in: op number. out: op code */
static int lclabel = 1;          /* track the .LC# labels */

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
     instmap[PLUSOP] = ADDL;
     instmap[MINUSOP] = SUBL;
     instmap[TIMESOP] = IMULL;
     instmap[DIVIDEOP] = DIVL;
     instmap[ANDOP] = ANDL;
     instmap[OROP] = ORL;
     instmap[NOTOP] = NOTQ; /* TODO add NOTL 11 to genasm.h? */
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
                makeflit(code->realval, lclabel);
                asmldflit(MOVSD, lclabel++, reg);
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
                break;
              case REAL:
                reg = getreg(FLOAT);
                break;
            }
          break;
      };
    return reg;
  }


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
  { TOKEN tok, lhs, rhs;
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
        case ASSIGNOP:                   /* Trivial version: handles I := e */
          lhs = code->operands;
          rhs = lhs->link;
          reg = genarith(rhs);              /* generate rhs into a register */
          sym = lhs->symentry;              /* assumes lhs is a simple var  */
          offs = sym->offset - stkframesize; /* net offset of the var   */
          switch (code->basicdt)            /* store value into lhs  */
            { case INTEGER:
                if (rhs->tokentype == OPERATOR)
                   { asmldr(MOVL, offs, RBP, reg, rhs->operands->stringval);
                     asmimmed(MOVL, rhs->operands->link->intval, ECX);
                     asmrr(instmap[rhs->whichval], ECX, reg);
                   }
                asmst(MOVL, reg, offs, lhs->stringval);
                break;
              case REAL:
                if (rhs->tokentype == IDENTIFIERTOK)
                   { asmldr(MOVL, offs + FLOATSIZE, RBP, EAX, rhs->symentry->namestring);
                     asmfloat(EAX, reg);
                   }
                if (rhs->tokentype == OPERATOR)
                   { makeflit(rhs->operands->link->realval, lclabel);
                     asmldr(MOVSD, offs, RBP, reg, rhs->operands->stringval);
                     int reg1 = getreg(FLOAT);
                     asmldflit(MOVSD, lclabel++, reg1);
                     asmrr(instmap[rhs->whichval] + SD_OFFSET, reg1, reg);
                   }
                asmstr(MOVSD, reg, offs, RBP, lhs->stringval);
                break;
              case POINTER:
                /* TODO offs + FLOATSIZE? */
                asmldr(MOVQ, offs + FLOATSIZE, RBP, reg, rhs->stringval);
                asmstr(MOVQ, reg, offs, RBP, lhs->stringval);
                break;
            };
          break;
        case FUNCALLOP:
          /*     ***** fix this *****   */
          break;
        case GOTOOP:
          /*     ***** fix this *****   */
          break;
        case LABELOP:
          /*     ***** fix this *****   */
          break;
        case IFOP:
          /*     ***** fix this *****   */
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
  {
    int reg = regkind[kind];
    if (regused[reg])
       { reg++;
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
  {
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
  {
    return -1;
  }
