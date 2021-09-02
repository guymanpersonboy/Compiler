/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2018 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "lexan.h"

/* This file will work as given with an input file consisting only
   of integers separated by blanks:
   make lex1
   lex1
   12345 123    345  357
   */

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks () {
    int c;
    // skips blanks and whitespace
    while ((c = peekchar()) != EOF && (c == ' ' || c == '\n' || c == '\t')) {
        getchar();
    }
    // skips comments
    if (c == '{' ) {
        // { and } comments
        while ((c = peekchar()) != EOF && c != '}') {
            getchar();
        }
        getchar();
        // TODO call skipblanks again fi more whitespace?
    }
    if (peekchar() == '(' && peek2char() == '*') {
        // (* and *) comments
        while ((c = peekchar()) != EOF && (c != '*' && peek2char() != ')')) {
            getchar();
        }
        getchar();
        getchar();
        // TODO call skipblanks again fi more whitespace?
    }
}

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok) {
    int c;
    char str[16];
    while ((c = peekchar()) != EOF && CHARCLASS[c] == ALPHA) {
        break;
    }
    // TODO determine if an identifier or reserved
    // if (tok == identifier) {}
    tok->tokentype = IDENTIFIERTOK;
    strcpy(tok->stringval, str);
    // else {}
    tok->tokentype = RESERVED;
    // TODO there are some #define in token.h for these, use?
    tok->whichval = 1.29;

    return tok;
}

/* Get strings */
TOKEN getstring (TOKEN tok) {    
    if (peekchar() == '\'') {
        getchar();
        int c, i;

        // copy each char between ' and '
        char str[16];
        for (i = 0; i < 15; i++) {
            // read until the final ' 
            if ((c = peekchar()) != '\'') {
                str[i] = getchar();
            } else if (c == '\'' && peek2char() == '\'') {
                // '' to include a ' in lisp
                str[i] = getchar();
                getchar();
            } else {
                // peekchar() == ' and peek2char != ' so i++ for \0 and break
                getchar();
                i++;
                break;
            }
        }
        str[i] = '\0';
        strcpy(tok->stringval, str);
    }
    tok->tokentype = STRINGTOK;

    return tok;
}

/* //??? Get Operators and Delimiters */
TOKEN special (TOKEN tok) {
    return tok;
}

/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok) {
    long num;
    int  c, charval;
    num = 0;
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();
        charval = (c - '0');
        num = num * 10 + charval;
    }
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = num;
    return (tok);
}

