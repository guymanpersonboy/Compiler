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

static const char *reserved[ ] = {
    "array", "begin", "case", "const", "do",
    "downto", "else", "end", "file", "for",
    "function", "goto", "if", "label", "nil",
    "of", "packed", "procedure", "program",
    "record", "repeat", "set", "then", "to",
    "type", "until", "var", "while", "with",
    "and", "or", "not", "div", "mod", "in"
};
static const char *delimiters[] = {
    ",", ";", ":", "(", ")", "[", "]", ".."
};
static const char *operators[] = {
    "+", "-", "*", "/", ":=", "=", "<>", "<",
    "<=", ">=", ">", "^", "."
};

/* Skip blanks, whitespace, and comments */
void skipblanks () {
    int c;
    // skips blanks and whitespace
    while ((c = peekchar()) != EOF && (c == ' ' || c == '\n' || c == '\t')) {
        getchar();
    }
    if (c == '{') {
        getchar();
        // skips { } comments
        while ((c = peekchar()) != EOF && c != '}') {
            getchar();
        }
        getchar();
        skipblanks();
    }
    // TODO FIX
    if (peekchar() == '(' && peek2char() == '*') {
        // skips (* *) comments
        while ((c = peekchar()) != EOF && (c != '*' && peek2char() != ')')) {
            getchar();
        }
        getchar();
        getchar();
        skipblanks();
    }
}

/* Get identifiers and reserved words */
TOKEN identifier (TOKEN tok) {
    const int NUM_RESERVED = 35;
    int c;
    char str[16];

    // assume only the first 15 chars are significant
    for (int i = 0; i < 15; i++) {
        // read until non alpha-numeric char
        if ((c = peekchar()) != EOF &&
                (CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC)) {
            str[i] = getchar();
        } else {
            str[i] = '\0';
            break;
        }
    }
    // determine if a reserved word
    for (int word = 0; word < NUM_RESERVED; word++) {
        if (strcmp(str, reserved[word]) == 0) {
            // determine if an operator reserved word
            const int LOOKUP_BIAS = 245;
            // 29 <= word <= 34
            if (AND - LOOKUP_BIAS <= word && word <= IN - LOOKUP_BIAS) {
                const int OP_BIAS = 15;
                tok->tokentype = OPERATOR;
                // whichval AND to IN is 29 - 15 and 34 - 15
                tok->whichval = word - OP_BIAS;

                return tok;
            }
            // else a reserved word
            tok->tokentype = RESERVED;
            tok->whichval = word + 1;

            return tok;
        }
    }
    // we now know its an identifier
    tok->tokentype = IDENTIFIERTOK;
    strcpy(tok->stringval, str);

    return tok;
}

/* Get strings */
TOKEN getstring (TOKEN tok) {    
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
            // peekchar() == ' and peek2char != '
            getchar();
            break;
        }
    }
    str[i] = '\0';
    strcpy(tok->stringval, str);
    tok->tokentype = STRINGTOK;

    return tok;
}

/* // Get Operators and Delimiters */
TOKEN special (TOKEN tok) {
    const int NUM_DELIMITERS = 8;
    const int NUM_OPERATORS = 19;
    // TODO FIX OPERATORS AND DELIMITERS (THE PROBLEM MIGHT BE HERE WITH \0 OR THE TABLES)
    const int c = (peek2char() == ' ') ? '\0' : peek2char();
    char next_chars[2] = {peekchar(), c};
    int i;

    // determine if an delimiter or operator
    for (i = 0; i < NUM_DELIMITERS; i++) {
        if (next_chars == delimiters[i]) {
            // a delimiter
            if (strcmp(next_chars, "..") == 0) {
                getchar;
            }
            getchar();
            tok->tokentype = DELIMITER;
            tok->whichval = i + 1;

            return (tok);
        }
    }
    // we check for an operator
    for (i = 0; i < NUM_OPERATORS; i++) {
        // check for ops with identical first chars
        if (strcmp(next_chars, operators[i]) == 0) {
            if (next_chars[1] != '\0') {
                getchar();
            }
            getchar();
            tok->tokentype = OPERATOR;
            tok->whichval = i + 1;
            break;
        }
    }

    return (tok);
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
