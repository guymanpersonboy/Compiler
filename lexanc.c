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
#include <stdbool.h>
#include <ctype.h>
#include <string.h>
#include <math.h>
#include "token.h"
#include "lexan.h"

static bool consume_check_float(TOKEN tok, long num, int *m, bool dec_flag);

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
        // skips { } comments
        while ((c = peekchar()) != EOF && c != '}') {
            getchar();
        }
        getchar();
        skipblanks();
    }
    if (peekchar() == '(' && peek2char() == '*') {
        getchar();
        getchar();
        // skips (* *) comments
        while ((c = peekchar()) != EOF && (c != '*' || peek2char() != ')')) {
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
    // consume all other ALPHA and NUMERIC chars
    while ((c = peekchar()) != EOF &&
            (CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC)) {
        getchar();
    }
    // determine if a reserved word
    for (int word = 0; word < NUM_RESERVED; word++) {
        if (strcmp(str, reserved[word]) == 0) {
            const int LOOKUP_BIAS = 245;
            // check if actually an operator. reserved index: 29 <= word <= 34)
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
    // an identifier
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
    // consume all other chars until and including an '
    while ((c = peekchar()) != EOF &&
            (c == '\'' || CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC)) {
        getchar();
        if (c == '\'') {
            break;
        }
    }
    str[i] = '\0';
    strcpy(tok->stringval, str);
    tok->tokentype = STRINGTOK;

    return tok;
}

/* Get Operators and Delimiters */
TOKEN special (TOKEN tok) {
    const int NUM_DELIMITERS = 8;
    const int NUM_OPERATORS = 19;
    char next_chars[2] = {peekchar(), peek2char()};
    int c, i;

    // set up next_chars to be read as a string for strcmp()
    if ((c = peek2char()) == EOF || (c == ' ' || c == '\n' || c == '\t')) {
        next_chars[1] = '\0';
    }

    // determine if an delimiter or operator
    for (i = 0; i < NUM_DELIMITERS; i++) {
        if ((c = peekchar()) != EOF && next_chars[0] == delimiters[i][0]
                && next_chars[1] != '=') {
            // check if actually the DOT operator
            if (next_chars[0] == '.' && next_chars[1] != '.') {
                break;
            }
            // a delimiter
            tok->tokentype = DELIMITER;
            tok->whichval = i + 1;
            if (strcmp(next_chars, "..") == 0) {
                getchar();
            }
            getchar();

            return tok;
        }
    }
    for (i = 0; i < NUM_OPERATORS; i++) {
        // check for operators with identical chars
        if ((c = peekchar()) != EOF && next_chars[0] == operators[i][0]
                && next_chars[1] == operators[i][1]) {
            // an operator
            tok->tokentype = OPERATOR;
            tok->whichval = i + 1;
            if (next_chars[1] != '\0') {
                getchar();
            }
            getchar();
            break;
        }
    }

    return tok;
}

/* Get and convert unsigned numbers of all types. */
TOKEN number (TOKEN tok) {
    bool dec_flag = false;
    bool overflow_flag = false;
    int sig_figs = 0;
    int mantissa = 0;
    long num = 0;
    int  c, charval;

    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    // converts a number to internal numeric form
    while ((c = peekchar()) != EOF && (CHARCLASS[c] == NUMERIC || c == '.')) {
        c = getchar();
        if (dec_flag) {
            mantissa--;
        }
        if (c == '.') {
            // check if actually delimiter ".."
            if (peekchar() == '.') {
                // put one '.' and process number as is
                ungetc(c, stdin);
                break;
            }
            tok->basicdt = REAL;
            dec_flag = true;
            continue;
        }
        // count for 8 sig figs if num will be a float
        if (c != '0' || sig_figs) {
            sig_figs++;
        }

        charval = (c - '0');
        // check for INTEGER overflow
        if (!dec_flag && (num > __INT_MAX__ / 10 || (num == __INT_MAX__ / 10
                && charval > 7))) {
            overflow_flag = consume_check_float(tok, num, &mantissa, dec_flag);
            if (overflow_flag) {
                break;
            }
        }
        num = num * 10 + charval;

        if (dec_flag && sig_figs == 8) {
            // consume all nubmers until reaching 'e' or end of float
            while ((c = peekchar()) != EOF && (CHARCLASS[c] == NUMERIC)) {
                getchar();
            }
            break;
        }
    }

    // E notation
    if ((c = peekchar()) == 'e' || c == 'E') {
        int exp = 0;
        int bias = 1;
        tok->basicdt = REAL;
        getchar();
        
        // bias on exp
        if ((c = peekchar()) == '+' || c == '-') {
            c = getchar();
            bias = (c == '-') ? -1 : 1;
        }
        // read exp value
        while ((c = peekchar()) != EOF && (CHARCLASS[c] == NUMERIC)) {
            c = getchar();
            charval = (c - '0');
            exp = exp * 10 + charval;
        }
        mantissa += bias * exp;
    }

    // set tok->tokenvalue
    if (tok->basicdt == REAL) {
        tok->realval = num * pow(10, mantissa);
        fprintf(stderr, "%f\n", tok->realval);

        fprintf(stderr, "exp %d\n", mantissa);
        if (-45 > mantissa || mantissa > 31) {
            printf("Floating number out of range\n");
            tok->realval = 0;
        }
    } else {
        tok->intval = num;

        if (overflow_flag) {
            printf("Integer number out of range\n");
        }
    }

    return (tok);
}

/* consume the rest of the line and check if the tok is a valid float
return true if INTEGER overflow and false if a float */
static bool consume_check_float(TOKEN tok, long num, int *m, bool dec_flag) {
    // overflows at 10 sigs keep only 8
    num /= 100;
    bool overflow_flag = false;
    // removed two digits so m + 2 : initialize as 0
    int mantissa = (dec_flag) ? *m + 2 : 0;
    int c;

    while ((c = peekchar()) != EOF && (CHARCLASS[c] == NUMERIC || c == '.')) {
        c = getchar();
        if (c == '.') {
            // check if actually delimiter ".."
            if (peekchar() == '.') {
                // put one '.' and process number as is
                ungetc(c, stdin);

                return true;
            }
            tok->basicdt = REAL;
            dec_flag = true;
            continue;
        }
        mantissa += (dec_flag) ? 0 : 1;
    }
    *m = mantissa;
    // return false if a float
    if (dec_flag) {
        return false;
    }

    return true;
}
