/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_Y_TAB_HH_INCLUDED
# define YY_YY_Y_TAB_HH_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    PRINTLN = 258,
    INT = 259,
    VOID = 260,
    IF = 261,
    WHILE = 262,
    TTRUE = 263,
    TFALSE = 264,
    OBJECT = 265,
    THIS = 266,
    NEW = 267,
    MAINCLASS = 268,
    CLASS = 269,
    PUBLIC = 270,
    STRING = 271,
    RETURN = 272,
    LENGTH = 273,
    DOUBLEPLUS = 274,
    BOOLAND = 275,
    BOOLOR = 276,
    LESSTHANEQUALTO = 277,
    GREATERTHANEQUALTO = 278,
    BOOLEQUAL = 279,
    BOOLNOTEQUAL = 280,
    ID = 281,
    INTEGER_LITERAL = 282,
    STRING_LITERAL = 283,
    BOOLEAN = 284,
    EXTENDS = 285,
    ELSE = 286,
    INVALID = 287,
    DOUBLEMINUS = 288,
    PRINT = 289
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 30 "parser.y" /* yacc.c:1909  */

        char * s;
        bool b;
        int i;
        char c;
        class AST_Node * n;
        int tok;

#line 98 "y.tab.hh" /* yacc.c:1909  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_HH_INCLUDED  */
