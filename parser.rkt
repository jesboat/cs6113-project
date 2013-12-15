#lang ragg

 program : value
         | expression

 id : IDENTIFIER

 num : INT

 value: id
      | LEFT-PAREN RIGHT-PAREN
      | num
      | VOID
      | FUN id RIGHT-ARROW expression
      | LEFT-ANGLE-BRACKET value PIPE value RIGHT-ANGLE-BRACKET
      | LEFT-PAREN value RIGHT-PAREN


 expression: value
           | value value
           | LEFT-PAREN expression RIGHT-PAREN
           | LET id EQ value IN expression
           | IF expression THEN expression ELSE expression
           | LEFT-ANGLE-BRACKET expression PIPE expression RIGHT-ANGLE-BRACKET

