# TinyML

This is the final project for the course of Functional Languages (MSc of Computer Science at University of Padova, 2023-2024) held by Prof. Alvise Spanò.
The initial source code provided by the professor can be found at: https://github.com/alvisespano/FunctionalLanguages-UniPD/tree/main/2023-24/TinyML

This interpreter implements only s subset of expression of ML.

# List of implementation of the interpreter

Here there is a brief summary of implementation on the type checker and the evaluator

## Math operators

These are the math operators: +, -, *, /, %. The original interpreter provided by the professor implements only the type checker for the first 4 operator on integers.

The type checker and the evaluator now implements these operator for the following types:
- Integer and floats, with automatic type escalation for integers for +, -, *, /;
- Integer for %;
- Strings for +, implementing string concatenation.

## Comparison operators

There are the comparison operators: =, <>, <, >, <=, >=. The original interprete implements the typechecking for = operator for all the types and <, >, <=, >= for integers.

The type checker and the evaluator now implements these operators for the following types:
- =, <> for all types;
- <, >, <=, >= for integers and floats, with automatic type escalation for integers;
- <, >, <=, >= for strings with alphanumerical order on the characters;
- <, >, <=, >= for booleans as defined on F# specification.

## Logic operators

These are the logic operators: and, or. There was no implementation of these operators on the original interpreter. Now they are defined for boolean values.

## Unary operators

This are the unary operators: not, -. On the original implementation there was only typechecking for the not operator.

The type checker and the evaluator now implements these operator for the following types:
- not for booleans;
- \- for integers and floats.
