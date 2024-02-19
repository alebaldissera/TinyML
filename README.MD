# TinyML

This is the final project for the course of Functional Languages (MSc of Computer Science at University of Padova, 2023-2024) held by Prof. Alvise Spanò.
The initial source code provided by the professor can be found at: https://github.com/alvisespano/FunctionalLanguages-UniPD/tree/main/2023-24/TinyML

This interpreter implements only s subset of expression of ML.

# Run the project

You can run the project directly with:

```bash
dotnet run --project src .\\src\\App\\TinyML.fsproj
```

Or build the project with:

```bash
dotnet build --project src .\\src\\App\\TinyML.fsproj
```

You can also choose to use the type checker algorithm instead the type inference with the flag: `--type-checker`.

# List of implementations of the interpreter

Here there is a brief summary of implementation on the type checker and the evaluator

## Math operators

These are the math operators: +, -, *, /, %. The original interpreter provided by the professor implements only the type checker for the first 4 operator on integers.

The type checker and the evaluator now implements these operator for the following types:
- Integer and floats for +, -, *, /, %;
- Strings for +, implementing string concatenation.

## Comparison operators

There are the comparison operators: =, <>, <, >, <=, >=. The original interprete implements the typechecking for = operator for all the types and <, >, <=, >= for integers.

The type checker and the evaluator now implements these operators for the following types:
- =, <> for all types;
- <, >, <=, >= for integers and floats;
- <, >, <=, >= for strings with alphanumerical order on the characters;
- <, >, <=, >= for booleans as defined on F# specification.

## Logic operators

These are the logic operators: and, or. There was no implementation of these operators on the original interpreter. Now they are defined for boolean values.

## Unary operators

This are the unary operators: not, -. I also added `int`, `float`, `string`, `char` for type casting. On the original implementation there was only typechecking for the not operator.

The type checker and the evaluator now implements these operator for the following types:
- not for booleans;
- \- for integers and floats;
- `int`, `float`, `string`, `char` for all available types except for `unit`.

## If-Then-Else

The original implementation has support only for If-Then-Else statement. The new implementation supports also If-Then statement. The If guard supports only boolean expressions.

# Implementation of operator overloading

To implements operator overloading, I created a separate table which maps each operator to a list containing the input types and the output type as last element. The type checker or the type inference algorithm lookup those tables checking the types. The type inference algorithm, by default, fallback to the first element of the list is no other type is specified.

This specific implementation allow a discrete level of flexibility and can also be used to allow the user to extend the functionality of the operators for other types with a proper extension of the language. At evaluation time, there must be a similar table to maps custom operator to a function application.
