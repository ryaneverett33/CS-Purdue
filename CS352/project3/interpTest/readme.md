The test cases survived an implementation of the parser from project 1 (with additional syntax specified for proj2)
and are tested with standard `javac` compiler and gives the desired output.

You should probably following this order to test your project,
as each case ask for increasingly number of features supported.

1. `simple.java`: no method invocation required. Prints string literals and integer expressions.
2. `loop.java`: asks for an implementation of method invocation: no parameters, belongs to a class with no instance variables. Computes factorial and prints the result.

According to the type checking guideline posted on Piazza, 80% of the scores you earn is based on cases 1 and 2. However, for interpretation, you have to implement interpretation of a method with no arguments and belongs to a class without instance variables, so that most of the cases are covered (especially while loops.

3. `array.java`: Tests array access and do bubble sorting. If interpreted correctly, the sorting should be successful.
4. `numbers.java`: Tests complicated computation (n choose k, greatest common divisor). It requires method invocation with arguments to be implemented.
5. `HanoiDemo.java`: Tests recursive method call.
