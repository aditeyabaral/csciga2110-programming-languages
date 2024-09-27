In this assignment you will implement a parser and evaluator for a
simple language.  It extends the first language we implemented an
interpreter for in class by adding the following features:

- Adding boolean values and lists and basic operations on them.
- If statements.
- Binding multiple variables at a time with let and let*
- Limited forms of recursion on numbers and values

The starter code is split across multiple files:

- ps2-ast.rkt --- defines the types for values and expressions in the
  language and documents the behavior of the expressions.

- ps2.rkt --- this is where your implementation of parse and eval will go.

- ps2-test.rkt --- contains testing code. The list test-examples is a
  list of s-expressions for example programs. The list test-asts is a
  list of ASTs generated by our reference solution corresponding to
  these s-expressions, (e.g. the ith element of this list is the AST
  for the ith program in test-examples). The list test-results is a
  list of values corresponding to what executing these programs should
  result in.  (e.g. the ith element of test-results is what you should
  get after parsing and evaluating the ith program in test-examples).

  Includes rackunit unit testing declarations to run tests
  corresponding to these cases, which are used in gradescope.
  
  The tests are split into two groups:

  1. Parsing tests check whether for each program in test-examples,
     your implementation of parse yields the AST in test-asts.

  2. Evaluation tests check whether for each AST in test-asts,
     your implementation of eval yields the result in test-results.

  In other words, we split things up so that even if your
  implementation of parse has a bug in it, you can still get credit
  for correctly evaluating the AST that should have been generated.

- ps2-test-util.rkt --- a utility file for helping to print the names of
  test cases when producing test result output.

You can run the tests by running

   racket ps2-test.rkt

in a directory containing the rkt files.

You should only be editing ps2.rkt. To submit your work, upload just
your completed ps2.rkt.  If you edit other files and your
implementation in ps2.rkt requires those edits, then your solution
will not work when uploading to GradeScope.