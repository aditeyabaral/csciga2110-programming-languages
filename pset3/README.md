In this assignment you will implement a parser and evaluator for a
language with stateful operations. It extends the language we looked
at in class that had the "box" constructs by adding the following
additional features:

- Vectors
- Transactions
- Multi-statement "begin" expressions
- Pairs

The starter code is split across multiple files:

- ps3-ast.rkt --- defines the types for values and expressions in the
  language and documents the behavior of the expressions.

- ps3.rkt --- this is where your implementation of the parser and
  evaluator will go.

- ps3-test.rkt --- contains testing code. Rather than being broken out
  into separate test cases for parser and evaluator, as in the
  previous assignment, we have combined them into 1 file.

You can run the tests by running

   racket ps3-test.rkt

in a directory containing the rkt files.

You should only be editing ps3.rkt. To submit your work, upload just
your completed ps3.rkt.  If you edit other files and your
implementation in ps3.rkt requires those edits, then your solution
will not work when uploading to GradeScope.
