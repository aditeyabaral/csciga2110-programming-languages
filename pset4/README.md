In this assignment you will implement a parser and evaluator for a
language with objects. Instead of class-based inheritance, the object
system we will implement will support something called delegation, in
which an object forwards unrecognized methods/messages to another
object. 

Please read https://users.dcc.uchile.cl/~etanter/ooplai/Forwarding_and_Delegation.html
if you are not familiar with OO programming with delegation.

The starter code is split across multiple files:

- ps4-ast.rkt --- defines the types for values and expressions in the
  language and documents the behavior of the expressions. DO NOT change this file.

- ps4.rkt --- this is where your implementation of the parser and
  evaluator will go.

- ps4-test.rkt --- default test cases. We recommend starting with this testing file
  while debugging your implementation.

- ps4-test-rand.rkt --- randomized versions of test cases, which will be used on GradeScope
  to minimize hard coding / coincidental solutions.

You can run the tests by running

   racket ps4-test.rkt

or

   racket ps4-test-rand.rkt

in a directory containing the rkt files.

You should only be editing ps4.rkt. To submit your work, upload just
your completed ps4.rkt.  If you edit other files and your
implementation in ps4.rkt requires those edits, then your solution
will not work when uploading to GradeScope. Please do not rename ps4.rkt
before uploading.
