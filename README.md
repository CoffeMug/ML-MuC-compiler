MLCCompiler
===========

A MuC compiler written in StandardML.

Example usage:

  ./ucc.sh testsuit/noisy/simple/sim09.c

will create a sim09.s assembly file.

To compile and run it you have to use a MIPS emulator such as SPIM:

  spim -file sim09.s 

should give the output:

  12345678
  ABCD