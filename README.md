MLCCompiler
===========

A MuC compiler written in StandardML.

Example usage:
Run make in the top level directory to create the MIPS compiler.
Then use the ucc.sh script to create MIPS assebly code from MuC source:

    ./ucc.sh testsuit/noisy/simple/sim09.c

will create a sim09.s assembly file in the current directory.

To compile and run it you have to use a MIPS emulator such as SPIM:

    spim -file sim09.s 

should give the output:

    12345678
    ABCD