# gh_cpp

gh_cpp is an implmentation of a C preprocessor, with some additional checking capabilities.
It can explain macro-expansions and check a small subset of the MISRA-2004 coding guidelines.

### Options

	$ gh_cpp -[vinm] -[IDU] filename.c

with the following options:

	-I, -D, -U compiler directives as in gcc
	-d	for debugging, extra verbose
	-i	do not expand #include files
	-m	check ~35 simple misra rules
	-m -m	check the rules also for included files
	-n	numbered output
	-x	show only output for the toplevel file
	-e	explain all macro expansions
	-v	more verbose
