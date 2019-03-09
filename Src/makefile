
gh_cpp:	gh_cpp1.o gh_cpp2.o gh_cpp3.o gh_cpp4.o gh_cpp5.o
	gcc -ansi -Wall -g -o gh_cpp gh_cpp1.o gh_cpp2.o gh_cpp3.o gh_cpp4.o gh_cpp5.o

gh_cpp1.o:	gh_cpp1.c gh_cpp.h configure
	gcc -ansi -Wall -g -c gh_cpp1.c

gh_cpp2.o:	gh_cpp2.c gh_cpp.h
	gcc -ansi -Wall -g -c gh_cpp2.c

gh_cpp3.o:	gh_cpp3.c gh_cpp.h
	gcc -ansi -Wall -g -c gh_cpp3.c

gh_cpp4.o:	gh_cpp4.c gh_cpp.h
	gcc -ansi -Wall -g -c gh_cpp4.c

gh_cpp5.o:	gh_cpp5.c gh_cpp.h
	gcc -ansi -Wall -g -c gh_cpp5.c

configure_:
	echo "" | cpp -dM | \
	sed 's/\"/\\\"/g' | \
	sed 's/\(.*\)/	\"\1\",/' > configure.h

configure:
	echo "" > empty.h
	gcc -E -P -dM empty.h | \
	sed 's/\"/\\\"/g' | \
	sed 's/\(.*\)/	\"\1\",/' > configure.h
	rm -f empty.h

install:	gh_cpp
	cp gh_cpp /usr/bin

clean:
	rm -f *.o gh_cpp
