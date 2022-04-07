test: out.cpp prefix.cpp suffix.cpp
	clang++ -o test -g -Wno-parentheses-equality out.cpp
