test: out.cpp prefix.cpp suffix.cpp
	clang++ -o test -g -Wno-parentheses-equality out.cpp
	clang++ -o test.asm -O3 -S -Wno-parentheses-equality out.cpp
