ltest: out_lean.cpp prefix.cpp suffix.cpp
	clang++ -o ltest -g -O3 -Wno-parentheses-equality -fsanitize=address out_lean.cpp
test: out4.cpp prefix.cpp suffix.cpp
	clang++ -o test -g -O3 -Wno-parentheses-equality out4.cpp
old: out3.cpp prefix.cpp suffix.cpp
	clang++ -o old -g -O3 -Wno-parentheses-equality out3.cpp
test.asm: out4.cpp prefix.cpp suffix.cpp
	clang++ -o test.asm -O3 -S -Wno-parentheses-equality out4.cpp
old.asm: out3.cpp prefix.cpp suffix.cpp
	clang++ -o old.asm -O3 -S -Wno-parentheses-equality out3.cpp
