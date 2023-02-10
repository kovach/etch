CC := clang
CXX := clang++

# todo, compile Main.lean, run, static compilation with given sqlite version
out: main.cpp gen_main.c gen_query_1.c gen_main_.c gen_funs.c gen_out.c decls.c Makefile
	$(CXX) -o out -l sqlite3 -O3 -ffast-math main.cpp

gen_funs_readable.c: gen_funs.c impls_readable.h
	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format >$@
#	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format >$@
