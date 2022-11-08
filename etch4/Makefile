# todo, compile Main.lean, run, static compilation with given sqlite version
out: main.cpp gen_main.c gen_query_1.c gen_main_.c gen_funs.c gen_out.c
	clang++ -o out -l sqlite3 -O3 -ffast-math main.cpp
