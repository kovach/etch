# todo, compile Main.lean, run, static compilation with given sqlite version
out: main.cpp gen_main.c gen_query_1.c gen_main_.c gen_funs.c gen_out.c decls.c Makefile gen_out_taco.c gen_out_sql.c
	clang++ -o out -l sqlite3 -O3 -ffast-math main.cpp
wcoj: wcoj.cpp gen_main.c gen_query_1.c gen_main_.c gen_funs.c gen_out.c decls.c Makefile gen_out_taco.c gen_out_sql.c
	clang++ -o wcoj -l sqlite3 -O3 -ffast-math wcoj.cpp
