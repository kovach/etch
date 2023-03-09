# todo, compile Main.lean, run, static compilation with given sqlite version
out: main.cpp gen_funs.c gen_out.c decls.c Makefile gen_out_taco.c gen_out_sql.c
	g++ -o out -O3 -ffast-math main.cpp -lsqlite3
wcoj: wcoj.cpp gen_funs.c gen_out.c decls.c Makefile gen_out_taco.c gen_out_sql.c
	g++ -o wcoj -O3 -ffast-math wcoj.cpp -lsqlite3
