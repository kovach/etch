CC := clang
CXX := clang++

CFLAGS += -O2
CXXFLAGS += -std=c++20 -O3 -ffast-math

SQLITE_ZIP := sqlite-amalgamation-3400100.zip
SQLITE_URL := https://www.sqlite.org/2022/$(SQLITE_ZIP)
SQLITE_SHA256 := 49112cc7328392aa4e3e5dae0b2f6736d0153430143d21f69327788ff4efe734

# todo, compile Main.lean, run
out: main.cpp sqlite3.o sqlite3.h decls.c decls_tpch.cpp gen_funs.c
	$(CXX) -o out $(CXXFLAGS) main.cpp sqlite3.o

gen_funs_readable.c: gen_funs.c impls_readable.h
	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format >$@
#	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format >$@


$(SQLITE_ZIP):
	curl -o $@ $(SQLITE_URL)
	echo '$(SQLITE_SHA256) $(SQLITE_ZIP)' | sha256sum -c

sqlite3.c sqlite3.h: $(SQLITE_ZIP)
	unzip -p $< $(patsubst %.zip,%,$<)/$@ >$@

sqlite3.o: sqlite3.c sqlite3.h

clean:
	rm -f *.o
