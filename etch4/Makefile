CC := clang
CXX := clang++

CFLAGS += -O2
CXXFLAGS += -std=c++20 -O3 -ffast-math

SQLITE_ZIP := sqlite-amalgamation-3400100.zip
SQLITE_URL := https://www.sqlite.org/2022/$(SQLITE_ZIP)
SQLITE_SHA256 := 49112cc7328392aa4e3e5dae0b2f6736d0153430143d21f69327788ff4efe734

DUCKDB_VERSION := v0.7.1
DUCKDB_ZIP := duckdb_cli-$(DUCKDB_VERSION)-linux-amd64.zip
DUCKDB_URL := https://github.com/duckdb/duckdb/releases/download/$(DUCKDB_VERSION)/duckdb_cli-linux-amd64.zip
DUCKDB_SHA256 := ca44c8dceea83287ba2b22216344f432e706e2dafe27a8c8cfd9bfaf77f4767f

# default to our vendored copy of duckdb
DUCKDB ?= duckdb/duckdb

# todo, compile Main.lean, run
out: main.cpp sqlite3.o sqlite3.h decls.c decls_tpch.cpp gen_funs.c
	$(CXX) -o out $(CXXFLAGS) main.cpp sqlite3.o

gen_funs_readable.c: gen_funs.c impls_readable.h
	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format --style='{ColumnLimit: 180}' >$@
#	$(CC) -E -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format >$@


$(SQLITE_ZIP):
	curl -o $@ $(SQLITE_URL)
	echo '$(SQLITE_SHA256) $(SQLITE_ZIP)' | sha256sum -c

sqlite3.c sqlite3.h: $(SQLITE_ZIP)
	unzip -p $< $(patsubst %.zip,%,$<)/$@ >$@

sqlite3.o: sqlite3.c sqlite3.h

$(DUCKDB_ZIP):
	curl -Lo $@ $(DUCKDB_URL)
	echo '$(DUCKDB_SHA256) $(DUCKDB_ZIP)' | sha256sum -c

duckdb/duckdb: $(DUCKDB_ZIP)
	mkdir -p duckdb
	unzip -p $< duckdb >$@

TPC-H-x1.db:
	curl -Lo $@ https://github.com/lovasoa/TPCH-sqlite/releases/download/v1.0/TPC-H.db
	echo 'be2a81a548d930ae8c7a9eb427c44f73e2a753d53ffb16bb2a13f89ec8eb8bc8 $@' | sha256sum -c

# Generate CSV files for TPC-H datasets
tpch-csv-x1-q5: TPC-H-x1.db bench/tpch-q5-duckdb-export-to-csv.sql $(DUCKDB)
	mkdir -p $@
	rm -rf tmp.duckdb
	sed -e 's#TPC-H\.db#$<#g' -e 's#tpch-csv#$@#g' bench/tpch-q5-duckdb-export-to-csv.sql | $(DUCKDB) tmp.duckdb
	rm tmp.duckdb

.PHONY: run-tpch-duckdb-x1-q5
run-tpch-duckdb-x1-q5: tpch-csv-x1-q5 bench/tpch-q5-duckdb.sql $(DUCKDB)
	sed -e 's#tpch-csv-q5#$<#g' bench/tpch-q5-duckdb.sql | $(DUCKDB)

clean:
	rm -f *.o tmp.duckdb
