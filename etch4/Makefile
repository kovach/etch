CC := clang
CXX := clang++

CFLAGS += -O2
CXXFLAGS += -std=c++20 -O3 -ffast-math

SQLITE_ZIP := sqlite-amalgamation-3410100.zip
SQLITE_URL := https://www.sqlite.org/2023/$(SQLITE_ZIP)
SQLITE_SHA256 := df0d54bf246521360c8148f64e7e5ad07a4665b4f902339e844f4c493d535ff5

# https://www.sqlite.org/compile.html#recommended_compile_time_options
SQLITE_CPPFLAGS := -I. \
	-DSQLITE_DQS=0 \
	-DSQLITE_THREADSAFE=0 \
	-DSQLITE_DEFAULT_MEMSTATUS=0 \
	-DSQLITE_DEFAULT_WAL_SYNCHRONOUS=1 \
	-DSQLITE_LIKE_DOESNT_MATCH_BLOBS \
	-DSQLITE_MAX_EXPR_DEPTH=0 \
	-DSQLITE_OMIT_DECLTYPE \
	-DSQLITE_OMIT_DEPRECATED \
	-DSQLITE_OMIT_PROGRESS_CALLBACK \
	-DSQLITE_OMIT_SHARED_CACHE \
	-DSQLITE_USE_ALLOCA \
	-DSQLITE_OMIT_AUTOINIT \
	-DSQLITE_ENABLE_UNLOCK_NOTIFY \
	-DSQLITE_ENABLE_DBSTAT_VTAB=1 \
	-DSQLITE_SECURE_DELETE \
	-DSQLITE_ENABLE_STMTVTAB \
	-DSQLITE_ENABLE_MATH_FUNCTIONS \
	-DHAVE_FDATASYNC=1 -DHAVE_USLEEP=1 -DHAVE_LOCALTIME_R=1 -DHAVE_GMTIME_R=1 -DHAVE_STRERROR_R=1 -DHAVE_POSIX_FALLOCATE=1
SQLITE_LDLIBS += -lm

DUCKDB_VERSION := v0.7.1
DUCKDB_CLI_ZIP := duckdb_cli-$(DUCKDB_VERSION)-linux-amd64.zip
DUCKDB_CLI_URL := https://github.com/duckdb/duckdb/releases/download/$(DUCKDB_VERSION)/duckdb_cli-linux-amd64.zip
DUCKDB_CLI_SHA256 := ca44c8dceea83287ba2b22216344f432e706e2dafe27a8c8cfd9bfaf77f4767f
LIBDUCKDB_ZIP := libduckdb-$(DUCKDB_VERSION)-linux-amd64.zip
LIBDUCKDB_URL := https://github.com/duckdb/duckdb/releases/download/$(DUCKDB_VERSION)/libduckdb-linux-amd64.zip
LIBDUCKDB_SHA256 := 1c15e0f142f6183e60d7a77b068b902532264519f2fd08dedc18573b7f507251

# default to our vendored copy of duckdb and sqlite3
DUCKDB ?= duckdb/duckdb
SQLITE3 ?= sqlite3/shell

# Define FORCE_REGEN to regenerate gen_funs.c every time `make` is run.
# FORCE_REGEN := 1

.PHONY: all
all: out

# Delete partial output files if make failed (e.g., if checksum did not match).
.DELETE_ON_ERROR:

out: main.cpp sqlite3.o sqlite3.h decls.c decls_tpch.cpp gen_funs.c
	$(LINK.cpp) main.cpp sqlite3.o $(LDLIBS) -o $@

out: LDLIBS += $(SQLITE_LDLIBS)

ifdef FORCE_REGEN
.PHONY: gen_funs.c
endif
gen_funs.c:
	lake update
	lake exe bench

gen_funs_readable.c: gen_funs.c impls_readable.h .clang-format
	$(CPP) $(CPPFLAGS) -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format --style='{ColumnLimit: 180}' >$@


$(SQLITE_ZIP):
	curl -o $@ $(SQLITE_URL)
	echo '$(SQLITE_SHA256) $(SQLITE_ZIP)' | sha256sum -c

sqlite3.c sqlite3.h: $(SQLITE_ZIP)
	unzip -p $< $(patsubst %.zip,%,$<)/$@ >$@

sqlite3/shell.c: $(SQLITE_ZIP)
	mkdir -p sqlite3
	unzip -p $< $(patsubst %.zip,%,$<)/$(@F) >$@

sqlite3.o: sqlite3.c sqlite3.h
sqlite3.o: CPPFLAGS += $(SQLITE_CPPFLAGS)

sqlite3/shell: sqlite3/shell.c sqlite3.o
sqlite3/shell: CPPFLAGS += $(SQLITE_CPPFLAGS)
sqlite3/shell: LDLIBS += $(SQLITE_LDLIBS)

bench-sqlite: bench-sqlite.cpp sqlite3.o
bench-sqlite: CPPFLAGS += $(SQLITE_CPPFLAGS)
bench-sqlite: LDLIBS += $(SQLITE_LDLIBS)

$(DUCKDB_CLI_ZIP):
	curl -Lo $@ $(DUCKDB_CLI_URL)
	echo '$(DUCKDB_CLI_SHA256) $(DUCKDB_CLI_ZIP)' | sha256sum -c

duckdb/duckdb: $(DUCKDB_CLI_ZIP)
	mkdir -p duckdb
	unzip -p $< duckdb >$@
	chmod +x $@

bench-duckdb: bench-duckdb.cpp duckdb/libduckdb.so duckdb/duckdb.hpp
	$(LINK.cpp) $< $(LDLIBS) -o $@
bench-duckdb: CPPFLAGS += -Iduckdb
bench-duckdb: LDLIBS += -Wl,-rpath,duckdb -Lduckdb -lduckdb

$(LIBDUCKDB_ZIP):
	curl -Lo $@ $(LIBDUCKDB_URL)
	echo '$(LIBDUCKDB_SHA256) $(LIBDUCKDB_ZIP)' | sha256sum -c

duckdb/libduckdb.so duckdb/duckdb.hpp duckdb/duckdb.h: $(LIBDUCKDB_ZIP)
	mkdir -p duckdb
	unzip -p $< $(@F) >$@

# Files produced using https://github.com/lovasoa/TPCH-sqlite
TPC-H-x0.01.db:
	curl -Lo $@ https://github.com/lovasoa/TPCH-sqlite/releases/download/v1.0/TPC-H-small.db
	echo '3e178ac56ffad2446ce9a555fab14333eb8a1038d59f4f1c30496914e2a87171 $@' | sha256sum -c
TPC-H-x0.025.db:
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.025.db
	echo '19bb3bf0efe421959ad28d8a99ee361d6c7e1a1cd2747d5ae6268b374d49b822 $@' | sha256sum -c
TPC-H-x0.05.db:
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.05.db
	echo '2d99f10cb5786ae409d3730ad778f8e837937b5b91e466cb2cbae0e386fd784f $@' | sha256sum -c
TPC-H-x0.1.db:
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.1.db
	echo 'cfe8f5724d78eebf27ce2b1f447a29266d874750689f43835791b2ee51101e75 $@' | sha256sum -c
TPC-H-x0.25.db:
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.25.db
	echo '384483c067fc46ef4384dcb44d5c66b9415939d448a9d03dce2d80cb5b16c692 $@' | sha256sum -c
TPC-H-x0.5.db:
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.5.db
	echo 'f2788cbedb42f4cc4fb4f5fd09d9d61cf9c738a9030d4de1da0c3fe739fa0cde $@' | sha256sum -c
TPC-H-x1.db:
	curl -Lo $@ https://github.com/lovasoa/TPCH-sqlite/releases/download/v1.0/TPC-H.db
	echo 'be2a81a548d930ae8c7a9eb427c44f73e2a753d53ffb16bb2a13f89ec8eb8bc8 $@' | sha256sum -c
TPC-H-x2.db:
	@echo 'Download this file at https://drive.google.com/file/d/158GjzzWj4wnGxDt3NfBKXFg-Hgj5e74O/view?usp=sharing' && false
	@#echo 'aa73478b811c4cb1323fbc98993899ab2018064e6b47e7c31868a661c7f8b5b6 $@' | sha256sum -c
TPC-H-x4.db:
	@echo 'Download this file at https://drive.google.com/file/d/14aM_1IY7ACLOzRtS1LKpRYGweDXZZF0M/view?usp=sharing' && false
	@#echo '9530ea95daecc3c8e411f9a7eb8a78ece3aaaae4b285729e45253283ea091f36 $@' | sha256sum -c

define TPCH_TEMPLATE
# Generate CSV files for TPC-H datasets
tpch-csv-$(1)-q5: TPC-H-$(1).db bench/tpch-q5-duckdb-export-to-csv.sql $$(DUCKDB)
	mkdir -p $$@
	rm -rf tmp.duckdb
	sed -e 's#TPC-H\.db#$$<#g' -e 's#tpch-csv#$$@#g' bench/tpch-q5-duckdb-export-to-csv.sql | $$(DUCKDB) tmp.duckdb
	rm tmp.duckdb

.PHONY: run-tpch-$(1)-q5-duckdb
run-tpch-$(1)-q5-duckdb: tpch-csv-$(1)-q5 bench/tpch-q5-duckdb-prep.sql bench/tpch-q5-duckdb.sql bench-duckdb
	./bench-duckdb <(sed -e 's#tpch-csv-q5#$$<#g' bench/tpch-q5-duckdb-prep.sql) 5:bench/tpch-q5-duckdb.sql

.PHONY: run-tpch-$(1)-q5-duckdbforeign
run-tpch-$(1)-q5-duckdbforeign: tpch-csv-$(1)-q5 bench/tpch-q5-duckdb-prep-foreign-key.sql bench/tpch-q5-duckdb.sql bench-duckdb
	./bench-duckdb <(sed -e 's#tpch-csv-q5#$$<#g' bench/tpch-q5-duckdb-prep-foreign-key.sql) 5:bench/tpch-q5-duckdb.sql

.PHONY: run-tpch-$(1)-q5-etch
run-tpch-$(1)-q5-etch: out TPC-H-$(1).db
	ln -sf TPC-H-$(1).db TPC-H.db
	./out
	rm TPC-H.db

.PHONY: run-tpch-$(1)-q5-sqlite
run-tpch-$(1)-q5-sqlite: bench/tpch-q5-sqlite-prep.sql bench/tpch-q5-sqlite.sql TPC-H-$(1).db $$(SQLITE3)
	./bench-sqlite <(sed 's/TPC-H\.db/TPC-H-$(1).db/g' bench/tpch-q5-sqlite-prep.sql) 5:bench/tpch-q5-sqlite.sql

endef

$(eval $(call TPCH_TEMPLATE,x0.01))
$(eval $(call TPCH_TEMPLATE,x0.025))
$(eval $(call TPCH_TEMPLATE,x0.05))
$(eval $(call TPCH_TEMPLATE,x0.1))
$(eval $(call TPCH_TEMPLATE,x0.25))
$(eval $(call TPCH_TEMPLATE,x0.5))
$(eval $(call TPCH_TEMPLATE,x1))
$(eval $(call TPCH_TEMPLATE,x2))
$(eval $(call TPCH_TEMPLATE,x4))


.PHONY: clean
clean:
	rm -f *.o tmp.duckdb sqlite3/shell out sqlite3.c sqlite3.h sqlite3/shell.c duckdb/duckdb
