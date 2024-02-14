# we assume bash
SHELL := bash

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
SQLITE_LDLIBS += -lm -ldl

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

# Define TPCH_DB_GENERATE to generate TPC-H SF ≤1 databases from scratch.
# By default, we download the preloaded DBs.
# DBs with SF >1 are always generated from scratch.
# TPCH_DB_GENERATE := 1

# Delete partial output files if make failed (e.g., if checksum did not match).
.DELETE_ON_ERROR:

ALL_BENCH := bench-tpch-q5 bench-tpch-q9 bench-wcoj bench-taco bench-matmul bench-filtered-spmv

.PHONY: all
all: $(ALL_BENCH) $(DUCKDB) $(SQLITE3) bench-duckdb bench-sqlite

bench-tpch-q5: bench-tpch-q5.cpp gen_tpch_q5.c
bench-tpch-q9: bench-tpch-q9.cpp gen_tpch_q9.c
bench-wcoj: bench-wcoj.cpp gen_wcoj.c
bench-taco: bench-taco.cpp gen_taco.c taco_kernels.c
bench-filtered-spmv: bench-filtered-spmv.cpp gen_filtered_spmv.c
bench-matmul: bench-matmul.cpp gen_matmul.c

$(ALL_BENCH):
	$(LINK.cpp) $< sqlite3.o $(LDLIBS) -o $@
$(ALL_BENCH): CPPFLAGS += $(SQLITE_CPPFLAGS)
$(ALL_BENCH): LDLIBS += $(SQLITE_LDLIBS)
$(ALL_BENCH): sqlite3.o sqlite3.h common.h operators.h

ifdef FORCE_REGEN
.PHONY: gen_filtered_spmv.c gen_matmul.c gen_tpch_q5.c gen_tpch_q9.c gen_wcoj.c gen_taco.c
endif
gen_filtered_spmv.c gen_matmul.c gen_tpch_q5.c gen_tpch_q9.c gen_wcoj.c gen_taco.c &:
	lake update
	-lake exe cache get # get mathlib4 cache
	lake exe bench

%_readable.c: %.c impls_readable.h .clang-format
	$(CPP) $(CPPFLAGS) -P -include impls_readable.h $< | sed -E -e 's/\b1 \*//g' -e 's/\* 1\b//g' -e 's/\b0 \+//g' -e 's/\+ 0\b//g' -e 's/&& true\b//g' -e 's/\btrue &&//g' | clang-format --style='{ColumnLimit: 180}' >$@


$(SQLITE_ZIP):
	curl -o $@ $(SQLITE_URL)
	echo '$(SQLITE_SHA256) $(SQLITE_ZIP)' | sha256sum -c

sqlite3.c sqlite3.h sqlite3/shell.c &: $(SQLITE_ZIP)
	rm -rf tmp_sqlite3
	mkdir -p sqlite3
	unzip $< "$(patsubst %.zip,%,$<)/*" -d tmp_sqlite3
	mv tmp_sqlite3/$(patsubst %.zip,%,$<)/sqlite3.c sqlite3.c && touch sqlite3.c
	mv tmp_sqlite3/$(patsubst %.zip,%,$<)/sqlite3.h sqlite3.h && touch sqlite3.h
	mv tmp_sqlite3/$(patsubst %.zip,%,$<)/shell.c sqlite3/shell.c && touch sqlite3/shell.c
	rm -rf tmp_sqlite3

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

duckdb:
	mkdir -p $@

duckdb/duckdb: $(DUCKDB_CLI_ZIP) | duckdb
	unzip -p $< duckdb >$@
	chmod +x $@

bench-duckdb: bench-duckdb.cpp duckdb/libduckdb.so duckdb/duckdb.hpp
	$(LINK.cpp) $< $(LDLIBS) -o $@
bench-duckdb: CPPFLAGS += -Iduckdb
bench-duckdb: LDLIBS += -Wl,-rpath,duckdb -Lduckdb -lduckdb

$(LIBDUCKDB_ZIP):
	curl -Lo $@ $(LIBDUCKDB_URL)
	echo '$(LIBDUCKDB_SHA256) $(LIBDUCKDB_ZIP)' | sha256sum -c

duckdb/libduckdb.so duckdb/duckdb.hpp duckdb/duckdb.h &: $(LIBDUCKDB_ZIP) | duckdb
	unzip -o $< -d duckdb
	touch duckdb/libduckdb.so duckdb/duckdb.hpp duckdb/duckdb.h

data:
	mkdir -p $@

TPCH_DB_TO_GEN :=

ifdef TPCH_DB_GENERATE
TPCH_DB_TO_GEN += 0.01 0.025 0.05 0.1 0.25 0.5 1
else
# Files produced using https://github.com/lovasoa/TPCH-sqlite
data/TPC-H-x0.01.db: | data
	curl -Lo $@ https://github.com/lovasoa/TPCH-sqlite/releases/download/v1.0/TPC-H-small.db
	echo '3e178ac56ffad2446ce9a555fab14333eb8a1038d59f4f1c30496914e2a87171 $@' | sha256sum -c
data/TPC-H-x0.025.db: | data
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.025.db
	echo '19bb3bf0efe421959ad28d8a99ee361d6c7e1a1cd2747d5ae6268b374d49b822 $@' | sha256sum -c
data/TPC-H-x0.05.db: | data
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.05.db
	echo '2d99f10cb5786ae409d3730ad778f8e837937b5b91e466cb2cbae0e386fd784f $@' | sha256sum -c
data/TPC-H-x0.1.db: | data
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.1.db
	echo 'cfe8f5724d78eebf27ce2b1f447a29266d874750689f43835791b2ee51101e75 $@' | sha256sum -c
data/TPC-H-x0.25.db: | data
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.25.db
	echo '384483c067fc46ef4384dcb44d5c66b9415939d448a9d03dce2d80cb5b16c692 $@' | sha256sum -c
data/TPC-H-x0.5.db: | data
	curl -Lo $@ https://github.com/kovach/etch/releases/download/files/TPC-H-x0.5.db
	echo 'f2788cbedb42f4cc4fb4f5fd09d9d61cf9c738a9030d4de1da0c3fe739fa0cde $@' | sha256sum -c
data/TPC-H-x1.db: | data
	curl -Lo $@ https://github.com/lovasoa/TPCH-sqlite/releases/download/v1.0/TPC-H.db
	echo 'be2a81a548d930ae8c7a9eb427c44f73e2a753d53ffb16bb2a13f89ec8eb8bc8 $@' | sha256sum -c
endif

# x2 and x4 don't have pre-generated files.
TPCH_DB_TO_GEN += 2 4

data/TPCH-sqlite data/TPCH-sqlite.stamp &: | data
	rm -rf data/TPCH-sqlite
	git clone --recursive https://github.com/lovasoa/TPCH-sqlite.git data/TPCH-sqlite
	git -C data/TPCH-sqlite -c advice.detachedHead=false checkout 23e420d8d49a6471b4275d9cf060572e44a53ab4
	echo 23e420d8d49a6471b4275d9cf060572e44a53ab4 >data/TPCH-sqlite.stamp

define TPCH_DB_TEMPLATE
	make -C data/TPCH-sqlite clean
	PATH="$$PWD/data/TPCH-sqlite/bin:$$PATH" make -C data/TPCH-sqlite -j1 SCALE_FACTOR=$(SIZE)
	mv data/TPCH-sqlite/TPC-H.db data/TPC-H-x$(SIZE).db

endef

data/TPCH-sqlite/bin: | data/TPCH-sqlite $(SQLITE3)
	mkdir $@
	ln -s $$(realpath $(SQLITE3)) $@/sqlite3

$(foreach SIZE,$(TPCH_DB_TO_GEN), data/TPC-H-x$(SIZE).db) &: data/TPCH-sqlite.stamp data/TPCH-sqlite/bin | data
	$(foreach SIZE,$(TPCH_DB_TO_GEN),$(TPCH_DB_TEMPLATE))

define FILTERED_SPMV_TEMPLATE
data/filtered-spmv-$(1).db: bench/filtered-spmv-datagen.py | data
	python3 $$< $$@ $$(shell bc -l <<< '$(1)/(10000*10000)') 0.1 $(1)

.PHONY: run-filtered-spmv-$(1)-etch
run-filtered-spmv-$(1)-etch: bench-filtered-spmv data/filtered-spmv-$(1).db
	./bench-filtered-spmv data/filtered-spmv-$(1).db

.PHONY: run-filtered-spmv-$(1)-duckdb
run-filtered-spmv-$(1)-duckdb: data/filtered-spmv-$(1).db bench/filtered-spmv-duckdb-prep.sql bench/filtered-spmv-duckdb.sql bench-duckdb
	./bench-duckdb <(sed -e 's#data/filtered-spmv.*\.db#$$<#g' bench/filtered-spmv-duckdb-prep.sql) 5:<(sed -e 's#0\.8#0#g' bench/filtered-spmv-duckdb.sql) 5:<(sed -e 's#0\.8#0.2#g' bench/filtered-spmv-duckdb.sql) 5:<(sed -e 's#0\.8#0.4#g' bench/filtered-spmv-duckdb.sql) 5:<(sed -e 's#0\.8#0.6#g' bench/filtered-spmv-duckdb.sql) 5:<(sed -e 's#0\.8#0.8#g' bench/filtered-spmv-duckdb.sql) 5:<(sed -e 's#0\.8#1#g' bench/filtered-spmv-duckdb.sql)

.PHONY: run-filtered-spmv-$(1)-sqlite
run-filtered-spmv-$(1)-sqlite: data/filtered-spmv-$(1).db bench/filtered-spmv-sqlite-prep.sql bench/filtered-spmv-sqlite.sql bench-sqlite
	./bench-sqlite <(sed -e 's#data/filtered-spmv.*\.db#$$<#g' bench/filtered-spmv-sqlite-prep.sql) 5:<(sed -e 's#0\.8#0#g' bench/filtered-spmv-sqlite.sql) 5:<(sed -e 's#0\.8#0.2#g' bench/filtered-spmv-sqlite.sql) 5:<(sed -e 's#0\.8#0.4#g' bench/filtered-spmv-sqlite.sql) 5:<(sed -e 's#0\.8#0.6#g' bench/filtered-spmv-sqlite.sql) 5:<(sed -e 's#0\.8#0.8#g' bench/filtered-spmv-sqlite.sql) 5:<(sed -e 's#0\.8#1#g' bench/filtered-spmv-sqlite.sql)

endef

$(foreach nonzeros,2000000,$(eval $(call FILTERED_SPMV_TEMPLATE,$(nonzeros))))

define MATMUL_TEMPLATE
data/matmul-$(1).db: bench/matmul-datagen.py | data
	python3 $$< $$@ $$(shell bc -l <<< '$(1)/(10000*10000)') $(1)

run-matmul-$(1): bench-matmul data/matmul-$(1).db
	./bench-matmul data/matmul-$(1).db

endef

$(foreach nonzeros,200 2000 20000 200000,$(eval $(call MATMUL_TEMPLATE,$(nonzeros))))

define TACO_TEMPLATE
data/taco-s$(1).db: bench/taco-datagen.py | data
	python3 $$< $$@ $(1)

run-taco-s$(1): bench-taco data/taco-s$(1).db
	./bench-taco data/taco-s$(1).db

endef

$(foreach sparsity,0.0001 0.0003 0.0007 0.001 0.003 0.007 0.01 0.03 0.07 0.1 0.3 0.5 0.7 0.9,$(eval $(call TACO_TEMPLATE,$(sparsity))))

define WCOJ_TEMPLATE
# Generate CSV files for the worse-case optimal join benchmark
data/wcoj-csv-x$(1): bench/wcoj-datagen.py | data
	rm -rf $$@
	mkdir -p $$@
	python3 $$< $$@ $$$$((100*$(1)))

.PHONY: run-wcoj-x$(1)-duckdb
run-wcoj-x$(1)-duckdb: data/wcoj-csv-x$(1) bench/wcoj-duckdb-prep.sql bench/wcoj-duckdb.sql bench-duckdb
	./bench-duckdb <(sed -e 's#wcoj-csv#$$<#g' bench/wcoj-duckdb-prep.sql) 5:bench/wcoj-duckdb.sql

data/wcoj-x$(1).db: data/wcoj-csv-x$(1) bench/wcoj-sqlite-import.sql $$(SQLITE3) | data
	rm -f $$@
	sed 's#wcoj-csv#$$<#g' bench/wcoj-sqlite-import.sql | $$(SQLITE3) $$@

.PHONY: run-wcoj-x$(1)-etch
run-wcoj-x$(1)-etch: bench-wcoj data/wcoj-x$(1).db
	./bench-wcoj data/wcoj-x$(1).db

.PHONY: run-wcoj-x$(1)-sqlite
run-wcoj-x$(1)-sqlite: data/wcoj-x$(1).db bench/wcoj-sqlite-prep.sql bench/wcoj-sqlite.sql bench-sqlite
	./bench-sqlite <(sed -e 's#wcoj\.db#$$<#g' bench/wcoj-sqlite-prep.sql) 5:bench/wcoj-sqlite.sql

endef

$(foreach scale,1 3 5 10 25 30 50 100 250 300 500 1000 3000 10000,$(eval $(call WCOJ_TEMPLATE,$(scale))))

define TPCH_TEMPLATE
data/tpch-csv-$(1)-$(2): data/TPC-H-$(1).db bench/tpch-$(2)-duckdb-export-to-csv.sql $$(DUCKDB) | data
	mkdir -p $$@
	rm -rf tmp-tpch-csv-$(1)-$(2).duckdb
	sed -e 's#TPC-H\.db#$$<#g' -e 's#tpch-csv#$$@#g' bench/tpch-$(2)-duckdb-export-to-csv.sql | $$(DUCKDB) tmp-tpch-csv-$(1)-$(2).duckdb
	rm tmp-tpch-csv-$(1)-$(2).duckdb

.PHONY: run-tpch-$(1)-$(2)-duckdb
run-tpch-$(1)-$(2)-duckdb: data/tpch-csv-$(1)-$(2) bench/tpch-$(2)-duckdb-prep.sql bench/tpch-$(2)-duckdb.sql bench-duckdb
	./bench-duckdb <(sed 's#tpch-csv#$$<#g' bench/tpch-$(2)-duckdb-prep.sql) 5:bench/tpch-$(2)-duckdb.sql

.PHONY: run-tpch-$(1)-$(2)-duckdbforeign
run-tpch-$(1)-$(2)-duckdbforeign: data/tpch-csv-$(1)-$(2) bench/tpch-$(2)-duckdb-prep-foreign-key.sql bench/tpch-$(2)-duckdb.sql bench-duckdb
	./bench-duckdb <(sed 's#tpch-csv#$$<#g' bench/tpch-$(2)-duckdb-prep-foreign-key.sql) 5:bench/tpch-$(2)-duckdb.sql

.PHONY: run-tpch-$(1)-$(2)-sqlite
run-tpch-$(1)-$(2)-sqlite: bench/tpch-$(2)-sqlite-prep.sql bench/tpch-$(2)-sqlite.sql data/TPC-H-$(1).db bench-sqlite
	./bench-sqlite <(sed 's#TPC-H\.db#data/TPC-H-$(1).db#g' bench/tpch-$(2)-sqlite-prep.sql) 5:bench/tpch-$(2)-sqlite.sql

.PHONY: run-tpch-$(1)-$(2)-etch
run-tpch-$(1)-$(2)-etch: bench-tpch-$(2) data/TPC-H-$(1).db
	./bench-tpch-$(2) data/TPC-H-$(1).db

endef

$(foreach SIZE,x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4,\
	$(foreach QUERY,q5 q9,\
		$(eval $(call TPCH_TEMPLATE,$(SIZE),$(QUERY)))))


.PHONY: clean
clean:
	rm -rf *.o tmp-*.duckdb tmp-sqlite3 sqlite3 out sqlite3.c sqlite3.h duckdb/duckdb

.PHONY: list-benchmarks
list-benchmarks:
	@LC_ALL=C $(MAKE) -pRrq -f $(firstword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/(^|\n)# Files(\n|$$)/,/(^|\n)# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort -V | egrep -v -e '^[^[:alnum:]]' -e '^$@$$' | grep '^run-'
# From https://stackoverflow.com/a/26339924/1937836


.PHONY: lean-streams
lean-streams:
	lake build fusion && perf record -g --cal-graph lbr -o ok .lake/build/bin/fusion 500000
# or, lake build fusion && perf record -g --cal-graph dwarf -o ok .lake/build/bin/fusion 500000
# then, something like: : $> perf script -i ok | stackcollapse-perf.pl | flamegraph.pl > out1.svg
