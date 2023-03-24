mkdir -p bench-output

(for size in 0.01 0.03 0.1 0.3 0.5 0.7 0.9; do
	echo data/taco-s$size.db
done) | xargs make -j$(nproc)

# for size in 0.01 0.03 0.1 0.3 0.5 0.7 0.9; do
for size in 0.01 0.03 0.1; do
	echo $size
	make run-taco-s$size >/dev/null

	rm -f bench-output/run-taco-s$size.txt
	for i in `seq 5`; do
		make run-taco-s$size >>bench-output/run-taco-s$size.txt
	done
done

# for size in x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4; do
# 	for db in duckdb duckdbforeign etch sqlite; do
# 		# warm up
# 		# echo run-tpch-$size-q5-$db time -2
# 		make run-tpch-$size-q5-$db >/dev/null
# 		# echo run-tpch-$size-q5-$db time -1
# 		make run-tpch-$size-q5-$db >/dev/null
# 
# 		rm -f bench-output/run-tpch-$size-q5-$db.txt
# 		for i in `seq 5`; do
# 			# echo run-tpch-$size-q5-$db time $i
# 			make run-tpch-$size-q5-$db >>bench-output/run-tpch-$size-q5-$db.txt
# 		done
# 	done
# 	echo run-tpch-$size-q5
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-duckdb.txt | awk '{x+=$0}END{print "duckdb:",x/NR}'
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-duckdbforeign.txt | awk '{x+=$0}END{print "duckdbforeign:",x/NR}'
# 	sed -n 's/q5 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-etch.txt | awk '{x+=$0}END{print "etch:",x/NR}'
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-sqlite.txt | awk '{x+=$0}END{print "sqlite:",x/NR}'
# done
# 
# for size in x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4; do
# 	for db in duckdb duckdbforeign etch sqlite; do
# 		# warm up
# 		# echo run-tpch-$size-q9-$db time -2
# 		make run-tpch-$size-q9-$db >/dev/null
# 		# echo run-tpch-$size-q9-$db time -1
# 		make run-tpch-$size-q9-$db >/dev/null
# 
# 		rm -f bench-output/run-tpch-$size-q9-$db.txt
# 		for i in `seq 5`; do
# 			# echo run-tpch-$size-q9-$db time $i
# 			make run-tpch-$size-q9-$db >>bench-output/run-tpch-$size-q9-$db.txt
# 		done
# 	done
# 	echo run-tpch-$size-q9
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q9-duckdb.txt | awk '{x+=$0}END{print "duckdb:",x/NR}'
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q9-duckdbforeign.txt | awk '{x+=$0}END{print "duckdbforeign:",x/NR}'
# 	sed -n 's/q9 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q9-etch.txt | awk '{x+=$0}END{print "etch:",x/NR}'
# 	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q9-sqlite.txt | awk '{x+=$0}END{print "sqlite:",x/NR}'
# done
