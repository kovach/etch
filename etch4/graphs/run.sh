mkdir -p bench-output
for size in x0.01 x0.025 x0.05 x0.1 x0.25 x0.5 x1 x2 x4; do
	for db in duckdb duckdbforeign etch sqlite; do
		# warm up
		# echo run-tpch-$size-q5-$db time -2
		make run-tpch-$size-q5-$db >/dev/null
		# echo run-tpch-$size-q5-$db time -1
		make run-tpch-$size-q5-$db >/dev/null

		rm -f bench-output/run-tpch-$size-q5-$db.txt
		for i in `seq 5`; do
			# echo run-tpch-$size-q5-$db time $i
			make run-tpch-$size-q5-$db >>bench-output/run-tpch-$size-q5-$db.txt
		done
	done
	echo run-tpch-$size-q5
	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-duckdb.txt | awk '{x+=$0}END{print "duckdb:",x/NR}'
	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-duckdbforeign.txt | awk '{x+=$0}END{print "duckdbforeign:",x/NR}'
	sed -n 's/q5 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-etch.txt | awk '{x+=$0}END{print "etch:",x/NR}'
	sed -n 's/q2 took (s): real \([^ ]*\)s.*/\1/p' <bench-output/run-tpch-$size-q5-sqlite.txt | awk '{x+=$0}END{print "sqlite:",x/NR}'
done
