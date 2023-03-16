.timer on

select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;

select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;

select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;

select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;

select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;

EXPLAIN QUERY PLAN
select
 n_name,
 sum(l_extendedprice * (1 - l_discount)) as revenue
from
  customer,
  orders,
  lineitem,
  supplier,
  nation,
  region
where
  c_custkey = o_custkey
  and l_orderkey = o_orderkey
  and l_suppkey = s_suppkey
  and c_nationkey = s_nationkey
  and s_nationkey = n_nationkey
  and n_regionkey = r_regionkey
  and r_name = 'ASIA'
  and unixepoch(o_orderdate, 'utc') >= unixepoch('1994-01-01', 'utc')
  and unixepoch(o_orderdate, 'utc') < unixepoch('1995-01-01', 'utc')
group by
 n_name;
