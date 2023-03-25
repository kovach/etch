---------------- load data into memory


CREATE TABLE NATION  ( N_NATIONKEY  INTEGER NOT NULL,
                            N_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (N_NATIONKEY));
CREATE TABLE PART  ( P_PARTKEY     INTEGER NOT NULL,
                          P_NAME        VARCHAR(55) NOT NULL,
                          PRIMARY KEY (P_PARTKEY));
CREATE TABLE SUPPLIER ( S_SUPPKEY     INTEGER NOT NULL,
                             S_NATIONKEY   INTEGER NOT NULL,
                             PRIMARY KEY (S_SUPPKEY));
CREATE TABLE PARTSUPP ( PS_PARTKEY     INTEGER NOT NULL,
                             PS_SUPPKEY     INTEGER NOT NULL,
                             PS_SUPPLYCOST  DOUBLE  NOT NULL,
                             PRIMARY KEY (PS_PARTKEY, PS_SUPPKEY));
CREATE TABLE ORDERS  ( O_ORDERKEY       INTEGER NOT NULL,
                           O_ORDERDATE      DATE NOT NULL,
                           PRIMARY KEY (O_ORDERKEY));
CREATE TABLE LINEITEM ( L_PARTKEY     INTEGER NOT NULL,
                             L_SUPPKEY     INTEGER NOT NULL,
                             L_ORDERKEY    INTEGER NOT NULL,
                             L_LINENUMBER  INTEGER NOT NULL,
                             L_QUANTITY    DOUBLE NOT NULL,
                             L_EXTENDEDPRICE  DOUBLE NOT NULL,
                             L_DISCOUNT    DOUBLE NOT NULL,
                             PRIMARY KEY (L_ORDERKEY, L_LINENUMBER));

CREATE INDEX LINEITEM_idx_q9 ON LINEITEM(L_PARTKEY, L_SUPPKEY, L_ORDERKEY, L_QUANTITY, L_EXTENDEDPRICE, L_DISCOUNT);
CREATE INDEX PART_idx_q9 ON PART(P_PARTKEY, P_NAME);
CREATE INDEX ORDERS_idx_q9 ON ORDERS(O_ORDERKEY, O_ORDERDATE);
CREATE INDEX SUPPLIER_idx_q9 ON SUPPLIER(S_SUPPKEY, S_NATIONKEY);
CREATE INDEX PARTSUPP_idx_q9 ON PARTSUPP(PS_PARTKEY, PS_SUPPKEY, PS_SUPPLYCOST);
CREATE INDEX NATION_idx_q9 ON NATION(N_NATIONKEY, N_NAME);

INSERT INTO NATION
SELECT N_NATIONKEY, N_NAME
FROM read_csv_auto('tpch-csv/nation.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO PART
SELECT P_PARTKEY, P_NAME
FROM read_csv_auto('tpch-csv/part.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO SUPPLIER
SELECT S_SUPPKEY, S_NATIONKEY
FROM read_csv_auto('tpch-csv/supplier.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO PARTSUPP
SELECT PS_PARTKEY, PS_SUPPKEY, PS_SUPPLYCOST
FROM read_csv_auto('tpch-csv/partsupp.csv', delim=',', header=True)
ORDER BY 1, 2, 3;

INSERT INTO ORDERS
SELECT O_ORDERKEY, O_ORDERDATE
FROM read_csv_auto('tpch-csv/orders.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO LINEITEM
SELECT L_PARTKEY, L_SUPPKEY, L_ORDERKEY, L_LINENUMBER, L_QUANTITY, L_EXTENDEDPRICE, L_DISCOUNT
FROM read_csv_auto('tpch-csv/lineitem.csv', delim=',', header=True)
ORDER BY 1, 2, 3, 5, 6, 7;

PRAGMA database_size;

PRAGMA threads=1;
