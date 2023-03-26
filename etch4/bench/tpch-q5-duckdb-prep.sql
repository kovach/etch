---------------- load data into memory


CREATE TABLE REGION  ( R_REGIONKEY  INTEGER NOT NULL,
                            R_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (R_REGIONKEY));
CREATE TABLE NATION  ( N_NATIONKEY  INTEGER NOT NULL,
                            N_REGIONKEY  INTEGER NOT NULL,
                            N_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (N_NATIONKEY));
CREATE TABLE SUPPLIER ( S_SUPPKEY     INTEGER NOT NULL,
                             S_NATIONKEY   INTEGER NOT NULL,
                             PRIMARY KEY (S_SUPPKEY));
CREATE TABLE CUSTOMER ( C_CUSTKEY     INTEGER NOT NULL,
                             C_NATIONKEY   INTEGER NOT NULL,
                             PRIMARY KEY (C_CUSTKEY));
CREATE TABLE ORDERS  ( O_ORDERKEY       INTEGER NOT NULL,
                           O_CUSTKEY        INTEGER NOT NULL,
                           O_ORDERDATE      DATE NOT NULL,
                           PRIMARY KEY (O_ORDERKEY));
CREATE TABLE LINEITEM ( L_ORDERKEY    INTEGER NOT NULL,
                             L_SUPPKEY     INTEGER NOT NULL,
                             L_LINENUMBER  INTEGER NOT NULL,
                             L_EXTENDEDPRICE  DOUBLE NOT NULL, -- actually DECIMAL(15,2), but etch uses double
                             L_DISCOUNT    DOUBLE NOT NULL,
                             PRIMARY KEY (L_ORDERKEY, L_LINENUMBER));

-- Note: adding these indices (and also the ORDER BY in INSERT) don't help DuckDB, but we do it out of fairness.

CREATE INDEX REGION_idx_q5 ON REGION(R_REGIONKEY, R_NAME);
CREATE INDEX NATION_idx_q5 ON NATION(N_NATIONKEY, N_REGIONKEY, N_NAME);
CREATE INDEX SUPPLIER_idx_q5 ON SUPPLIER(S_SUPPKEY, S_NATIONKEY);
CREATE INDEX ORDERS_idx_q5 ON ORDERS(O_ORDERKEY, O_ORDERDATE, O_CUSTKEY);
CREATE INDEX CUSTOMER_idx_q5 ON CUSTOMER(C_CUSTKEY, C_NATIONKEY);
CREATE INDEX LINEITEM_idx_q5 ON LINEITEM(L_ORDERKEY, L_SUPPKEY, L_EXTENDEDPRICE, L_DISCOUNT);

INSERT INTO REGION
SELECT R_REGIONKEY, R_NAME
FROM read_csv_auto('tpch-csv/region.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO NATION
SELECT N_NATIONKEY, N_REGIONKEY, N_NAME
FROM read_csv_auto('tpch-csv/nation.csv', delim=',', header=True)
ORDER BY 1, 2, 3;

INSERT INTO SUPPLIER
SELECT S_SUPPKEY, S_NATIONKEY
FROM read_csv_auto('tpch-csv/supplier.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO CUSTOMER
SELECT C_CUSTKEY, C_NATIONKEY
FROM read_csv_auto('tpch-csv/customer.csv', delim=',', header=True)
ORDER BY 1, 2;

INSERT INTO ORDERS
SELECT O_ORDERKEY, O_CUSTKEY, O_ORDERDATE
FROM read_csv_auto('tpch-csv/orders.csv', delim=',', header=True)
ORDER BY 1, 2, 3;

INSERT INTO LINEITEM
SELECT L_ORDERKEY, L_SUPPKEY, L_LINENUMBER, L_EXTENDEDPRICE, L_DISCOUNT
FROM read_csv_auto('tpch-csv/lineitem.csv', delim=',', header=True)
ORDER BY 1, 2, 3, 4, 5;

PRAGMA database_size;

PRAGMA threads=1;
