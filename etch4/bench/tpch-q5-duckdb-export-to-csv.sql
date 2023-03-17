-- Load TPC-H dataset for Query 5

.echo on

INSTALL sqlite;
LOAD sqlite;

SET GLOBAL sqlite_all_varchar=true;

CREATE TABLE REGION  ( R_REGIONKEY  INTEGER NOT NULL,
                            R_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (R_REGIONKEY));
CREATE TABLE NATION  ( N_NATIONKEY  INTEGER NOT NULL,
                            N_REGIONKEY  INTEGER NOT NULL REFERENCES REGION (R_REGIONKEY),
                            N_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (N_NATIONKEY));
CREATE TABLE SUPPLIER ( S_SUPPKEY     INTEGER NOT NULL,
                             S_NATIONKEY   INTEGER NOT NULL REFERENCES NATION (N_NATIONKEY),
                             PRIMARY KEY (S_SUPPKEY));
CREATE TABLE CUSTOMER ( C_CUSTKEY     INTEGER NOT NULL,
                             C_NATIONKEY   INTEGER NOT NULL REFERENCES NATION (N_NATIONKEY),
                             PRIMARY KEY (C_CUSTKEY));
CREATE TABLE ORDERS  ( O_ORDERKEY       INTEGER NOT NULL,
                           O_CUSTKEY        INTEGER NOT NULL REFERENCES CUSTOMER (C_CUSTKEY),
                           O_ORDERDATE      DATE NOT NULL,
                           PRIMARY KEY (O_ORDERKEY));
CREATE TABLE LINEITEM ( L_ORDERKEY    INTEGER NOT NULL,
                             L_SUPPKEY     INTEGER NOT NULL REFERENCES SUPPLIER (S_SUPPKEY),
                             L_LINENUMBER  INTEGER NOT NULL,
                             L_EXTENDEDPRICE  DOUBLE NOT NULL, -- actually DECIMAL(15,2), but etch uses double
                             L_DISCOUNT    DOUBLE NOT NULL,
                             PRIMARY KEY (L_ORDERKEY, L_LINENUMBER));

INSERT INTO REGION
SELECT R_REGIONKEY, R_NAME FROM sqlite_scan('TPC-H.db', 'REGION');

INSERT INTO NATION
SELECT N_NATIONKEY, N_REGIONKEY, N_NAME FROM sqlite_scan('TPC-H.db', 'NATION');

INSERT INTO SUPPLIER
SELECT S_SUPPKEY, S_NATIONKEY FROM sqlite_scan('TPC-H.db', 'SUPPLIER');

INSERT INTO CUSTOMER
SELECT C_CUSTKEY, C_NATIONKEY FROM sqlite_scan('TPC-H.db', 'CUSTOMER');

INSERT INTO ORDERS
SELECT O_ORDERKEY, O_CUSTKEY, O_ORDERDATE FROM sqlite_scan('TPC-H.db', 'ORDERS');

INSERT INTO LINEITEM
SELECT L_ORDERKEY, L_SUPPKEY, L_LINENUMBER, L_EXTENDEDPRICE, L_DISCOUNT FROM sqlite_scan('TPC-H.db', 'LINEITEM');

COPY REGION   TO 'tpch-csv/region.csv'   (HEADER, DELIMITER ',');
COPY NATION   TO 'tpch-csv/nation.csv'   (HEADER, DELIMITER ',');
COPY SUPPLIER TO 'tpch-csv/supplier.csv' (HEADER, DELIMITER ',');
COPY CUSTOMER TO 'tpch-csv/customer.csv' (HEADER, DELIMITER ',');
COPY ORDERS   TO 'tpch-csv/orders.csv'   (HEADER, DELIMITER ',');
COPY LINEITEM TO 'tpch-csv/lineitem.csv' (HEADER, DELIMITER ',');
