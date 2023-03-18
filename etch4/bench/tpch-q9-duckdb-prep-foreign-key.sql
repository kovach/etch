---------------- load data into memory



CREATE TABLE NATION  ( N_NATIONKEY  INTEGER NOT NULL,
                            N_NAME       CHAR(25) NOT NULL,
                            PRIMARY KEY (N_NATIONKEY));
CREATE TABLE PART  ( P_PARTKEY     INTEGER NOT NULL,
                          P_NAME        VARCHAR(55) NOT NULL,
                          PRIMARY KEY (P_PARTKEY));
CREATE TABLE SUPPLIER ( S_SUPPKEY     INTEGER NOT NULL,
                             S_NATIONKEY   INTEGER NOT NULL REFERENCES NATION (N_NATIONKEY),
                             PRIMARY KEY (S_SUPPKEY));
CREATE TABLE PARTSUPP ( PS_PARTKEY     INTEGER NOT NULL REFERENCES PART (P_PARTKEY),
                             PS_SUPPKEY     INTEGER NOT NULL REFERENCES SUPPLIER (S_SUPPKEY),
                             PS_SUPPLYCOST  DOUBLE  NOT NULL,
                             PRIMARY KEY (PS_PARTKEY, PS_SUPPKEY));
CREATE TABLE ORDERS  ( O_ORDERKEY       INTEGER NOT NULL,
                           O_ORDERDATE      DATE NOT NULL,
                           PRIMARY KEY (O_ORDERKEY));
CREATE TABLE LINEITEM ( L_ORDERKEY    INTEGER NOT NULL REFERENCES ORDERS (O_ORDERKEY),
                             L_PARTKEY     INTEGER NOT NULL REFERENCES PART (P_PARTKEY),
                             L_SUPPKEY     INTEGER NOT NULL REFERENCES SUPPLIER (S_SUPPKEY),
                             L_LINENUMBER  INTEGER NOT NULL,
                             L_QUANTITY    DOUBLE NOT NULL,
                             L_EXTENDEDPRICE  DOUBLE NOT NULL,
                             L_DISCOUNT    DOUBLE NOT NULL,
                             PRIMARY KEY (L_ORDERKEY, L_LINENUMBER));

COPY NATION   FROM 'tpch-csv-q9/nation.csv'   (HEADER, DELIMITER ',');
COPY PART     FROM 'tpch-csv-q9/part.csv'     (HEADER, DELIMITER ',');
COPY SUPPLIER FROM 'tpch-csv-q9/supplier.csv' (HEADER, DELIMITER ',');
COPY PARTSUPP FROM 'tpch-csv-q9/partsupp.csv' (HEADER, DELIMITER ',');
COPY ORDERS   FROM 'tpch-csv-q9/orders.csv'   (HEADER, DELIMITER ',');
COPY LINEITEM FROM 'tpch-csv-q9/lineitem.csv' (HEADER, DELIMITER ',');

PRAGMA database_size;

PRAGMA threads=1;
