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

COPY REGION   FROM 'tpch-csv-q5/region.csv'   (HEADER TRUE, DELIMITER ',');
COPY NATION   FROM 'tpch-csv-q5/nation.csv'   (HEADER TRUE, DELIMITER ',');
COPY SUPPLIER FROM 'tpch-csv-q5/supplier.csv' (HEADER TRUE, DELIMITER ',');
COPY CUSTOMER FROM 'tpch-csv-q5/customer.csv' (HEADER TRUE, DELIMITER ',');
COPY ORDERS   FROM 'tpch-csv-q5/orders.csv'   (HEADER TRUE, DELIMITER ',');
COPY LINEITEM FROM 'tpch-csv-q5/lineitem.csv' (HEADER TRUE, DELIMITER ',');

PRAGMA database_size;

PRAGMA threads=1;
