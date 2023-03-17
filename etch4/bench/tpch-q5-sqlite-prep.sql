.echo on

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

CREATE INDEX REGION_idx_q5 ON REGION(R_REGIONKEY, R_NAME);
CREATE INDEX NATION_idx_q5 ON NATION(N_NATIONKEY, N_REGIONKEY, N_NAME);
CREATE INDEX SUPPLIER_idx_q5 ON SUPPLIER(S_SUPPKEY, S_NATIONKEY);
CREATE INDEX ORDERS_idx_q5 ON ORDERS(O_ORDERKEY, O_ORDERDATE, O_CUSTKEY);
CREATE INDEX CUSTOMER_idx_q5 ON CUSTOMER(C_CUSTKEY, C_NATIONKEY);
CREATE INDEX LINEITEM_idx_q5 ON LINEITEM(L_ORDERKEY, L_SUPPKEY, L_EXTENDEDPRICE, L_DISCOUNT);

ATTACH DATABASE 'TPC-H.db' AS t;

INSERT INTO region
SELECT r_regionkey, r_name
FROM t.region;

INSERT INTO nation
SELECT n_nationkey, n_regionkey, n_name
FROM t.nation;

INSERT INTO supplier
SELECT s_suppkey, s_nationkey
FROM t.supplier;

INSERT INTO customer
SELECT c_custkey, c_nationkey
FROM t.customer;

INSERT INTO orders
SELECT o_orderkey, o_custkey, o_orderdate
FROM t.orders;

INSERT INTO lineitem
SELECT l_orderkey, l_suppkey, l_linenumber, l_extendedprice, l_discount
FROM t.lineitem;

DETACH DATABASE t;

SELECT page_count * page_size as size
FROM pragma_page_count(), pragma_page_size();
