INSTALL sqlite;
LOAD sqlite;

CREATE TABLE A (I INTEGER NOT NULL,
                J INTEGER NOT NULL,
                V REAL NOT NULL,
                PRIMARY KEY (I, J));
CREATE TABLE V (I INTEGER NOT NULL,
                V REAL NOT NULL,
                PRIMARY KEY (I));

INSERT INTO A
SELECT *
FROM sqlite_scan('data/filtered-spmv-2000000.db', 'A')
ORDER BY I, J;

INSERT INTO V
SELECT *
FROM sqlite_scan('data/filtered-spmv-2000000.db', 'V')
ORDER BY I;
