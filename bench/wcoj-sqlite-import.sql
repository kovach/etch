CREATE TABLE R (A INTEGER NOT NULL,
                B INTEGER NOT NULL,
                PRIMARY KEY (A, B));
CREATE TABLE S (B INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (B, C));
CREATE TABLE T (A INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (A, C));

.mode csv
.import wcoj-csv/r.csv R
.import wcoj-csv/s.csv S
.import wcoj-csv/t.csv T
