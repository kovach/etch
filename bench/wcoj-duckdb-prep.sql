CREATE TABLE R (A INTEGER NOT NULL,
                B INTEGER NOT NULL,
                PRIMARY KEY (A, B));
CREATE TABLE S (B INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (B, C));
CREATE TABLE T (A INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (A, C));

COPY R   FROM 'wcoj-csv/r.csv'   (HEADER, DELIMITER ',');
COPY S   FROM 'wcoj-csv/s.csv'   (HEADER, DELIMITER ',');
COPY T   FROM 'wcoj-csv/t.csv'   (HEADER, DELIMITER ',');

PRAGMA database_size;

PRAGMA threads=1;
