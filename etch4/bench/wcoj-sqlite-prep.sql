CREATE TABLE R (A INTEGER NOT NULL,
                B INTEGER NOT NULL,
                PRIMARY KEY (A, B));
CREATE TABLE S (B INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (B, C));
CREATE TABLE T (A INTEGER NOT NULL,
                C INTEGER NOT NULL,
                PRIMARY KEY (A, C));

ATTACH DATABASE 'wcoj.db' AS orig;

INSERT INTO R
SELECT a, b
FROM orig.R;

INSERT INTO S
SELECT b, c
FROM orig.S;

INSERT INTO T
SELECT a, c
FROM orig.T;

DETACH DATABASE orig;

SELECT page_count * page_size as size
FROM pragma_page_count(), pragma_page_size();
