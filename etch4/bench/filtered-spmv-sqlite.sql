SELECT SUM(A.v * V.v)
FROM A, V
WHERE V.v >= 0.8 AND A.i == V.i;
