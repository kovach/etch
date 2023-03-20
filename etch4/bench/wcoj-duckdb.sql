-- for a description of this join problem see https://arxiv.org/pdf/1310.3314.pdf, Figure 2

SELECT COUNT(*)
FROM r, s, t
WHERE r.a = t.a AND r.b = s.b AND s.c = t.c;
