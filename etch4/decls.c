// sorry

int size[] = {0,0};

ind* out1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* out1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* out2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* out2_pos = (ind*)calloc(array_size, sizeof(ind));
num* out_vals = (num*)calloc(array_size, sizeof(num));
int  out1_i = -1;
int  out2_i = -1;
ind  _out = 0;

ind* C1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* C2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C2_pos = (ind*)calloc(array_size, sizeof(ind));
ind* C3_crd = (ind*)calloc(array_size, sizeof(ind));
ind* C3_pos = (ind*)calloc(array_size, sizeof(ind));
num*   C_vals = (num*)calloc(array_size, sizeof(num));
int C1_i = -1;
int C2_i = -1;
ind _C = 0;

ind* ssA1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssA1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssA2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssA2_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssA_vals = (num*)calloc(array_size, sizeof(num));
int  ssA1_i = -1;
int  ssA2_i = -1;
ind  ss_A = 0;

ind* dsA1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsA1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsA2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsA2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsA_vals = (num*)calloc(array_size, sizeof(num));
int  dsA1_i = -1;
int  dsA2_i = -1;
ind  ds_A = 0;

ind* ssB1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssB1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* ssB2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* ssB2_pos = (ind*)calloc(array_size, sizeof(ind));
num* ssB_vals = (num*)calloc(array_size, sizeof(num));
int  ssB1_i = -1;
int  ssB2_i = -1;
ind  ss_B = 0;

ind* dsB1_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsB1_pos = (ind*)calloc(array_size, sizeof(ind));
ind* dsB2_crd = (ind*)calloc(array_size, sizeof(ind));
ind* dsB2_pos = (ind*)calloc(array_size, sizeof(ind));
num* dsB_vals = (num*)calloc(array_size, sizeof(num));
int  dsB1_i = -1;
int  dsB2_i = -1;
ind  ds_B = 0;

int  A1_dimension = 10000;
ind* A1_crd;
ind* A1_pos;
ind* A2_crd;
ind* A2_pos;
num* A_vals;
int  A1_i = -1;
int  A2_i = -1;
ind  _A = 0;

int  B1_dimension = 10000;
ind* B1_crd;
ind* B1_pos;
ind* B2_crd;
ind* B2_pos;
num* B_vals;
int  B1_i = -1;
int  B2_i = -1;
ind  _B = 0;

void load_ssA() {
A1_crd = ssA1_crd;
A1_pos = ssA1_pos;
A2_crd = ssA2_crd;
A2_pos = ssA2_pos;
A_vals = ssA_vals;
A1_i = -1;
A2_i = -1;
_A = 0;
}

void load_dsA() {
A1_crd = dsA1_crd;
A1_pos = dsA1_pos;
A2_crd = dsA2_crd;
A2_pos = dsA2_pos;
A_vals = dsA_vals;
A1_i = -1;
A2_i = -1;
_A = 0;
}

void load_ssB() {
B1_crd = ssB1_crd;
B1_pos = ssB1_pos;
B2_crd = ssB2_crd;
B2_pos = ssB2_pos;
B_vals = ssB_vals;
B1_i = -1;
B2_i = -1;
_B = 0;
}
void load_dsB() {
B1_crd = dsB1_crd;
B1_pos = dsB1_pos;
B2_crd = dsB2_crd;
B2_pos = dsB2_pos;
B_vals = dsB_vals;
B1_i = -1;
B2_i = -1;
_B = 0;
}
