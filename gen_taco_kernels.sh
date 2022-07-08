#$cmd -prefix="ttv_" -print-nocolor -print-evaluate "out = A(i,j,k)*V(k)" -f=A:sss -f=V:s -s="reorder(i,j,k)" > ttv.cpp
cmd=/home/scott/Dropbox/2022/taco/build/bin/taco
# $cmd -prefix="ttv_" -print-nocolor "out = C(i,j,k)*V(k)" -f=C:sss -f=V:s -s="reorder(i,j,k)" > ttv.cpp
# $cmd -prefix="ttm_" -print-nocolor "out = C(i,j,l)*A(k,l)" -f=C:sss -f=A:ss -s="reorder(i,j,k,l)" > ttm.cpp
# $cmd -prefix="mttkrp_" -print-nocolor "out = C(i,j,k)*A(j,l)*B(k,l)" -f=C:sss -f=A:ss -f=B:ss -s="reorder(i,j,k,l)" > mttkrp.cpp
# $cmd -prefix="inner3_" -print-nocolor "out = C(i,j,k)*D(i,j,k)" -f=C:sss -f=D:sss -s="reorder(i,j,k)" > inner3.cpp
# $cmd -prefix="mmul2_" -print-nocolor "out = A(i,k)*B(j,k)" -f=A:ss -f=B:ss -s="reorder(i,j,k)" > mmul2.cpp
