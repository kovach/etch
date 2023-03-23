import sqlite3
#import random
#from scipy.sparse import csr_matrix
#import scipy.sparse
import numpy as np
from matplotlib import pyplot as plt
import subprocess

def commit(c, r, s, t):
    c.execute('delete from r')
    c.executemany(f'INSERT INTO r VALUES(?,?)', r)
    c.execute('delete from s')
    c.executemany(f'INSERT INTO s VALUES(?,?)', s)
    c.execute('delete from t')
    c.executemany(f'INSERT INTO t VALUES(?,?)', t)
    c.commit()

def makeV(n = 100, p = 0.1):
    result = set()
    m = np.random.rand(n)
    it = np.nditer(m, flags=['multi_index'])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), float(i)))
    return result

def makeA(n = 100, p = 0.1):
    result = set()
    m = np.random.rand(n, n)
    it = np.nditer(m, flags=['multi_index'])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), int(it.multi_index[1]), float(i)))
    return result

def makeC(n = 100, p = 0.1):
    result = set()
    m = np.random.rand(n, n, n)
    it = np.nditer(m, flags=['multi_index'])
    for i in it:
        if i < p:
            result.add((int(it.multi_index[0]), int(it.multi_index[1]), int(it.multi_index[2]), float(i)))
    return result

def fig(scales, sql, se, etch):
    def norm(arr):
        return np.array(arr)/arr[-1]
    def norm2(arr, s):
        return np.array(arr)/arr[-1]*s
    etch_reps = 5000
    sql_reps = 2
    etch = np.array(etch) / etch_reps
    sql = np.array(sql) / sql_reps
    plt.plot(scales, norm(scales**2)*sql[-1], label='n^2')
    plt.plot(scales, (sql), label='sqlite')
    plt.plot(se, norm(se**(1.0))*etch[-1], label='n^1')
    plt.plot(se, (etch), label='etch')
    #plt.plot(scales, norm(sql), label='sqlite')
    #plt.plot(se, norm(etch)*2, label='etch')
    #plt.plot(se, norm(np.array(se**(1.0)))*2, label='n^1')
    #plt.plot(scales, norm(np.array(scales**2)), label='n^2')
    plt.xscale('log')
    plt.yscale('log')
    plt.legend()
    plt.savefig('wcoj_scaling.pdf')

def parse_stdout(b):
    return [int(x) for x in b.decode().strip().split('\n')]
    #return int(b.decode())
def main_no():
    global con
    con = sqlite3.connect("./data/pldi.db")
    print("\n\n\n/*** START TEST ***/")
    print("   this tests ETCH's scaling for the triangle query.");
    print("   cf: Figure 14: Worst-case optimal join");
    #for sn in [10, 20]:
    results = []
    #scales = [10,20,30,40,50,60,70,80,90,100]
    scales = np.array([70,80,90,100,110,120 ,130,140,150,160,170,180])*8
    #scales = s
    for sn in scales:
        print(sn, ":")
        go_(con, sn)
        #print(list(con.execute('select count(*) from r')))
        pair = parse_stdout(subprocess.check_output('./wcoj'))
        results.append(pair)
    return (scales, results)

def main():
    #r = makeA()
    c = sqlite3.connect("./data/pldi.db")
    c.execute('CREATE TABLE if not exists A(i, j, v)')
    c.execute('CREATE TABLE if not exists B(i, j, v)')
    c.execute('CREATE TABLE if not exists C(i, j, k, v)')
    c.execute('CREATE TABLE if not exists V(i, v)')
    c.execute('delete from A')
    c.execute('delete from B')
    c.execute('delete from C')
    c.execute('delete from V')
    print("A")
    c.executemany(f'insert into A values(?,?,?)', makeA(1000))
    print("B")
    c.executemany(f'insert into B values(?,?,?)', makeA(1000))
    print("C")
    c.executemany(f'insert into C values(?,?,?,?)', makeC(100))
    print("V")
    c.executemany(f'insert into V values(?,?)', makeV(1000))
    c.commit()

def foo():
    result = subprocess.check_output(["echo", "22"])
    print(int(result))


main()
