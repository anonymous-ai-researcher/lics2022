import pandas as pd
import numpy as np
now = pd.read_csv(
    'OxfordAnalyse.txt'
,sep=',',index_col = False)
prototype = now[now['isLethe'] == 0]
lethe = now[now['isLethe'] == 1]
maxdepth = now['depthMax'].max()
alldatalethe = []
timeoutlethe = []
alldatapt = []
timeoutpt = []
print("lethe timeout rate in each depth:")
for D in range(1,(int(maxdepth))+1):
    print("depth ",D,":");
    alldata = 0
    timeout = 0
    depth = now[now['depthMax'] == D]
    for index, row in lethe.iterrows():
        if row['fileName'] in  depth['fileName'].values:
            alldata+=1
            if row['timeOut'] == 1:
                timeout+=1 
    print(timeout/alldata)
    alldatalethe.append(alldata)
    timeoutlethe.append(timeout)
print("prototype timeout rate in each depth:")
for D in range(1,(int(maxdepth))+1):
    print("depth ",D,":");
    alldata = 0
    timeout = 0
    depth = now[now['depthMax'] == D]
    for index, row in prototype.iterrows():
        if row['fileName'] in  depth['fileName'].values:
            alldata+=1
            if row['timeOut'] == 1:
                timeout+=1 
    print(timeout/alldata)
    alldatapt.append(alldata)
    timeoutpt.append(timeout)  
print("the rate of maxdepth:")
testNum = sum(alldatalethe)
for index,i in enumerate(alldatalethe):
    print("max depth " , index ," rate:", i/testNum)