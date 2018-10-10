def Calmi(partition):
    temp=uniq(partition);
    n=len(partition);
    m=len(temp);
    count=1;
    for i in range(m):
        a=partition.count(temp[i]);
        count=count*factorial(a);
    return count;

def listexp(list1,list2):
    n=len(list1);
    re=[list1[i]^list2[i] for i in range(n)];
    return prod(re[i] for i in range(n));

def positionlist(list,element):
    ind=0;
    re=0;
    if element not in list:
        re=-1;
    if re!=-1:
        n=len(list);
        for i in range(n):
            if list[i]==element:
                re=i;
                break;
    return re;

def removeelement(list,element):
    n=len(list);
    re=[];
    for i in range(n):
        if list[i]!=element:
            re=re+[list[i]];
    return re

def MZonal(partition,variables):
    ind=0;
    re=0;
    m=len(partition);
    n=len(variables);
    if n<m:
        ind=1;
    if ind==0:
        perm=Permutations(n,m).list();
        for i in range(len(perm)): 
            temp=[variables[j-1] for j in perm[i]];
            re=re+listexp(temp,partition);  
    re=re/Calmi(partition);    
    return re;

def coeffi(k,l):
    re=0;
    n=sum(k);
    m=len(l);
    wholelist=Partitions(n).list();
    if k==l and len(k)==1:
        re=1;
    else:
        if k==l:
            t=positionlist(wholelist,l);
            pt=multinomial(l);
            xx=[n];
            for xx in wholelist[:t]:
                re=coeffi(xx,l)+re;
            re=pt-re;
        else:
            table=SumVariable(k,l);
            rho=RHO(k)-RHO(l);
            xx=[n];
            for xx in table:
                temp=[xx[i]-l[i] for i in xrange(m)];
                y=removeelement(xx,0);
                y=sorted(y,reverse=1);
                t=uniq(temp);
                t=t[-1];
                a=positionlist(temp,t);
                b=positionlist(temp,-t);
                temp=l[a]-l[b]+2*t;
                re=re+temp*coeffi(k,y);
            re=re/rho;
    return re;

def RHO(partition):
    n=len(partition);
    re=sum(partition[i]*(partition[i]-i-1) for i in range(n));
    return re;

def SumVariable(k,l):
    n=sum(k);
    whole=Partitions(n).list();
    m=len(l);
    a=positionlist(whole,k);
    b=positionlist(whole,l);
    i=0;
    table2=Tuples([i for i in range(n+1)],m);
    table3=[i for i in table2 if sum(i)==n];
    re=[];
    x=l;
    for x in table3:
        q=sorted(x,reverse=1);
        q=removeelement(q,0);
        p=positionlist(whole,q);
        q=[x[i]-l[i] for i in range(m)];
        q=removeelement(q,0);
        if a<=p<b and q[0]>0 and len(q)==2:
            re=re+[x];
    return re;

def CZonal(part,vari):
    n=sum(part);
    table=Partitions(n).list();
    position=positionlist(table,part);
    temp=table[position:];
    re=sum(coeffi(part,list(i))*MZonal(list(i),vari) for i in temp);
    return re;
