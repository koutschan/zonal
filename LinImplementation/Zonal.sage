#First of all, we define some useful functions that help in the computation#

def Calmi(p):                         
    """
    For a paritition p with m_1 1's, m_2 2's and etc, return (m_1)!(m_2)!...(m_l)!. 
    This is the reciprocal of the leading coefficient of M-polynomial in (3.2)
    
    For example, 
    """
##
#Calmi is short for "Calculating 


    t=Partition(p).to_exp()           #exponential form of the partition {m_1,m_2,...}#
    re=prod(factorial(i) for i in t)  #re=(m_1)!(m_2)!...(m_l)!#
    return re;                        #return the product.#

def listexp(list1,list2):                       #Given two lists of same length, say {a_1,a_2,...,a_n} and {b_1,b_2,...,b_n} return (a_1)^(b_1)(a_2)^(b_2)...(a_n)^(b_n)#
    n=len(list1);       
    re=[list1[i]^list2[i] for i in range(n)];
    return prod(i for i in re);

def positionlist(list,element):      #Given a list and an element, find the (first) position of the element in the list. If the element does not belong to the list, return -1.#
    re=0;                            #Give value 0 to re, short for return.#
    if element not in list:          #If the element is not in the list, re=-1#
        re=-1;
    if re!=-1:                       #If re is not -1, proceed to find its first position.#
        n=len(list);                 #n=length of the list#
        for i in range(n):
            if list[i]==element:     #Break at the first time list[i]=element and re=i, the position#
                re=i;
                break;
    return re;

def removeelement(list,element):     #Given a list and an element, remove this element (completely if appearing multiple times) from this list.#
    re=[];                           #re: return#
    for i in list:                   #Let i run elements in the list#
        if i!=element:               #If i is not the elememt#
            re=re+[i];               #Add i to the end of re#
    return re;

def MZonal(partition,variables):              #Computing M-polynomial by (3.2)#
    ind=0;                                    #index is 0 or 1. If ind=1, this means there are more parts in the partition than the number of variable. Thus return 0.#
    re=0;                                     #return#
    m=len(partition);                         #m=length of partition#
    n=len(variables);                         #n=number of variables#
    if n<m:                                   #If n<m, index is 1 and return 0#
        ind=1;
    if ind==0:                                #If index is 0, not 1, continue to compute.#
        perm=Permutations(n,m).list();        #By (3.2), for the summation part, we choose all posible combination of the variables for the summand#
        for i in perm:                        #For each summmand,#
            temp=[variables[j-1] for j in i]; #pick the right combination of the variables#
            re=re+listexp(temp,partition);    #Get the term (y_1)^(\lambda_1)(y_2)^(\lambda_2)...(y_m)^(\lambda_m)#
    re=re/Calmi(partition);                   #Divide the sum by the leading coefficient.#
    return re;


#After computing M-polynomials, we now apply (3.3), (3.4), and (3.5) to compute C-polynomials.#
#First of all, given a parition, \lambda, (3.4) requires to compute \rho_{\lambda}.#

def RHO(partition):              #Given a partition, compute the value \rho by formula (2.1). Note that position in Sage begins from 0, explaining the "-i-1" instead of "-i" in (2.1)#
    n=len(partition);
    return sum(partition[i]*(partition[i]-i-1) for i in range(n));


#Next, in order to use (3.4), we first list all the possible \mu's that appear in the sum.#

def SumVariable(k,l):                             #Given two partitions k and l, for all the possible \mu's in the sum of (3.4), it returns [\lamda_i-\lambda_j+2t,\mu].#
    n=sum(k);                                     #k and l are partitions of n#
    m=len(l);                                     #m=length of partition l.#
    re=[];                                        #return#
    for i in range(m-1):
        for j in range(i+1,m):                    #(i,j) runs over all pars with i<j, correspondng to \lambda_i and \lambda_j of \mu#
            for t in range(1,l[j]+1):             #t=1,2,...,\lambda_j#
                tem=[a for a in l];
                tem[i]=tem[i]+t;
                tem[j]=tem[j]-t;
                tem=sorted(tem,reverse=true);   #Reorder temp#
                tem=removeelement(tem,0);       #remove all zeros#
                if tem>l and tem<=k:
                    re=re+[[l[i]-l[j]+2*t,tem]];
    return re;

#Now, we can apply (3.4) to compute coefficient c_{\kappa,\lambda}

#Based on the recurrence, strategy and properties of c_{\kappa,\lambda}, it is obvious that to compute c_{\kappa,\lambda}, all coefficients c_{\eta,\kappa} for all \eta>=\kappa need to be computed, which is an upper triangle#

#Modification after Christoph's suggestion. By Lemma 7.2.3 of Muirhead's book, for c_{\kappa,\lambda}=, if \lambda has less part than \kappa.#

def COE(k):                            #Given partition k, return c_{k,k}#
    n=sum(k);                          #k is a partition of n#
    whole=Partitions(n).list();        #list of partitions of n#
    count=0;
    partiallist=[];                    #list of all partitions l such that l>=k and l does not have more parts than k (otherwise, c_{l,k}=0#
    partial2=[];
    while whole[count]>k:
        if len(whole[count])<=len(k):  #Only count partitions that do not have more parts than k#
            partiallist=partiallist+[[RHO(whole[count]),list(whole[count])]];        #partiallists has elements of the form [\rho_{k},k]#
            partial2=partial2+[list(whole[count])];                                  #partial2 only has all the partitions of partiallist#
        count=count+1;
    partiallist=partiallist+[[RHO(whole[count]),list(whole[count])]];
    partial2=partial2+[list(whole[count])];
    m=len(partiallist);            #Size of the matrix$
    re=Matrix(QQ,m);               #re=m by m matrix with rational entries#
    for i in range(m):
        for j in range(i,m):       
            if j==i and i==0:      #When i=j=0, c_{(n),(n)}=1#
                re[i,j]=1;
            if j==i and i>0:
                re[i,j]=multinomial(partiallist[i][1])-sum(re[x,j] for x in range(j));        #(3.5)#
            if j>i:                                                                           #Instead of recursively computing coeffients, compute them by induction#
                rho=partiallist[i][0]-partiallist[j][0];                                      
                if rho==0:                                                                    #Sometimes, two partitions share the same \rho value, if so, we make c_{k,l}=0#
                    re[i,j]=0;
                else:
                    table=SumVariable(partiallist[i][1],partiallist[j][1]);                   #All summable \mu, according the (3.4) #
                    x=len(table);
                    y=positionlist(partial2,partiallist[i][1]);
                    temp=[1/2 for t in range(x)];
                    for t in range(x):
                        temp[t]=positionlist(partial2,table[t][1]);
                    re[i,j]=sum(table[t][0]*re[y,temp[t]] for t in range(x))/rho;             #(3.4)#
    return re[-1,-1];

def Coef(k):                                                             #Given partition k, return c_{k,k}#
    p=len(k);                                                            #length of the partition#
    n=sum(k);                                                            #k is a partition of n#
    chi=product(2*k[i]-2*k[j]-i+j for i in range(p-1) for j in range(i+1,p))/product(factorial(2*k[i]+p-(i+1)) for i in range(p));  #(3.7)#
    temp=k+[0];                                                          #Add a zero in the end, in order to make the following formula valid#
    re=2^(2*n)*factorial(n)*chi*product(product(rising_factorial((l+1)/2-i/2+temp[i]-temp[l],temp[l]-temp[l+1]) for i in range(l+1)) for l in range(p));
    return re;



def Lcoeffi(k,l):                      #Given partitions l<k, return all nonzero c_{mu,l} with k>=mu>=l#
    n=sum(k);                          #k is a partition of n# 
    whole=Partitions(n).list();        #Whole list of partitions of n#
    p1=positionlist(whole,k);          #p1=position of k#
    count=0;
    partiallist=[];
    while whole[p1+count]>l:
        if len(whole[p1+count])<=len(l):
            partiallist=partiallist+[list(whole[p1+count])];
        count=count+1;
    partiallist=partiallist+[list(whole[p1+count])];
    m=len(partiallist);                #length of this partial list#
    re=[1/2 for x in range(m)];        #list of c_{k,\mu} for all \mu between k and l, which will be returned#
    re[0]=Coef(k);                     #c_{k,k}#
    for x in range(1,m):               #Same idea as the COE function above#
        mu=partiallist[x];
        rho=RHO(k)-RHO(mu);
        if rho==0:
            re[x]=0;
        else:
            table=SumVariable(k,mu);
            y=len(table);
            temp1=[1/2 for t in range(y)];
            for t in range(y):
                temp1[t]=positionlist(partiallist,table[t][1]);
            re[x]=sum(table[t][0]*re[temp1[t]] for t in range(y))/rho;
    return re;    

def Coeffi(k,l): 
    if l>k:
        return 0;
    else:
        return Lcoeffi(k,l)[-1];    

def FLcoeffi(k):                       #Full List of coefficients c_{k,l} for all l<=k#
    n=sum(k);                          #k is a partition of n# 
    whole=Partitions(n).list();        #Whole list of partitions of n#
    p=positionlist(whole,k);           #p=position of k#
    partiallist=whole[p:]              #list of partitions from k to l#
    m=len(partiallist);                #length of this partial list#
    re=[1/2 for x in range(m)];        #list of c_{k,\mu} for all \mu between k and l, which will be returned#
    re[0]=Coef(k);                     #c_{k,k}#
    for x in range(1,m):               #Same idea as the COE function above#
        mu=partiallist[x];
        rho=RHO(k)-RHO(mu);
        if rho==0:
            re[x]=0;
        else:
            table=SumVariable(k,mu);
            y=len(table);
            temp1=[1/2 for t in range(y)];
            for t in range(y):
                temp1[t]=positionlist(partiallist,table[t][1]);
            re[x]=sum(table[t][0]*re[temp1[t]] for t in range(y))/rho;
    return re;

   

def CZonal(k,v):                                                          #Given partition k and variables v, compute C-polynomial C_{k}(v)#
    n=sum(k);                                                             #k is a partition of n$
    whole=Partitions(n).list();                                           #whole list of partitions of n#
    position=positionlist(whole,k);                                       #position of k in the whole list#
    partiallist=whole[position:];                                         #only consider partitions <=k#
    coefftable=FLcoeffi(k);                                               #list of all coefficients c_{k,l} for l<=k#
    Mtable=[MZonal(list(t),v) for t in partiallist];                      #list of all corresponding M_{l}(v)#
    re=sum(coefftable[t]*Mtable[t] for t in range(len(partiallist)));     #(3.3)#
    return re;


def CZonaltoM(k):
    A=Partitions(k).list();
    n=len(A);
    M=Matrix(QQ,n);
    for i in range(n):
        M[i,i:]=Matrix(Lcoeffi(A[i],A[-1]));
    return M;


# The rest is written by Prof. Raymond Kan #
# A function to find out if partition kappa dominates or equal to partition lam
def dominate(kappa,lam):
     if len(kappa)>len(lam):
         return False
     else:
         s1=0;
         s2=0;
         for i in range(len(kappa)):
             s1=s1+kappa[i];
             s2=s2+lam[i];
             if s1<s2:
                 return False
         return True

# A function to find out if mu and lam has at most two distinct elements
def checkmu(lam,mu):
    m1=len(lam);
    m2=len(mu);
    if (m2<m1-1)|(m2>m1):
        return False
    i1=0;
    i2=0;
    c=0;
    while (i2<m2)&(i1<m1):
        if lam[i1]==mu[i2]:
            i1=i1+1;
            i2=i2+1;
        elif lam[i1]<mu[i2]:
            i2=i2+1;
        else:
            i1=i1+1;
            c=c+1;
    c=c+m1-i1;
    return c<=2

# A function to compute the transition matrix from Jack polynomials to 
# monomials of degree k.  It takes two optional arguments:
# alpha: default is 2 
# normalization: 'J','C','P', or 'Q', default is 'J'
def JacktoM(k,*arg):
    if len(arg)==0:
        alpha=2;
        norm='J';
    else:
       alpha=arg[0];
       if len(arg)==1:
           norm='J';
       else:
           norm=arg[1];
    ai = 2/alpha;
    A=Partitions(k).list();
    n=len(A);
    if (norm=='C')|(norm=='Q'):
        ck=[prod(flatten(A[i].upper_hook_lengths(alpha))) for i in range(n)];
# M is a transition matrix from J-normalization of Jack polynomials to monomials.
# It has the attractive property that all elements of this transition matrix are integers.
    M=identity_matrix(ZZ,n);
    for i in range(n):
        M[i,i]=A[i].hook_product(alpha);    # Use internal function to compute the diagonal elements of M
        A[i]=list(A[i]);
    kappa_l=[len(A[i]) for i in range(n)];
    rho=[sum(A[i][j]*(A[i][j]-1-ai*j) for j in range(kappa_l[i])) for i in range(n)];     
    M[:,-1]=factorial(k);               # last column of M is k!
# Create a matrix with coefficients a_lam(mu)
    n1= round(n*n^(2/5)+6);
    a=zero_vector(n1);
    alist=zero_vector(n1);
    count=zero_vector(n-1);
    for jj in range(1,n-1):
        count[jj]=count[jj-1];  
        lam=A[jj];
        m2=kappa_l[jj];
        lam_c = Partition(lam).to_exp();
        for kk in range(jj):
            mu=A[kk];
            if checkmu(lam,mu):
                s=m2-1;
                if kappa_l[kk]==m2:
                    while lam[s]==mu[s]:
                        s=s-1;
                    t=mu[s];
                else:
                    t=0;
                while lam[s]==mu[s-1]:
                   s=s-1;
                t=lam[s]-t;
                r=s-1;
                while (mu[r]!=lam[r]+t)&((lam[r]==mu[r])|(lam[r-1]!=mu[r])):
                    r=r-1;
                if lam[r]==lam[s]:
                    w=lam.count(lam[r]);
                    w=w*(w-1)/2;
                else:
                    w=lam.count(lam[r])*lam.count(lam[s]);
# Store all the nonzero entries a_lam(mu)
                a[count[jj]]=(lam[r]-lam[s]+2*t)*w
                alist[count[jj]]=kk;
                count[jj]=count[jj]+1;  
# Compute the coefficients of M using recursion. 
    for ii in range(n-1):
        kappa=A[ii];
        for jj in range(ii+1,n-1):
            lam=A[jj];
            if dominate(kappa,lam):
                M[ii,jj]=sum(a[kk]*M[ii,alist[kk]] for kk in range(count[jj-1],count[jj]) if alist[kk]>=ii)*ai/(rho[ii]-rho[jj]); 
    if norm!='J':    
        M=M.base_extend(QQ);
        if norm=='P':
            for ii in range(n):
                M[ii,ii:]=M[ii,ii:]/M[ii,ii];
        elif norm=='Q':
            for ii in range(n):
                M[ii,ii:]=1/ck[ii]*M[ii,ii:];
        else:
            c0=alpha**k*factorial(k);
            for ii in range(n):
                M[ii,ii:]=c0/M[ii,ii]/ck[ii]*M[ii,ii:];
    return M

# Compute the transitition matrix from Jack polynomials to power-sum symmetric polynomials
def JacktoP(k,*arg):
    if len(arg)==0:
        alpha=2;
        norm='J';
    else:
       alpha=arg[0];
       if len(arg)==1:
           norm='J';
       else:
           norm=arg[1];
    m=SymmetricFunctions(QQ).m();
    p=SymmetricFunctions(QQ).p();
    A=JacktoM(k,alpha,norm)*m.transition_matrix(p,k);
    return A

# Compute the transitition matrix from power-sum symmetric polynomials to Jack polynomials.
# Note that we do not use the inverse of JacktoP(k,alpha,norm) to obtain this.
def PtoJack(k,*arg):
    if len(arg)==0:
        alpha=2;
        norm='J';
    else:
       alpha=arg[0];
       if len(arg)==1:
           norm='J';
       else:
           norm=arg[1];
    B=JacktoP(k,alpha,'J').transpose();
    n=B.nrows();
    for i in range(n):
        B[i,:]=B[i,:]/B[i,0];
    if norm!='C':
        B=alpha**k*factorial(k)*B;
        p=Partitions(k).list();
        if norm=='P':
            for ii in range(n):
                B[:,ii]=B[:,ii]/prod(flatten(p[ii].upper_hook_lengths(alpha)));
        elif norm=='J':
            for ii in range(n):
                B[:,ii]=B[:,ii]/prod(flatten(p[ii].upper_hook_lengths(alpha)))/p[ii].hook_product(alpha);
        else:
            for ii in range(n):
                B[:,ii]=B[:,ii]/p[ii].hook_product(alpha);
    return B

# Compute the transition matrix from monomial symmetric polynomials to Jack polynomials
def MtoJack(k,*arg):
    if len(arg)==0:
        alpha=2;
        norm='J';
    else:
       alpha=arg[0];
       if len(arg)==1:
           norm='J';
       else:
           norm=arg[1];
    m=SymmetricFunctions(QQ).m();
    p=SymmetricFunctions(QQ).p();
    C=m.transition_matrix(p,k);
    B=(JacktoM(k,alpha,'J')*C).transpose();
    n=B.nrows();
    for i in range(n):
        B[i,:]=B[i,:]/B[i,0];
    if norm!='C':
        B=alpha**k*factorial(k)*B;
        p=Partitions(k).list();
        if norm=='P':
            for ii in range(n):
                B[:,ii]=B[:,ii]/prod(flatten(p[ii].upper_hook_lengths(alpha)));
        elif norm=='J':
            for ii in range(n):
                B[:,ii]=B[:,ii]/prod(flatten(p[ii].upper_hook_lengths(alpha)))/p[ii].hook_product(alpha);
        else:
            for ii in range(n):
                B[:,ii]=B[:,ii]/p[ii].hook_product(alpha);
    return C*B

# A function to compute the transition matrix from zonal polynomials to 
# monomials of degree k.  It takes an optional argument:
# normalization: 'J','C','P', or 'Q', default is 'J'
def ZonaltoM(k,*arg):
    if len(arg)==0:
        norm='J';
    else:
        norm=arg[0];     
    A=Partitions(k).list();
    n=len(A);
    if (norm=='C')|(norm=='Q'):
        ck=[prod(flatten(A[i].upper_hook_lengths(2))) for i in range(n)]; 
# M is a transition matrix from J-normalization of zonal polynomials to monomials.
# It has the attractive property that all elements of this transition matrix are integers.
    M=identity_matrix(ZZ,n);
    for i in range(n):
        M[i,i]=A[i].hook_product(2);    # Use internal function to compute the diagonal elements of M
        A[i]=list(A[i]);
    kappa_l=[len(A[i]) for i in range(n)];
    rho=[sum(A[i][j]*(A[i][j]-j-1) for j in range(kappa_l[i])) for i in range(n)];     
    M[:,-1]=factorial(k);              # last column of M is k!
# Create a matrix with coefficients a_lam(mu)
    n1= round(n*n^(2/5)+6); 
    a=zero_vector(n1);
    alist=zero_vector(n1);
    count=zero_vector(n-1);
    for jj in range(1,n-1):
        count[jj]=count[jj-1]; 
        lam=A[jj];
        m2=kappa_l[jj];
        lam_c=Partition(lam).to_exp();
        for kk in range(jj):
            mu=A[kk];
            if checkmu(lam,mu):
                s=m2-1;
                if kappa_l[kk]==m2:
                    while lam[s]==mu[s]:
                        s=s-1;
                    t=mu[s];
                else:
                    t=0;
                while lam[s]==mu[s-1]:
                   s=s-1;
                t=lam[s]-t;
                r=s-1;
                while (mu[r]!=lam[r]+t)&((lam[r]==mu[r])|(lam[r-1]!=mu[r])):
                    r=r-1;
                if lam[r]==lam[s]:
                    w=lam_c[lam[r]-1];
                    w=w*(w-1)/2;
                else:
                    w=lam_c[lam[r]-1]*lam_c[lam[s]-1];
# Store all the nonzero entries a_lam(mu)
                a[count[jj]]=(lam[r]-lam[s]+2*t)*w;
                alist[count[jj]]=kk;
                count[jj]=count[jj]+1; 
# Compute the coefficients of M using recursion. 
    for ii in range(n-1):
        kappa=A[ii];
        for jj in range(ii+1,n-1):
            lam=A[jj];
            if dominate(kappa,lam):
                M[ii,jj]=sum(a[kk]*M[ii,alist[kk]] for kk in range(count[jj-1],count[jj]) if alist[kk]>=ii)/(rho[ii]-rho[jj]);
    if norm!='J':    
        M=M.base_extend(QQ);
        if norm=='P':
            for ii in range(n):
                M[ii,ii:]=M[ii,ii:]/M[ii,ii];
        elif norm=='Q':
            for ii in range(n):
                M[ii,ii:]=M[ii,ii:]/ck[ii];
        else:
            c0=2**k*factorial(k);
            for ii in range(n):
                M[ii,ii:]=c0/M[ii,ii]/ck[ii]*M[ii,ii:]; 
    return M

