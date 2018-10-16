def Calmi(partition):                 #For a paritition with m_1 1's, m_2 2's and etc, return (m_1)!(m_2)!...(m_l)!. This is the reciprocal of the leading coefficient of M-polynomial.#
    temp=uniq(partition);             #Delete the repeted parts and re-order the distinct parts in ascending order.#
    count=1;                          #set count=1, i.e., empty product.$
    for i in temp:                    #let i run all distinct parts.#
        a=partition.count(i);         #a counts the number of i appearing in the partition.#
        count=count*factorial(a);     #a contributes a! in the product of "count".#
    return count;                     #return the product.#

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

#Now, we can apply (3.4) to compute coefficient c_{\kappa,\lambda}#

def coeffi(k,l):                                #Compute c_{k,l}#
    re=0;
    n=sum(k);
    wholelist=Partitions(n).list();             #The whole list of partitions of n#
    if k==l and len(k)==1:                      #c_{(n),(n)}=1#
        re=1;
    else:
        if k==l:                                #If to compute c_{\kappa,\kappa} when \kappa is not (n), one needs (3.5)#
            t=positionlist(wholelist,k);        #The position of k=l in the whole partition list#
            re=multinomial(k)-sum(coeffi(list(xx),l) for xx in wholelist[:t]);               #(3.5)#
        else:                                   #When k and l are different, we use recurrence (3.4)#
            rho=RHO(k)-RHO(l);                  #There are cases that different partitions k and l share the same \rho value. If so, we set the coefficient 0#
            if rho==0:
                re=0;
            else:
                table=SumVariable(k,l);         #list of all \mu's and the corresponding \lambda_i-\lambda_j+2t#
                re=sum(yy[0]*coeffi(k,yy[1]) for yy in table); #Recurrence (3.4)#
                re=re/rho;
    return re;


def CZonal(part,vari):                                    #Compute C-polynomials, by given part(ition) and vari(ables)#
    n=sum(part);                                          #part(ition) is a partition of n#
    table1=Partitions(n).list();                          #full list of partitions of n#
    table=[list(xx) for xx in table1];                    #Converting all elememts from "Partition" to "list"#
    position=positionlist(table,part);                    #Find the position of part#
    temp=table[position:];                                #Delete all partitions that >= part#
    re=sum(coeffi(part,i)*MZonal(i,vari) for i in temp);  #(3.3)#
    return re;
