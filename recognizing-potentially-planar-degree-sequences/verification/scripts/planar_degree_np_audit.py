"""Independent local audits for the two planar-degree hardness encodings."""
from collections import Counter
from itertools import combinations,permutations,product


def covers(markers,selected,vertices):
    left=[markers[i] for i in selected]
    return any(all(v in pair for v,pair in zip(order,left)) for order in permutations(vertices))


def pair_codes(k):
    ls=list(range(0,2*k,2))
    rs=list(range(1,2*k,2))
    choices=list(combinations(range(2*k+1),2))  # one additional, unnamed original vertex
    subfamilies=[list(range(k))]
    for bit in range((k-1).bit_length()):
        for value in range(2):
            subfamilies.append([i for i in range(k) if i>>bit&1==value])
    count=yes=0
    for markers in product(choices,repeat=k):
        passed=all(covers(markers,I,[side[i] for i in I])
                   for I in subfamilies for side in (ls,rs))
        expected=all(set(pair)=={ls[i],rs[i]} for i,pair in enumerate(markers))
        assert passed==expected
        count+=1
        yes+=passed
    return count,yes


def valence(faces):
    return Counter(v for f in faces for v in f)


def step(faces,missing):
    keep=set(missing)
    out=[]
    born={}
    nxt=1+max(v for f in faces for v in f)
    for i,(a,b,c) in enumerate(faces):
        if i in keep:
            out.append((a,b,c))
        else:
            born[i]=nxt
            out.extend(((a,b,nxt),(b,c,nxt),(c,a,nxt)))
            nxt+=1
    return out,born


def tetrahedron_match():
    original=list(combinations(range(4),3))
    edges=[(0,1),(2,3)]
    first,_=step(original,[])
    second,new_second=step(first,[])
    marker=[new_second[next(i for i,f in enumerate(first) if set(e)<=set(f))] for e in edges]
    current,born=step(second,[])
    saved=[]
    for I,side in [([0,1],0),([0,1],1),([0],0),([0],1),([1],0),([1],1)]:
        newest=set(born.values())
        required=[{marker[i],edges[i][side]} for i in I]
        blanks=[next(j for j,f in enumerate(current) if r<=set(f) and set(f)&newest) for r in required]
        odd={v for i in blanks for v in current[i]}
        assert len(odd)==3*len(I)
        old=valence(current)
        saved.append((dict(old),odd))
        current,born=step(current,blanks)
        updated=valence(current)
        assert all(updated[v]==2*k-int(v in odd) for v,k in old.items())
        assert sum(k==3 for k in updated.values())==2*len(old)-4-len(I)
    rebuilt=dict(valence(current))
    for old,odd in reversed(saved):
        recovered={v:(d+1)//2 for v,d in rebuilt.items() if d!=3}
        assert recovered==old
        assert {v for v,d in rebuilt.items() if d!=3 and d%2}==odd
        rebuilt=recovered
    return len(current)


def bin_example(items,box):
    first=range(len(items))
    return sum(sum(items[i] for i in group)==box for group in combinations(first,3))//2


if __name__=='__main__':
    for k in range(1,4):
        print('Matching size',k,'cases and passing systems',pair_codes(k))
    print('Two-edge positive sphere final faces',tetrahedron_match())
    yes=bin_example((4,4,5,5,6,6),15)
    no=bin_example((4,4,4,6,6,6),15)
    assert yes==4 and no==0
    print('Unordered two-bin partitions:',yes,no)
