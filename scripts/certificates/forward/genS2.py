from genS import *
res=pickle.load(open('S_parts.pkl','rb'))
for name in ['A0','E3','E4']:
    for nm in ['R','cI','cc']:
        n,d=res[name][nm]
        n=sp.sympify(str(n)).subs({}); d=sp.sympify(str(d))
        nump,dl,dp=frac_lean(n,d)
        print(name,nm,'den:',dl,' numdeg',sp.Poly(nump,a,t).degree_list())
