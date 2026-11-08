# usage: rep.py FILE NAME BODYFILE : replace the "  sorry" body of theorem NAME by contents of BODYFILE
import sys,re
f,name,bodyf=sys.argv[1:4]
s=open(f).read()
body=open(bodyf).read().rstrip('\n')+'\n'
i=s.find('theorem '+name+' ')
if i<0: i=s.find('theorem '+name+'\n')
assert i>=0, name
j=s.find(':= by\n  sorry\n',i)
k=s.find('\ntheorem ',i+1)
assert j>=0 and (k<0 or j<k), 'no sorry body'
s=s[:j]+':= by\n'+body+s[j+len(':= by\n  sorry\n'):]
open(f,'w').write(s)
print('ok',name)
