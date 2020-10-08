'''
import numpy as np

heap=np.zeros(2**16,dtype=int)
htop=0
'''

heap=[]

syms=dict()
sids=[]

def sym(s) :
  if s in syms : return syms[s]
  i=len(sids)
  syms[s]=i
  sids.append(s)
  return i

def atom(s) :
  return (sym(s),CONST)

PAIR,CONST,VAR=1,2,3

def pair(x,y) :
  h=len(heap)
  heap.append(x)
  heap.append(y)
  return h,PAIR

def left(p) : return heap[p]

def right(p) : return heap[p+1]

class cls:
  def __init__(self,c,begin,end):
    self.begin=begin;
    self.end = end;
    self.c=c;

  def __repr__(self):
    return 'cls('+str(self.c)+'\t'+str(self.begin)+":"+str(self.end)+')'

def load_iltp():
  ts = []
  with open('out/bnf_asm.txt', 'r') as f:
    for line in f:
      begin=len(heap)
      toks = line[:-1].split()
      tree = stack2tree(toks)
      end=len(heap)
      clause=cls(tree,begin,end)
      #print('CLS:',p(tree))
      ts.append(clause)
      vids=dict()
      for h in range(begin,end) :
        x,t=heap[h]
        if VAR==t:
          if x in vids :
            y=vids[x]
            heap[h]=y,VAR
          else :
            #h0=h-begin
            heap[h]=h,t
            vids[x]=h
      #print('EOC-----',vids)
  #ph()
  return ts

def stack2tree(postfix):
  stack = []
  vars=dict()

  def tovar(x) :
    if isinstance(x,tuple) : return x
    if x[0].isupper():
      if x in vars:
        v = vars[x]
        return v,VAR
      else:
        v = len(vars)
        vars[x] = v
        return v,VAR
    else :
      return atom(x)

  ops2=["$"]
  for x in postfix:
    if x in ops2:
      t2 = stack.pop()
      t1 = stack.pop()
      t = pair(t1,t2)
      stack.append(t)
    else:
      stack.append(tovar(x))
  t = stack.pop()
  return t

def get_val(v) :
  return heap[v]

def set_val(v,t) :
  heap[v]=t

def p(o) :
  x,t=deref(o)
  if VAR==t: return "_"+str(x)
  elif CONST==t : return sids[x]
  else :
    a,b=heap[x],heap[x+1]
    return "("+p(a)+"=>"+p(b)+")"

def pp(o) :
  print(p(o))
  nl()

def nl() :
  print("")

def ph(begin=0,end=len(heap)) :
  print("HEAP:",begin,"-->",end)
  for i in range(begin,end) :
    print(i,':',end=" ")
    pp(heap[i])
  print('----------')

def pc(code) :
  print("CLAUSES:")
  for i,clause in enumerate(code):
    print(i,':',p(clause.c),'\t',clause.begin,':',clause.end)
  print("----------")


def deref(o) :
  while True :
    x,t=o
    if t==VAR:
      v,tv=get_val(x)
      if VAR==tv and v!=x :
        o=v,tv
      else :
        return o
    else:
     return o

# unify two terms
def unify(x,y,trail) :
  ustack=[]
  ustack.append(y)
  ustack.append(x)
  while ustack :
    x1,t1=deref(ustack.pop())
    x2,t2=deref(ustack.pop())
    #print('@@@:',p((x1,t1)),'===',p((x2,t2)))
    #print('=======')
    if x1 == x2:
      pass
    elif VAR == t1 :
      set_val(x1,(x2,t2))
      trail.append(x1)
    elif VAR == t2:
      set_val(x2,(x1,t1))
      trail.append(x2)
    elif t1!=t2 :
      return False
    elif t1 == CONST:
      if x1!=x2 :
        return False
    else :
      assert t1 == PAIR
      assert t2 == PAIR
      a1,b1=left(x1),right(x1)
      a2,b2=left(x2),right(x2)
      ustack.append(b2)
      ustack.append(b1)
      ustack.append(a2)
      ustack.append(a1)
  return True


def unwind(trail,ttop) :
  for _ in range(len(trail)-ttop):
    v = trail.pop()
    set_val(v,(v,VAR))

def trim_heap(htop) :
  #return
  l=len(heap)
  for _ in range(htop,l) : heap.pop()

def iron(a,size=200) :
  def iron0(a, k):
    if k <= 0: return ".?."
    x, t = deref(a)
    if t == PAIR:
      u, v = left(x),right(x)
      k -= 1
      return iron0(u, k), iron0(v, k)
    else:
      return x
  return iron0(a,size)


#def get_goal(code) :
#  return (nvar('Answer'),(nvar('Cont'),'goal'))

def get_goal() :
  goal = atom('goal')
  answer=(len(heap),VAR)
  p=pair(answer,goal)
  cont = (len(heap), VAR)
  return pair(cont,p)


def activate(clause) :
  c=clause.c
  hb,ctag=c
  #print('CLS PTR',p(c))

  #r= act(c, len(heap))

  begin = clause.begin
  end =  clause.end
  htop=len(heap)
  h = htop-begin
  for i in range(begin,end) :
    x0,t=heap[i]
    #print('ON HEAP at',i,':',x0,t)
    if PAIR==t:
      #print('PAIR')
      x = x0 + h
      heap.append((x, PAIR))
    elif VAR==t:
      #print('VAR/REF',t)
      x=x0+h
      heap.append((x,VAR))
    else :
      #print('CONST',x0,t)
      heap.append((x0,t))
  r=h+c[0],c[1]
  print('ACTIVATED:', r,'-->',p(r), 'heap:',h+begin,h+end)
  #ph(begin=begin,end=end)
  return r

# code interpreter
def interp() :
  goal=get_goal()
  code=load_iltp()
  pc(code)
  l=len(code)
  trail = []
  #ph()

  # inner loop of at most k steps
  def loop(G):
    htop = len(heap)
    ttop = len(trail)
    print('htop:',htop,'ttop:',ttop)
    #ph()
    i=0
    while i < l :
      clause=code[i]
      #yield None
      hb,tg=activate(clause)
      #print("END",hb)
      #i+=1;continue
      assert PAIR==tg
      h=left(hb)
      print("UNIFYING: ", p(G), '==', p(h))
      ok=unify(G,h,trail)

      if(not ok):
        unwind(trail,ttop)
        trim_heap(htop)
      else :
        b,tb=right(hb)
        #pp((b,tb))
        if VAR==tb:
          yield p(goal) #iron(goal)
          unwind(trail, ttop)
          trim_heap(htop)
        else:
           G = b, tb
           yield from loop(G)
      i+=1
  yield from loop(goal)





def go() :
  for a in interp() : print("ANSWER:",a)
  #interp()

go()
