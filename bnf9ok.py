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

      print('CLS:',p(tree))
      print('LINE:', line)

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
    elif ":-" == x: continue
    else:
      stack.append(tovar(x))
  t = stack.pop()
  return t

def get_val(v) :
  return heap[v]

def set_val(v,t) :
  heap[v]=t


def deref(o) :
  while True :
    x,t=o
    if t==VAR:
      v,tv=get_val(x)
      if v==x :
        assert VAR==tv
        return o
      if VAR==tv and v>x :
        print('DEREF:',v,'>',x)
        assert v<x
      o=v,tv

    else:
     return o

# unify two terms
def unify(x,y,trail,htop) :
  ustack=[]
  ustack.append(y)
  ustack.append(x)
  while ustack :
    x1,t1=deref(ustack.pop())
    x2,t2=deref(ustack.pop())
    if (x1,t1) == (x2,t2):
      pass
    elif VAR == t1 and VAR == t2:
      if x1>x2 :
        set_val(x1, (x2, t2))
        if x1 < htop: trail.append(x1)
      else :
        set_val(x2, (x1, t1))
        if x2 < htop: trail.append(x2)
    elif VAR == t1 :
      set_val(x1,(x2,t2))
      if x1<htop: trail.append(x1)
    elif VAR == t2:
      set_val(x2,(x1,t1))
      if x2<htop: trail.append(x2)
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
  for _ in range(htop,l) :
    heap.pop()

def get_goal() :
  goal = atom('goal')
  cont=(len(heap),VAR)
  p=pair(cont,goal)
  answer = (len(heap), VAR)
  return pair(answer, p)

def activate(G,clause,trail,ttop,htop) :
  hb,ctag=clause.c

  ok = unify(left(hb), G, trail, htop)
  unwind(trail, ttop)
  if not ok : return False

  begin = clause.begin
  end = clause.end
  h = htop - begin

  for j in range(begin,end) :
    x,t=heap[j]
    if CONST==t:
      heap.append((x, t))
    else :
      heap.append((x+h, t))
  r=h+hb,ctag
  return r

FAIL,DO,DONE,UNDO=0,1,2,3


def step(G, code, trail, goal,  i):
  l=len(code)
  htop = len(heap)
  ttop = len(trail)
  G = deref(G)
  assert G[0] < htop
  while i < l:
    unwind(trail, ttop)
    trim_heap(htop)
    clause = activate(G, code[i], trail, ttop, htop)
    i += 1
    if clause:
      hb, thb = clause
      assert PAIR == thb
      H = left(hb)
      assert H[0] >= htop
      assert G[0] < htop
      unify(G, H, trail, htop)
      b, tb = deref(right(hb))
      if VAR == tb:
        # yield p(left(goal[0]))
        # print("GOAL",iron(goal))
        print(p(left(goal[0])))
        return (DONE, G, ttop, htop, i)
      else:
        NewG = b, tb
        assert b < len(heap)
        # yield from loop(NewG,k+1)
        return (DO, (NewG, G), ttop, htop, i)
  return (FAIL, None, ttop, htop, i)

# code interpreter
def interp() :
  goal=get_goal()
  code=load_iltp()
  #pc(code)
  l=len(code)
  trail = []
  todo=[(DO,(goal,None),0,len(heap),l)]

  while(todo) :
    op, G, ttop, htop, i = todo.pop()
    if DO == op:
      (NewG, OldG) = G
      if i < l: ensure_undo(OldG, todo, ttop, htop, i, l);
      todo.append(step(NewG, code, trail, goal, 0))

    elif DONE == op:
      # yield p(answer)
      if i < l: ensure_undo(G, todo, ttop, htop, i, l)

    elif UNDO == op:
      unwind(trail, ttop)
      trim_heap(htop)
      if i < l: todo.append(step(G, code, trail, goal, i))

    else:  # FAIL == op:
      pass

def ensure_undo(G, todo, ttop, htop, i, l):
    # if i==l-1: print('!!!',i)
    instr = (UNDO, G, ttop, htop, i)
    if todo:
      (op, G1, ttop1, htop1, i1) = todo[-1]
      if (op, i1, G) == (UNDO, i, G1) and ttop >= ttop1:
        return
    todo.append(instr)


def go() :
  interp()


### -- HELPERS, IO

def p(o) :
  x,t=deref(o)
  if VAR==t: return "_"+str(x)
  elif CONST==t : return sids[x]
  else :
    assert PAIR==t
    a,b=heap[x],heap[x+1]
    return "("+p(a)+"=>"+p(b)+")"

def pp(o) :
  print(p(o))
  nl()

def nl() :
  print("")

def ph(begin=0,end=0) :
  if end==0: end=len(heap)
  print("HEAP:",begin,"-->",end)
  assert end>0
  for i in range(begin,end) :
    print(i,':',end=" ")
    pp(heap[i])
  print('----------')

def pt(trail,begin=0,end=0) :
  if end==0: end=len(trail)
  print("TRAIL:",begin,"-->",end)
  #assert end>0
  for i in range(begin,end) :
    print(i,':',end=" ")
    pp((trail[i],VAR))
  print('----------')

def phb(c) :
  hb, tg = c
  assert PAIR == tg
  h = left(hb)
  b = right(hb)
  return p(h)+ " :- " + p(b)

def pc(code) :
  print("CLAUSES:")
  for i,clause in enumerate(code):
    s=phb(clause.c)
    print(i,':',s,'\t',clause.begin,':',clause.end)
  print("----------")

def iron(a,size=200) :
  def iron0(a, k):
    if k <= 0: return ".?."
    x, t = deref(a)
    if t == PAIR:
      u, v = left(x),right(x)
      k -= 1
      return iron0(u, k), iron0(v, k)
    elif t== CONST:
      return sids[x]
    else:
      return "_"+str(x)
  return iron0(a,size)

go()
