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
  return tag(sym(s),CONST)

def tag(v,t) :
  return (v,t)

def tag_of(p) :
  return p[1]

def val(p) :
  return p[0]

PAIR,CONST,VAR=1,2,3

def pair(x,y) :
  assert isinstance(x,tuple)
  assert isinstance(y, tuple)
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


def tovar(x) :
    if x[0] == '_':
      v=int(x[1:])
      return tag(v,VAR)
    elif x[0] == '^':
      v=int(x[1:])
      return tag(v,PAIR)
    else :
      return atom(x)

def tload():
  cs = []
  with open('out/hasm.txt', 'r') as f:
    #h = len(heap)
    for line in f:
      toks = line[:-1].split()
      op=toks[0];
      if op=='d' :
        h = len(heap)
        #c=[op,tovar(toks[1])]
        c=[]
      if op=='d' or op=='u' or op=='b' :
        instr = [op]
        for i in range (1,4) :
          instr.append(tovar(toks[i]))
        c.append(tuple(instr))
      else :
        assert op=='p'
        instr = (op,tovar(toks[1]))
        c.append(instr)
        cs.append(c)
  for clause in cs :
    for instr in clause :
         print(instr)
    print('')
  return cs

def get_val(v) :
  return heap[v]

def set_val(v,t) :
  assert isinstance(t,tuple)
  heap[v]=t


def deref(o) :
  while True :
    #print("\n!!!! DEREF: <<<",o,'>>>\n')
    x,t=o
    if t==VAR:
      v,tv=get_val(x)
      if v==x :
        assert VAR==tv
        return o
      if VAR==tv and v>x :
        #print('DEREF:',v,'>',x)
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
  r = pair(answer, p)
  #print('!!!! GOAL HEAP:',len(heap))
  #pp(r)
  return r



FAIL,DO,DONE,UNDO=0,1,2,3

ctr=30
def COUNT() :
  global ctr
  if(ctr<=0) : exit(0)
  ctr-=1

def step(G, code, trail, goal,  i):
  COUNT()
  print('STEP G=',G)
  assert isinstance(G,tuple)
  def act(x):
    v, t = x
    if CONST == t:
      return t
    else:
      return v + htop, t
    return r

  l=len(code)
  htop = len(heap)
  ttop = len(trail)
  #ph()
  G = deref(G)
  assert G[0] < htop

  def act(x):
    v, t = x
    if CONST == t:
      return x
    else:
      return v + htop, t
    return r

  while i < l:
    unwind(trail, ttop)
    trim_heap(htop)
    clause=code[i]
    i += 1
    for c in clause :
      #print('INSTR:',i-1,c)
      #ph()
      op = c[0]
      if op == 'd':
        x1 = G
        x2 = act(c[2])
        pair(x1, x2)
        continue
      elif op == 'u' or op=='b':
        x1 = act(c[1])
        x2 = act(c[2])
        #print("PAIR",x1,x2)
        x3 = pair(x1,x2)
        old = deref(act(c[3]))
        ok=unify(x3,old,trail, htop)
      else:
        assert op == 'p'
        NewG, tg = deref(act(c[1]))
        if VAR == tg:
          return (DONE, None, G, ttop, htop, i)
        else:
          assert PAIR == tg
          return (DO, (NewG,tg), G, ttop, htop, i)

  return (FAIL, None, None, ttop, htop, i)






# code interpreter
def interp() :
  goal=get_goal()
  code=tload()
  #pc(code)
  l=len(code)
  trail = []
  todo=[(DO,goal,None,0,len(heap),l)]

  while(todo) :
    COUNT()
    instr=todo.pop()
    print('INTERP:',instr,'TODO:',len(todo))
    op, NewG, OldG, ttop, htop, i = instr
    if DO == op:
      assert isinstance(NewG,tuple)
      print('DOING:',p(NewG))
      if i < l: ensure_undo(OldG, todo, ttop, htop, i, l);
      r=step(NewG, code, trail, goal, 0)
      todo.append(r)

    elif DONE == op:
      print("ANSWER:",p(goal))
      if i < l: ensure_undo(OldG, todo, ttop, htop, i, l)

    elif UNDO == op:
      unwind(trail, ttop)
      trim_heap(htop)
      if i < l: todo.append(step(OldG, code, trail, goal, i))

    else:  # FAIL == op:
      print('FAILING:',i)
      pass

def ensure_undo(G, todo, ttop, htop, i, l):
    # if i==l-1: print('!!!',i)
    instr = (UNDO, None, G, ttop, htop, i)
    '''
    if todo:
      (op, G1?, _, ttop1, htop1, i1) = todo[-1]
      if (op, i1, G) == (UNDO, i, G1) and ttop >= ttop1:
        return
    '''
    todo.append(instr)




### -- HELPERS, IO

def p(o) :
  #print("\nDEREF:",o,"\n")
  x,t=deref(o)
  if VAR==t: return "_"+str(x)
  elif CONST==t : return sids[x]
  else :
    assert PAIR==t
    if x<len(heap) :
      a=p(heap[x])
    else :
      a='?'+str(x)
    x+=1
    if x<len(heap) :
      b=p(heap[x])
    else :
      b='?'+str(x)
    return "("+a+"=>"+b+")"

def pp(o) :
  print(p(o))

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

def go() :
  interp()
  #tload()

go()
