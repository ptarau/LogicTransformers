class pair :
  def __init__(self,x,y) :
    self.x=x
    self.y=y

  def __repr__(self):
    def repv(x) :
      if isinstance(x,int) :
        return "_"+str(x)
      else :
        return str(x)
    return "("+repv(self.x)+"=>"+repv(self.y)+")"


class var :
  def __init__(self,i,p):
   self.i=i
   self.p=p

  def __repr__(self) :
    if self.i==0 :
      return "V"+str(self.p.x)
    else:
      return "V"+str(self.p.y)

def load_iltp():
  ts = []
  with open('out/bnf_asm.txt', 'r') as f:
    for line in f:
      toks = line[:-1].split()
      tree = stack2tree(toks)
      ts.append(tree)
  return ts

def stack2tree(postfix):
  stack = []
  vars=dict()

  def tovar(x) :
    if isinstance(x,pair) : return x
    if x[0].isupper():
      if x in vars:
        v = vars[x]
      else:
        v = len(vars)
        vars[x] = v
      return v
    else :
      return x

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

def ispair(t) :
  return isinstance(t,pair)

def isvar(v) :
  return isinstance(v,tuple)

def get_val(v) :
  i,p=v
  if i == 0 : return p.x;
  return p.y

def set_val(v,t) :
  if v.i == 0 : v.p.x=t;
  else : v.p.y = t

VAR,REF,PAIR,CONST=0,1,2,3

def type_of(t) :
  if isinstance(t,pair) : return PAIR
  if isinstance(t,tuple) :
    if None == get_val(t) : return VAR
    else : return REF
  return CONST


def deref(o) :
  while True :
    t=type_of(o)
    if t==REF:
      o=get_val(o)
    else:
     return o,t


def t1() :
  p = pair(1, 2)
  v = var(0, p)
  u = var(1, p)
  set_val(u, v)
  print(deref(u))


'''

# unify two terms
def unify(x,y,trail,vids) :
  ustack=[]
  ustack.append(y)
  ustack.append(x)
  while ustack :
    x1,t1=deref(ustack.pop())
    x2,t2=deref(ustack.pop())
    if x1 is x2:
      pass
    elif VAR is t1 :
      x1[0]=x2
      if id(x1) not in vids:
        trail.append(x1)
    elif VAR is t2:
      x2[0]=x1
      if id(x2) not in vids:
        trail.append(x2)
    elif t1!=t2 :
      return False
    elif t1 is CONST:
      if x1!=x2 :
        return False
    else :
      assert t1 == PAIR and len(x1)==2
      assert t2 == PAIR and len(x2)==2
      a1,b1=x1
      a2,b2=x2   
      ustack.append(b2)
      ustack.append(b1)
      ustack.append(a2)
      ustack.append(a1)
  return True
'''

def go() :
  for t in load_iltp() : print(t)

go()
