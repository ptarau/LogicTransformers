VAR=1
REF=2
PAIR=3
CONST=4

# unnamed variable
def var() :
  v=[None]
  v[0]=v
  return v

# named variable
def nvar(name):
  v=[None,name]
  v[0]=v
  return v

# return type of data object
def type_of(x) :
  if isinstance(x,list) :
    return VAR+(not x is x[0]) # VAR or REF
  elif isinstance(x,tuple) :
    return PAIR
  else:
    return CONST

# finding the reference of a variable
def deref(x) :
  while True :
    t=type_of(x)
    if t==REF:
      x=x[0]
    else:
     return x,t

# return term with all vars in it dereferenced
def iron(a,size=200) :
  def iron0(a, k):
    if k <= 0: return ".?."
    x, t = deref(a)
    if t == PAIR:
      u, v = x
      k -= 1
      return iron0(u, k), iron0(v, k)
    else:
      return x
  return iron0(a,size)

def to_pterm(x) :
  x,t=deref(x)
  if VAR==t : return x
  elif CONST==t : return x
  else :
    assert PAIR==t
    a, b = x
    args=[None,to_pterm(a)]
    while True:
      b, t = deref(b)
      if PAIR == t :
        a,b=b
        args.append(to_pterm(a))
      else :
        args[0]=to_pterm(b)
        return list(args)

# converts a "."/2 lists to actual lists
def dot2list(a):
  def is_dot_list(a):
    return isinstance(a,list) and len(a)>0 and '.'==a[0]
  def walk(x) :
    if is_dot_list(x) :
      args=[]
      while is_dot_list(x) :
        e=dot2list(x[1])
        args.append(e)
        y=x
        x=x[2]
      if x=='[]' :
        return args
      else :
        y=(y[0],dot2list(y[1]),dot2list(y[2]))
        args.append(y)
        return args
    elif VAR==type_of(x) :
      return x
    elif isinstance(x,tuple) or isinstance(x,list) :
      return tuple(map(dot2list,x))
    else :
      return x
  return walk(a)

# turn term int more readable string
def pt(a,size=200) :
  def pt0(a, k):
    if k <= 0: return ".?."
    x, t = deref(a)
    if t == PAIR:
      u, v = x
      k -= 1
      return f'({pt0(u, k)}=>{pt0(v, k)})'
    elif t == VAR:
      if len(x) == 2:
        return str(x[1])
      else:
        return "_" + str(id(x))
    else:
      return str(x)
  return pt0(a,size)


# undo bindings on the trail
def unwind(trail,ttop) :
  #print('UNWIND',pt(trail[-1]),':',len(trail),'-',ttop)
  for _ in range(len(trail)-ttop):
    v = trail.pop()
    v[0] = v

# unify two terms
def unify(x,y,trail) :
  ustack=[]
  ustack.append(y)
  ustack.append(x)
  while ustack :
    x1,t1=deref(ustack.pop())
    x2,t2=deref(ustack.pop())
    if x1 is x2:
      pass
    elif VAR==t1 :
      x1[0]=x2
      trail.append(x1)
    elif VAR==t2:
      x2[0]=x1
      trail.append(x2)
    elif t1!=t2 :
      return False
    elif t1==CONST:
      if x1!=x2 :
        return False
    else :
      #assert t1 == PAIR and len(x1)==2
      #assert t2 == PAIR and len(x2)==2
      a1,b1=x1
      a2,b2=x2   
      ustack.append(b2)
      ustack.append(b1)
      ustack.append(a2)
      ustack.append(a1)
  return True

# load from an "assembler" code file
def tload(fname='out/tnf_asm.txt'):
  def to_const(x) :
    try :
      return int(x)
    except ValueError:
      try:
        return float(x)
      except ValueError:
        return x
  with open(fname,'r') as f: txt=f.read()
  ls = txt.split('\n')
  code = []
  vars=dict()
  cs=[]
  for l in ls:
    xs=l.split(' ')
    if len(xs)<=1 :continue # skip extra new lines
    for j,x in enumerate(xs) :
      if x[0].isupper():
        if x in vars:
          v=vars[x]
        else:
          v=[len(vars),x]
          vars[x]=v
        xs[j]=v
      elif x[0]=="_":
        v = [len(vars), x]
        vars[x] = v
        xs[j] = v
      elif x=='[|]':
        xs[j]='.'
      else :
        xs[j] = to_const(x)
    cs.append(xs)
    if xs[0]=='p' :
      code.append(cs)
      vars=dict() # new vars scoped over next clause
      cs=[]
  return code

# creates actual variables from code skeletons
def activate(instr,vars) :
  newinstr=[]
  for c in instr :
    if isinstance(c,list): # a variable
      n=c[0]
      if n<len(vars) :
        d=vars[n]
      else:
        d=nvar(c[1])
        vars.append(d)
    else: # const
      d=c
    newinstr.append(d)
  return newinstr

# builds goal assuming goal(X):- ... is
# a clause in the source program
def get_goal(code) :
  r= (nvar('Answer'),('true','goal'))
  return r

FAIL, DONE, DO, UNDO = 0, 1, 2, 3

def step(G, i, code, trail):
  ttop = len(trail)
  while i < len(code):
    unwind(trail, ttop)
    clause = code[i]
    i += 1  # next clause
    vars = []
    for instr in clause:
      c = activate(instr, vars)
      op = c[0]
      if op == 'u' or op == 'b':
        r = unify((c[1], c[2]), c[3], trail)
        if not r:
          break
      elif op == 'd':
        assert VAR == type_of(c[1])
        c[1][0] = G
        trail.append(c[1])
      else:  # op==p
        NewG, tg = deref(c[1])
        if NewG == 'true' and CONST == tg:
          return (DONE, G, ttop, i)
        else:
          assert PAIR == tg
          return (DO, NewG, G, ttop, i)
  return (FAIL,)

# code interpreter
def interp(code,goal) :
  l=len(code)
  todo=[(DO,goal,None,0,None)]
  trail=[]
  while todo :
    instr=todo.pop()
    op=instr[0]
    if DO==op :
      _,NewG,G,ttop,i=instr
      r=step(NewG,0,code,trail)
      todo.append((UNDO,G,ttop,i))
      todo.append(r)
    elif DONE==op:
      _, G, ttop, i = instr
      todo.append((UNDO,G,ttop,i))
      yield iron(goal)
    elif UNDO==op :
      _, G, ttop, i=instr
      unwind(trail,ttop)
      if i!=None and i<l :
        todo.append(step(G,i,code,trail))
    else : #FAIL == op:
      pass

# tests
def go() :
  code=tload()
  ctr=0
  max_ctr=1000000
  for g in interp(code,get_goal(code)):
    answer=iron(g[0])
    ctr+=1
    answer=to_pterm(answer)
    print('ANSWER:',dot2list(answer))
    if ctr>=max_ctr :
      print('TOO MANY ANSWERS?')
      break
  print('TOTAL ANSWERS:',ctr)

# tests unification
def utest() :
  X=var()
  Y=var()
  a=(X,'a')
  b=('b',Y)
  print('AB',a,type_of(a),b,type_of(b))
  trail=[]
  r=unify(a,b,trail)
  print(r)
  print('FINAL AB',a,type_of(a),b,type_of(b))
  print('TR',trail)
  print("PT",pt((a,(nvar("X"),var()))))

# tests conversion to Horn form
def ptest():
  A = nvar('A')
  B = nvar('B')
  print(to_pterm((((A, (A, 'b')), 'a'), (B, 'c'))))
  print(to_pterm(((1, 'g'), (2, (3, 'f')))))

go()
