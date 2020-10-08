VAR, REF, PAIR, CONST = 1,2,3,4

# unnamed variable
def var() : return [None]

# named variable
def nvar(name): return [None,name]

# return type of data object
def type_of(x) :
  if isinstance(x,list) :
    if x[0] is None : return VAR
    return REF
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

def pp(x) : return dot2list(to_pterm(x))

# turn term into more readable string
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


# creates actual variables from code skeletons
def activate(instr,vars,vids) :
  newinstr=[]
  #l=len(vars)
  for c in instr :
    if isinstance(c,list): # a variable
      n=c[0]
      if n<len(vars) :
        d=vars[n]
      else:
        d=nvar(c[1])
        #print('D=',d,id(d),type(vids))
        vids.add(id(d))
        vars.append(d)
    else: # const
      d=c
    newinstr.append(d)
  return newinstr

# undo bindings on the trail
def unwind(trail,ttop) :
  #print('UNWIND',pt(trail[-1]),':',len(trail),'-',ttop)
  for _ in range(len(trail)-ttop):
    v = trail.pop()
    v[0] = None

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

# builds goal assuming goal(X):- ... is
# a clause in the source program
def get_goal() :
  answer= nvar('Answer')
  return  (answer,('true','goal')),answer

FAIL, DONE, DO, UNDO = 0, 1, 2, 3
opnames=["FAIL", "DONE", "DO", "UNDO"]

# inner loop of at most len(code) steps
def step(G,i, code,trail):
    ttop=len(trail)
    while i<len(code):
      unwind(trail, ttop)
      clause=code[i]
      i+=1 #next clause
      vars,vids = [],set()
      #print('@@@ CLAUSE:',clause)
      for instr in clause :
        #print("INSTR:",instr)
        c=activate(instr,vars,vids)
        op=c[0]
        #print("!!!",c)

        if op=='u' :
          old,oldt=deref(c[3])
          if VAR==oldt :
            old[0]=c[1],c[2]
            continue
          else :
            #print("OLD:",old)
            assert PAIR==oldt
            if not (unify(c[1],old[0],trail,vids) and \
                    unify(c[2],old[1],trail,vids)) : break

        elif op=='b':
          old,oldt=deref(c[3])
          #assert VAR==oldt
          old[0]=c[1],c[2]
          continue

        elif op=='d':
          assert VAR==type_of(c[1])
          c[1][0]=G
          continue

        else: #p(..)
          NewG,tg=deref(c[1])
          if NewG=='true' and CONST == tg :
            return (DONE,G,ttop,i)
          else:
            assert PAIR==tg
            return (DO,(NewG,G),ttop,i)
    return (FAIL,None,ttop,i)


def ensure_undo(G,todo,ttop,i,l) :
    #if i==l-1: print('!!!',i)
    instr = (UNDO, G, ttop, i)
    if todo :
       (op, G1, ttop1, i1)=todo[-1]
       if (op,i1,G)==(UNDO,i,G1) and ttop>=ttop1:
         return
    todo.append(instr)

def show_todo(todo) :
  k=len(todo)
  while k>0:
    k-=1
    (op,G,ttop,i)=todo[k]
    print("v",opnames[op],ttop,i)
    if(op==UNDO) : print(pp(todo[k][1]))
  print("-----------\n")



# code interpreter
def interp(code) :

  # trampoline, ensures LCO, no recursion etc.

  goal,answer=get_goal()
  l=len(code)
  todo=[(DO,(goal,None),0,l)]
  ctr,maxctr=0, 200000000000
  max_trail, max_todo = 0, 0
  trail=[]
  while ctr<maxctr and todo :

    #show_todo(todo)

    ctr+=1
    max_trail=max(max_trail,len(trail))
    max_todo = max(max_todo, len(todo))
    op,G,ttop,i=todo.pop()
    #opn=opnames[op]
    #print('\n',ctr,'!!!','op=',opn,'ttop=',len(trail),'todo=',len(todo))
    #print('--->',pp(instr[1]),instr[2],'i=',instr[3])

    if DO==op :
      (NewG,OldG)=G
      if i<l : ensure_undo(OldG,todo,ttop,i,l);
      todo.append(step(NewG, 0, code, trail))

    elif DONE==op:
      yield iron(answer), max_trail, max_todo
      if i<l: ensure_undo(G,todo,ttop,i,l)

    elif UNDO==op :
      unwind(trail, ttop)
      if i<l: todo.append(step(G,i, code,trail))

    else: # FAIL == op:
      pass

  if ctr==maxctr: print('*** TOO MANY STEPS? ',ctr)
  print('max_trail=',max_trail,'max_todo=',max_todo)

# tests
def go() :
  code=tload()
  ctr=0
  max_ctr=10000000000
  for a,mtr,mtd in interp(code):
    ctr+=1
    print('ANSWER=',ctr,'trail=',mtr,'todo=',mtd,'-->',pp(a))
    if ctr>=max_ctr :
      print('TOO MANY ANSWERS?')
      break
  print('TOTAL ANSWERS:',ctr)

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

# tests unification
def utest() :
  X=var()
  Y=var()
  a=(X,'a')
  b=('b',Y)
  print('AB',a,type_of(a),b,type_of(b))
  trail=[]
  r=unify(a,b,trail,set())
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

# also works with gc disabled
#import gc
#gc.disable()
go()
#utest()
