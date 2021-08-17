#include "defs.h"
#include "vm.h"
#include "istack.h"
#include "io.h"

#define NDEBUG

// to be initialized in hinit()
static term  *heap;

static term  htop;

void hinit() {
  htop=0;
  heap=XALLOC(MAXHEAP,term );
}

inline static void heapTrim(term  oldtop) {
  htop=oldtop;
}

inline int tag(term  p) {
  return (int)(p&MASK);
}

// integer atom id
inline term  atom(term  a) {
  return ATOM|(a<<SHIFT);
}

// ulong value of an atom - index in sym. table
inline term  aval(term  a) {
  return a>>SHIFT;
}

// variable
inline term  var() {
  term  v=VAR|(htop<<SHIFT);
  heap[htop++]=v;
  return v;
}


// tags i as if it were a variable
inline term  asVar(term  i) {
  return VAR|(i<<SHIFT);
}

inline term  asRef(term  i) {
  return REF|(i<<SHIFT);
}

// value of a var
inline term  vget(term  v) {
  return heap[v>>SHIFT];
}

inline void vset(term  x,term  val) {
  heap[x>>SHIFT]=val;
}

// index on heap where the var points
inline term  vid(term  v) {
  return v>>SHIFT;
}

// finds unbound var or term to which this points
inline term  deref(term  x) {
  while(VAR==tag(x)) {
    term  v=vget(x);
    if (v==x) return v;
    x=v;
  }
  return x;
}

inline term  asPair(term  start) {
  return PAIR|(start<<SHIFT);
}

// pair address
inline term  pair(term  x,term  y) {
  term  start=htop;
  heap[htop++]=x;
  heap[htop++]=y;
  return PAIR|(start<<SHIFT);
}

// left of a pair
inline term  left(term  p) {
  return heap[p>>SHIFT];
}

// left of a pair
inline term  right(term  p) {
  return heap[1+(p>>SHIFT)];
}

// rough printout of the heap's content
void pph() {
  printf("HEAP size:%lu\n",htop);
  for(int i=0;i<htop;i++) {
    term  x=heap[i];
    printf("%u:",i);p(x);
    printf("\t\t\t\t:====:\t");pterm(x);//printf("\n");
  }
  printf("\n");
}


static inline  action newAction(ACT act,term G,term OldG,long ttop,long i,term  ht) {
  action a=XALLOC(1,struct action);
  a->act=act;
  a->G=G;
  a->OldG=OldG;
  a->ttop=ttop;
  a->i=i;
  a->ht=ht;
  return a;
}

int unify(term x,term y,istack trail,long umax,istack ustack) {
  clearStack(ustack);
  ipush(ustack,y);
  ipush(ustack,x);
  
  while (!isEmpty(ustack)) {
    const term x1=deref(ipop(ustack));
    const term x2=deref(ipop(ustack));
    const int t1=tag(x1);
    const int t2=tag(x2);
    
    if(x1==x2) continue;
    
    if(VAR==t1 && VAR==t2) {
      long i1=vid(x1);long i2=vid(x2);
      
      if(i1>i2) {
        vset(x1,x2);
        if(i1<umax)
          ipush(trail,x1);
      }
      else {
        vset(x2,x1);
        if(i2<umax)
          ipush(trail,x2);
      }
    }
    else if(VAR==t1) {
      vset(x1,x2);
      if(vid(x1)<umax)
        ipush(trail,x1);
    }
    else if(VAR==t2) {
      vset(x2,x1);
      if(vid(x2)<umax)
        ipush(trail,x2);
    }
    else if(t1!=t2) {
      return 0;
    }
    else if(ATOM==t1) {
      if(x1!=x2) return 0;
    }
    else {
      term a1=left(x1);
      term b1=right(x1);
      term a2=left(x2);
      term b2=right(x2);
      ipush(ustack,b2);
      ipush(ustack,b1);
      ipush(ustack,a2);
      ipush(ustack,a1);
    }
  }
  return 1;
}

void unwind(istack trail,long ttop) {
  long i=size(trail)-ttop;
  while(i>0) {
    term v=ipop(trail);
    vset(v,v);
    i-=1;
  }
}



#define MAXVARS 10000

static term vars[MAXVARS];
//static term *vars;

void initVars(void) {
  //vars=XALLOC(MAXVARS,term);
  for(int i=0;i<MAXVARS;i++) {
    vars[i]=NIL;
  }
}

/*
 activate needs the heapp position where
 the variable will be put if needed
 if var is new it is used, othervise
 the var is made to point to the existing one
 
 */
static inline term activate(term t) {
  int tg=tag(t);
  if(REF == tg)
    return vars[vid(t)];
  else if(VAR==tg) {
    term v=var();
    vars[vid(t)]=v;
    return v;
  }
  else { // constant (only x1,x2 can be that)
    return t;
  }
}


static inline term acti_var(term t) {
  term v=var();
  vars[vid(t)]=v;
  return v;
}

long fuel=200000000000;

action step(term G,long i,stack code,istack trail,
            istack ustack,IdDict preds) {
  if(!fuel--) exit(1);
  long ttop=size(trail);
  long umax=htop;
  long l=size(code);
  while(i<l) {
    if(!fuel--) exit(1);
    heapTrim(umax);
    unwind(trail,ttop);
    stack clause=at(code,i++);
    
    long m=size(clause);
    for(long j=0;j<m;j++) {
      instr templ=at(clause,j);
      
      //printf("EXEC STEP: j=%ld umax=%ld %u ",j,umax,templ->op);n();
      OP op=templ->op;
      
      switch(op) {
        case U:{
        term x1=activate(templ->x1);
        term x2=activate(templ->x2);
        term x3=activate(templ->x3);
        //printf("U %ld:",htop);pp(x1);sp();pp(x2);sp();pp(x3);n();
        term old=deref(x3);
        if(VAR==tag(old)) {
          term p=pair(x1,x2);
          vset(old,p);
        }
        else {
          //assert(PAIR==tag(old));
          //if(PAIR!=tag(old)) j=m;
          if(!(unify(x1, left(old),trail,umax,ustack) &&
               unify(x2, right(old),trail,umax,ustack)))
            j=m;
        }
        } break;
      case B: {
        //printf("B %ld:",htop);pp(x1);sp();pp(x2);sp();pp(x3);n();
        term x3=acti_var(templ->x3);
        term x1=activate(templ->x1);
        term x2=activate(templ->x2);
        term p=pair(x1,x2);
        vset(x3,p);
      } break;
      case D: {
        term x1=acti_var(templ->x1);
        vset(x1,G);
      } break;
      case P: {
        // TODO: add to action x2 as the predicate to explore !!!
        term x1=activate(templ->x1);
        term NewG=deref(x1);
        //printf("P %d:",op);pp(x1);n();
        term  ht=htop;
        if(VAR==tag(NewG)) {
          return newAction(DONE,NIL,G,ttop,i,ht);
        }
        else {
          return newAction(DO,NewG,G,ttop,i,ht);
        }
      } break;
      default:
        assert(0);
      }
    }
  }
  return NULL; //newAction(FAIL,NIL,NIL,0,0,NIL);
}

term getGoal(void) {
  term answer=var();
  term cont=var();
  term goal=atom(0);
  term cpair=pair(cont,goal);
  term tpair=pair(answer,cpair);
  return tpair;
}

void interp() {
  hinit();
  initVars();
  printf("STARTING\n");
  struct rets r;
  file2code(fname,&r);
  stack code=r.code;
  IdDict preds=r.preds;
  
  stack todo=newStack();
  istack trail=newStack();
  istack ustack=newStack();
  
  long l=size(code);
  term goal=getGoal();
  term answer=left(goal);
  
  push(todo,newAction(DO,goal,NIL,0,size(code),htop));
  
  while(!isEmpty(todo)) {
    if(!fuel--) exit(1);
    //n();pph();n();n();printf("TRAIL\n");ppts(trail);printf("END\n");
    action a=pop(todo);
    //printf("\nACTION: ");ppa(a);n();
    ACT op=a->act;
    long i=a->i;
    term G=a->G;
    term oldG=a->OldG;
    long ttop=a->ttop;
    term  ht=a->ht;
    XFREE(a);
    if (DO==op) {
      action r=step(G,0,code,trail,ustack,preds);
      if(i<l) push(todo,newAction(UNDO,oldG,NIL,ttop,i,ht));
      if(r) push(todo,r);
    }
    else if (DONE==op) {
      if (i<l) push(todo,newAction(UNDO,oldG,NIL,ttop,i,ht));
      printf("ANSWER: ");pp(answer);n();
      printf("todo=%lu,trail=%lu,heap=%lu\n\n",
              size(todo),size(trail),htop);
    }
    else {
      //assert(UNDO==op);
      unwind(trail, ttop);
      heapTrim(ht);
      action r=step(G,i,code,trail,ustack,preds);
      if(r) push(todo,r);
    }
  }
}

