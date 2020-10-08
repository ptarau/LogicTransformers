#include "defs.h"
#include "vm.h"
#include "stack.h"
#include "io.h"

static long varctr=0;

term var() {
  term t=XALLOC(1,struct term);
  t->tag=VAR;
  t->pick.var.id=varctr++;
  t->pick.var.val=t;
  return t;
}

long getId(term v) {
  return v->pick.var.id;
}

void setId(term v,long id) {
  v->pick.var.id=id;
}

void bindVar(term v,term t) {
  v->pick.var.val=t;
}

void unbindVar(term v) {
  v->pick.var.val=v;
}

term deref(term x) {
  while(VAR==x->tag) {
    term v=x->pick.var.val;
    if (v==x) {
      return v;
    }
    x=v;
  }
  return x;
}

term pair(const term l,const term r) {
  //term t=(term)malloc(sizeof(struct term));
  term t=XALLOC(1,struct term);
  t->tag=PAIR;
  t->pick.pair.left=l;
  t->pick.pair.right=r;
  return t;
}

term atom(const char *s,long id) {
  //term t=(term)malloc(sizeof(struct term));
  term t=XALLOC(1,struct term);
  t->tag=ATOM;
  t->pick.atom.id=id;
  t->pick.atom.sym=s;
  return t;
}

instr newInstr(OP op,term x1,term x2,term x3) {
  instr ins=XALLOC(1,struct instr);
  ins->op=op;
  ins->x1=x1;
  ins->x2=x2;
  ins->x3=x3;
  return ins;
}

action newAction(ACT act,term G,term OldG,long ttop,long i) {
  action a=XALLOC(1,struct action);
  a->act=act;
  a->G=G;
  a->OldG=OldG;
  a->ttop=ttop;
  a->i=i;
  return a;
}

int unify(term x,term y,stack trail,long umax,stack ustack) {
  //stack ustack=newStack();
  push(ustack,y);
  push(ustack,x);
  
  while (!isEmpty(ustack)) {
    const term x1=deref(pop(ustack));
    const term x2=deref(pop(ustack));
    const int t1=x1->tag;
    const int t2=x2->tag;
    
    if(x1==x2) continue;
    
    if(VAR==t1 && VAR==t2) {
      long i1=getId(x1);long i2=getId(x2);
      if(i1>i2) {
        bindVar(x1,x2);
        if(i1<umax)
          push(trail,x1);
      }
      else {
        bindVar(x2,x1);
        if(i2<umax)
          push(trail,x2);
      }
    }
    else if(VAR==t1) {
      bindVar(x1,x2);
      if(getId(x1)<umax)
        push(trail,x1);
    }
    else if(VAR==t2) {
      bindVar(x2,x1);
      if(getId(x2)<umax)
        push(trail,x2);
    }
    else if(t1!=t2) return 0;
    else if(ATOM==t1) {
      if(x1->pick.atom.id!=x2->pick.atom.id) return 0;
    }
    else if(NUM==t1) {
      if(x1->pick.num.whole!=x2->pick.num.whole) return 0;
    }
    else {
      term a1=x1->pick.pair.left;
      term b1=x1->pick.pair.right;
      term a2=x2->pick.pair.left;
      term b2=x2->pick.pair.right;
      push(ustack,b2);
      push(ustack,b1);
      push(ustack,a2);
      push(ustack,a1);
    }
  }
  return 1;
}

void unwind(stack trail,long ttop) {
  long i=size(trail)-ttop;
  while(i>0) {
    term v=pop(trail);
    unbindVar(v);
    i-=1;
  }
}

term activate(term t,term *vars) {
  if(NULL==t){return NULL;}
  int tag=t->tag;
  if(VAR == tag) {
    long i=getId(t);
    if(NULL!=vars[i]) {
      term v=vars[i];
      return v;
    }
    else {
      term v=var();
      vars[i]=v;
      return v;
    }
  }
  else {
    assert(ATOM==tag);
    return t;
  }
}

void activate_instr(instr templ,instr ins,term *vars) {
  ins->op=templ->op;
  //printf("!!!!!!!!!!!!!! %d",ins->op);opn(ins->op);n();
  ins->x1=activate(templ->x1,vars);
  ins->x2=activate(templ->x2,vars);
  ins->x3=activate(templ->x3,vars);
}

void clean_choice(term *vars,term *pairs) {
  long k=0;
  while(1) {
    term z=vars[k];
    if(NULL==z) break;
    vars[k++]=NULL;
    XFREE(z);
  }
  
  k=0;
  while(1) {
    term z=pairs[k];
    if(NULL==z) break;
    vars[k++]=NULL;
    XFREE(z);
  }
  
}

long fuel=1000000000;

action step(term G,long i,stack code,stack trail,stack ustack) {
  long ttop=size(trail);
  long umax=varctr;
  struct instr ins;
  
  while(i<size(code)) {
    varctr=umax;
    if(!fuel--) exit(1);
    unwind(trail,ttop);
    clearStack(ustack);
    
    stack clause=at(code,i++);

    term *vars=getRegs();
    term *pairs=getPairs();
    clean_choice(vars,pairs);
    for(long j=0;j<size(clause);j++) {
      instr templ=at(clause,j);
      activate_instr(templ,&ins,vars);
      long m=0;
      //printf("EXEC STEP: j=%ld ",j);ppi(&ins);n();
      OP op=ins.op;
      if(U==op) {
        //printf("%ld\n",ins.x3);
        term old=deref(ins.x3);
        if(VAR==old->tag) {
          term p=pair(ins.x1,ins.x2);
          bindVar(old,p);
          pairs[m++]=p;
          //if(getId(old)<umax) {push(trail,old);}
        }
        else {
          assert(PAIR==old->tag);
          int ok=unify(ins.x1, old->pick.pair.left,trail,umax,ustack);
          if(ok) ok=unify(ins.x2, old->pick.pair.right,trail,umax,ustack);
          if(!ok) {
            //clean_choice(vars,pairs);
            break;
          }
        }
      }
      else if(B==op) {
        term p=pair(ins.x1,ins.x2);
        //term p=pair(deref(ins.x1),deref(ins.x2));
        bindVar(ins.x3,p);
        //pairs[m++]=p;
      }
      else if(D==op) {
        bindVar(ins.x1,G);
      }
      else if(P==op) {
        term NewG=deref(ins.x1);
        if(VAR==NewG->tag) {
          return newAction(DONE,NULL,G,ttop,i);
        }
        else {
          return newAction(DO,NewG,G,ttop,i);
        }
      }
    }
  }
  return newAction(FAIL,NULL,NULL,ttop,i);
}

term getGoal() {
  varctr=0;
  term answer=var();
  term cont=var();
  term goal=atom("goal",0);
  term cpair=pair(cont,goal);
  term tpair=pair(answer,cpair);
  return tpair;
}

void interp() {
  printf("STARTING\n");
  stack todo=newStack();
  stack trail=newStack();
  stack ustack=newStack();
  stack code=file2code(fname);
 
  long l=size(code);
  term goal=getGoal();
  term answer=goal->pick.pair.left;
  
  //if TR pp(goal);n();
 
  push(todo,newAction(DO,goal,NULL,0,size(code)));
  
  while(!isEmpty(todo)) {
    if(!fuel--) exit(1);
    
    action a=pop(todo);
    
    //printf("ACTION: ");ppa(a);n();
    
    ACT op=a->act;
    long i=a->i;
    term G=a->G;
    term oldG=a->OldG;
    long ttop=a->ttop;
    
    XFREE(a);
    
    //printf("DOING: todo[%ld], i=%ld : ",i,size(todo)-1);sp();ppa(a);n();
    
    if (DO==op) {
      action r=step(G,0,code,trail,ustack);
      //printf("r:-------");ppa(r);n();
      if(i<l) {
        push(todo,newAction(UNDO,oldG,NULL,ttop,i));
      }
      push(todo,r);
    }
    
    else if (DONE==op) {
      if (i<l) {
        push(todo,newAction(UNDO,oldG,NULL,ttop,i));
      }
      {printf("ANSWER: ");pp(answer);n();}
    }
    
    else if (UNDO==op) {
      unwind(trail, ttop);
      push(todo,step(G,i,code,trail,ustack));
    }
    
    else if (FAIL==op) {
      //printf("FAILING");
      continue;
    }
  }
}

