#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "io.h"
#include "defs.h"
#include "istack.h"
#include "dict.h"
#include "idict.h"
#include "vm.h"

void n() {
  printf("\n");
}

void sp() {
  printf(" ");
}

char* opn(OP op) {
  char *ops[4]={"D","U","B","P"};
  return ops[op];
}

static char* actn(ACT op) {
  char *ops[4]={"FAIL","DO","DONE","UNDO"};
  return ops[op];
}

stack gsyds=NULL;

void p(const term  v) {
  term  x=deref(v);
  term  t=tag(x);
  
  switch(t) {
  case HNIL:
    printf("NIL");break;
  case VAR:
    printf("_%lu",vid(x));
    break;
  case PAIR:
    printf("(");
    p(left(x));
    printf("=>");
    p(right(x));
    printf(")");
    break;
  case ATOM: {
    term  i=aval(x);
    printf("%s",at(gsyds,i));
    //printf("%s%lu:","#",i);
  }
    break;
  default:
    printf("OTHER %lu\n:%lu",x,t);
  }
}

void pp(term t) {
  p(t);
}

void pterm (term  x) {
  term  t=tag(x);
  
  switch(t) {
  case HNIL:
    printf("NIL %lu\n",x);break;
  case VAR:
    printf("VAR %lu -> <%u>%lu\n",vid(x),tag(x),vid(vget(x)));
    break;
  case PAIR: {
    term  l=left(x);term  r=right(x);
    printf("(<%u>%lu , <%u>%lu)\n",tag(l),vid(l),tag(r),vid(r));
  }
    break;
  case ATOM:
    printf("ATOM %lu\n",aval(x));
    break;
  default:
    printf("OTHER %lu\n:%lu",x,t);
  }
}


void ppi(instr ins) {
  printf("%s ",opn(ins->op));
  pp(ins->x1);
  if(NIL==ins->x2) return;
  printf(" ");
  pp(ins->x2);printf(" ");
  pp(ins->x3);
}

void ppa(action a) {
  printf("%s ",actn(a->act));sp();
  printf("G=");if(NIL!=a->G) {pp(a->G);sp();} else printf("NIL ");
  printf("OldG=");if(NIL!=a->OldG) {pp(a->OldG);sp();} else printf("NIL ");
  printf("tr=%ld clause=%ld\n",a->ttop,a->i);
}


void ppc(stack clause) {
  long l=size(clause);
  for(long i=0; i<l; i++) {
    instr ins = at(clause,i);
    printf("INSTR: ");ppi(ins);n();
  }
}

void ppts(istack s) {
  long l=size(s);
  for(long i=0; i<l; i++) {
    term t = iat(s,i);
    printf("VAR: ");pp(t);n();
  }
}

char **file2toks(char *fname) {
  static char *toks[1<<16];
  FILE *fp=fopen(fname,"r");
  char c;
  char tok[1<<10];
  int i=0;
  int j=0;
  while(1) {
    c=fgetc(fp);
    if(feof(fp)) break;
    else if(' '==c || '\n'==c) {
      tok[j++]='\0';
      char *word=XALLOC(j+1,char);
      strcpy(word,tok);
      toks[i++]=word;
      j=0;
    }
    else {
      tok[j++]=c;
    }
  }
  toks[i++]=NULL;
  return toks;
}

int eq(const char *s,const char*t) {
  return 0==strcmp(s,t);
}

long str2id(Dict d,stack s,char *w,int *isnew) {
  const long id=dictGet(d,w);
  if(NOT_FOUND==id) {
    const long n=dictCount(d);
    dictPut(d,w,n);
    push(s,w);
    *isnew=1;
    return n;
  }
  return id;
}

term va(char *w,Dict vars,stack vids,Dict syms,stack syds) {
  int isnew=0;
  if(!w) return NIL;
  char c=w[0];
  if(isupper(c)||c=='_') {
    long id=str2id(vars,vids,w,&isnew);
    term v;
    if(isnew) {
      v=asVar(id);
      return v;
    }
    else {
      v=asRef(id);
      return v;
    }
  }
  else {
    long id=str2id(syms,syds,w,&isnew);
    term a=atom(id);
    return a;
  };
}

instr newInstr(OP op,term x1,term x2,term x3) {
  instr ins=XALLOC(1,struct instr);
  ins->op=op;
  ins->x1=x1;
  ins->x2=x2;
  ins->x3=x3;
  return ins;
}

void add_to_pred(IdDict preds,long key,long val) {
  istack vals;
  if(inIdDict(preds,key)) {
    vals=(stack)gIdDictGet(preds,key);
  }
  else {
    vals=newStack();
    gIdDictPut(preds,key,vals);
  }
  //printf("PUSH----------%lu\n",val);
  ipush(vals,val);
}

void file2code(char *fname,rets r) {
   char **toks = file2toks(fname);
  
  stack code=newStack();
  Dict syms=newDict();
  stack syds=newStack();
  gsyds=syds;
  
  stack clause=newStack();
  Dict vars=newDict();
  stack vids=newStack();
  IdDict preds=newIdDict();
  long i=0;
  long cls=0;
  
  term goal=va("goal",vars,vids,syms,syds);
  
  char *tok;
  
  while((tok=toks[i++])) {
    if(NULL==tok) break;
    else if(eq("d",tok)) {
      OP op=D;
      term x1=va(toks[i++],vars,vids,syms,syds);
      //term x2=NIL;
      //term x3=NIL;
      term x2=va(toks[i++],vars,vids,syms,syds);
      add_to_pred(preds,x2,cls++);
      term x3=va(toks[i++],vars,vids,syms,syds);
      instr ins=newInstr(op,x1,x2,x3);
      push(clause,ins);
    }
    else if(eq("u",tok)) {
      OP op=U;
      term x1=va(toks[i++],vars,vids,syms,syds);
      term x2=va(toks[i++],vars,vids,syms,syds);
      term x3=va(toks[i++],vars,vids,syms,syds);
      instr ins=newInstr(op,x1,x2,x3);
      push(clause,ins);
    }
    else if(eq("b",tok)) {
      OP op=B;
      term x1=va(toks[i++],vars,vids,syms,syds);
      term x2=va(toks[i++],vars,vids,syms,syds);
      term x3=va(toks[i++],vars,vids,syms,syds);
      instr ins=newInstr(op,x1,x2,x3);
      push(clause,ins);
    }
    else if(eq("p",tok)) {
      OP op=P;
      term x1=va(toks[i++],vars,vids,syms,syds);
      //term x2=NIL;
      //term x3=NIL;
      term x2=va(toks[i++],vars,vids,syms,syds);
      term x3=va(toks[i++],vars,vids,syms,syds);
      instr ins=newInstr(op,x1,x2,x3);
      push(clause,ins);
      push(code,clause);
      //long l=size(vids);
      
      clause=newStack();
      vars=newDict();
      vids=newStack();
    }
    else {
      printf("*** UNEXPECTED token:%s\n",tok);
      i++;
    }
  }
  //printf("######### length of regs %ld\n",reglen);
  
  r->goal=goal;
  r->code=code;
  r->syds=syds;
  r->preds=preds;
  
  
}
