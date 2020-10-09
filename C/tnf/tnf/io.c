#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "io.h"
#include "defs.h"
#include "stack.h"
#include "dict.h"
#include "vm.h"

void n() {
  printf("\n");
}

void sp() {
  printf(" ");
}

/*
static char* tn(TAG op) {
  char *ops[4]={"VAR","PAIR","ATOM","NUM"};
  return ops[op];
}
*/

char* opn(OP op) {
  char *ops[4]={"D","U","B","P"};
  return ops[op];
}

static char* actn(ACT op) {
  char *ops[4]={"FAIL","DO","DONE","UNDO"};
  return ops[op];
}

void pp(term t) {
  //printf("!!! %ld\n",(long)t);
  t=deref(t);
  switch(t->tag) {
  case VAR : {
    printf("_");
    printf("%ld",getId(t));
    break;
  }
  case ATOM: {
    printf("%s",t->pick.atom.sym);
    break;
  }
  case PAIR : {
    printf("(");
    pp(t->pick.pair.left);
    printf("=>");
    pp(t->pick.pair.right);
    printf(")");
    break;
  }
  }
}

void ppi(instr ins) {
  printf("%s ",opn(ins->op));
  pp(ins->x1);
  if(NULL==ins->x2) return;
  printf(" ");
  pp(ins->x2);printf(" ");
  pp(ins->x3);
}

void ppa(action a) {
  printf("%s ",actn(a->act));sp();
  printf("G=");if(NULL!=a->G) {pp(a->G);sp();} else printf("NULL ");
  printf("OldG=");if(NULL!=a->OldG) {pp(a->OldG);sp();} else printf("NULL ");
  printf("tr=%ld clause=%ld\n",a->ttop,a->i);
}


void ppc(stack clause) {
  long l=size(clause);
  for(long i=0; i<l; i++) {
    instr ins = at(clause,i);
    //printf("INSTR: ");ppi(ins);n();
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
      //printf("tok %c\n",tok[j]);
      tok[j++]=c;
    }
  }
  toks[i++]=NULL;
  return toks;
}

int eq(const char *s,const char*t) {
  return 0==strcmp(s,t);
}

long str2id(Dict d,stack s,char *w) {
  const long id=dictGet(d,w);
  if(NOT_FOUND==id) {
    const long n=dictCount(d);
    dictPut(d,w,n);
    push(s,w);
    return n;
  }
  return id;
}

term va(char *w,Dict vars,stack vids,Dict syms,stack syds) {
  char c=w[0];
  if(isupper(c)) {
    long id=str2id(vars,vids,w);
    term v=var();
    setId(v,id);
    //printf("VAR: ");pp(v);printf("\n");
    return v;
  }
  else {
    long id=str2id(syms,syds,w);
    term a=atom(w,id);
    //printf("ATOM: ");pp(a);printf("\n");
    return a;
  };
}

static long reglen=0;

static term *regs;
static term *pairs;

void makeRegs() {
  regs=XALLOC(reglen,term);
  pairs=XALLOC(reglen,term);
  //getRegs();
}

term *getRegs() {
  for(long i=0;i<reglen;i++) {
    //if(NULL==regs[i]) break;
    //XFREE(regs[i]);
    regs[i]=NULL;
  }
  return regs;
}

term *getPairs() {
  for(long i=0;i<reglen;i++) {
    //if(NULL==pairs[i]) break;
    //XFREE(pairs[i]);
    pairs[i]=NULL;
  }
  return pairs;
}


stack file2code(char *fname) {
   char **toks = file2toks(fname);
  
  stack code=newStack();
  Dict syms=newDict();
  stack syds=newStack();
  
  stack clause=newStack();
  Dict vars=newDict();
  stack vids=newStack();
  
  
  term goal=va("goal",vars,vids,syms,syds);
  if TR printf("GOAL ID: %ld\n",goal->pick.atom.id);
  
  int i=0;
  char *tok;
  
  while((tok=toks[i++])) {
    if(NULL==tok) break;
    else if(eq("d",tok)) {
      OP op=D;
      term x1=va(toks[i++],vars,vids,syms,syds);
      //term x2=NULL;
      //term x3=NULL;
      term x2=va(toks[i++],vars,vids,syms,syds);
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
      //term x2=NULL;
      //term x3=NULL;
      term x2=va(toks[i++],vars,vids,syms,syds);
      term x3=va(toks[i++],vars,vids,syms,syds);
      instr ins=newInstr(op,x1,x2,x3);
      push(clause,ins);
      push(code,clause);
      if TR {ppc(clause);}
      
      long l=size(vids);
      reglen=(reglen<l)?l:reglen;
      
      clause=newStack();
      vars=newDict();
      vids=newStack();
    }
    else {
      printf("*** UNEXPECTED token:%s\n",tok);
      i++;
    }
  }
  printf("######### length of regs %ld\n",reglen);
  makeRegs();
  return code;
}
