#include <stdio.h>
#include <assert.h>

#include "tests.h"
#include "dict.h"
#include "vm.h"
#include "io.h"
#include "stack.h"

void t1() {
  printf("\nt1\n");
  int size = sizeof(struct pair);
  struct term t;
  printf("%d\n",size);
  printf("term %ld\n",sizeof(struct term));
  //printf("long %ld\n",sizeof((struct term).pair));
  
  t.tag=4;
  t.pick.atom.id=3;
}

void t2() {
  printf("\nt2\n");
  term a=atom("hello",0);
  term v=var();
  term p=pair(a,v);
  printf("%lu\n",sizeof(p));
  const char *s=p->pick.pair.left->pick.atom.sym;
  printf("%s\n",s);
}

void t3a() {
  printf("\nt3a\n");
  char **toks=file2toks(fname);
  printf("FIRST:%s\n",toks[0]);
  printf("NEXT :%s\n",toks[1]);
  printf("NEXT :%s\n",toks[2]);
  printf("NEXT:%s\n",toks[12]);
  printf("NEXT:%s\n",toks[22]);
  int i=0;
  while(1) {
    char *tok=toks[i];
    if(NULL==tok) break;
    //printf("%s",tok);
    i++;
  }
  printf("code len=%d\n",i);
}

void t3() {
  printf("\nt3\n");
  stack code=file2code(fname);
  printf("code len=%ld\n",size(code));
}


void stack_test() {
  printf("\nstack_test\n");
  stack s=newStack();
  push(s,"hello");
  char *x=pop(s);
  printf("POPPED %s\n",x);
}

void tests() {
  t1();
  t2();
  dict_test();
  stack_test();
  t3a();
  t3();
}

int dict_test() {
  printf("\ndict_test\n");
  Dict d;
  char buf[1<<12];
  d = newDict();
  dictPut(d, "foo", 999);
  printf("%ld\n",dictGet(d, "foo"));
  dictPut(d, "foo", 88);
  printf("%ld\n",dictGet(d, "foo"));
  dictDel(d, "foo");
  printf("%ld\n",dictGet(d, "foo"));
  dictDel(d, "foo");
  assert(dictGet(d, "foo") == NOT_FOUND);
  dictDel(d, "foo");
  
  for(long i = 0; i < 10000; i++) {
    sprintf(buf, "%ld", i);
    dictPut(d, buf, i);
  }
  printf("%ld / %ld\n",dictCount(d),dictSize(d));
  printf("%ld\n",dictGet(d,"888"));
  printf("%ld\n",dictGet(d,"-1"));
  
  freeDict(d);
  
  return 0;
}

