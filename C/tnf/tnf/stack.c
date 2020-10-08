#include "defs.h"
#include "vm.h"
#include "stack.h"

static long MINSIZE = 1<<4;

static inline Any *makeArray(long size) {
  return XALLOC(size,Any);
}

stack newStack() {
  stack s=XALLOC(1,struct stackholder);
  s->capacity=MINSIZE;
  s->array=makeArray(s->capacity);
  s->top= -1;
  return s;
}

void freeStack(stack s) {
  XFREE(s->array);
  XFREE(s);
}

long isEmpty(stack s) {
  return s->top<0;
}

long size(stack s) {
  return s->top+1;
}

void maybe_expand(stack s) {
  if(s->top+1>=s->capacity) {
  
    s->capacity=s->capacity<<1; // *2
    
    Any *oldarray=s->array;
    s->array=makeArray(s->capacity);
    { long i; // copying old stack
      for(i=0;i<=s->top;i++) {
        s->array[i]=oldarray[i];
      }
    }
    XFREE(oldarray); // avoids memory leaks
    
    //s->array=RALLOC(s->array,s->capacity,Any);
    //assert(s->array);
  }
}

void maybe_shrink(stack s) {
  if(s->top-1<s->capacity>>2 && s->capacity>>1>MINSIZE) { // div by 4
    
     s->capacity=s->capacity>>1; // div by 2
    
    Any *oldarray=s->array;
    s->array=makeArray(s->capacity);
    { long i; // copying old stack
      for(i=0;i<=s->top;i++) {
        s->array[i]=oldarray[i];
      }
    }
    XFREE(oldarray); // avoids memory leaks
    
    //s->array=RALLOC(s->array,s->capacity,Any);
    //assert(s->array);
  }
}

void push(stack s,Any t) {
  maybe_expand(s);
  s->array[++s->top]=t;
}

Any pop(stack s) {
  //maybe_shrink(s);
  return s->array[s->top--];
}

Any peek(stack s) {
  return s->array[s->top];
}

Any at(stack s,long i) {
  assert (i>=0 && i<=s->top);
  return s->array[i];
}

void clearStack(stack s) {
  s->top = -1;
}



