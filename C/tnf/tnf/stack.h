#ifndef stack_h
#define stack_h

#include "defs.h"
#include "vm.h"

typedef struct stackholder {
  long capacity;
  long top;
  Any *array;
}
*stack;

stack newStack(void);

void freeStack(stack s);

long isEmpty(stack s);

void push(stack s,Any i);

Any pop(stack s);

Any peek(stack s);

Any at(stack s,long i);

long size(stack s);

void clearStack(stack s);

#endif /* stack_h */
