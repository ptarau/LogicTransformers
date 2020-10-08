#ifndef io_h
#define io_h

#include <stdio.h>
#include "stack.h"

void pp(term t);

void ppi(instr ins);

void ppc(stack s);

void ppa(action a);

char *opn(OP op);

void n(void);

void sp(void);

char **file2toks(char *fname);

stack file2code(char *fname);

void makeRegs(void);

term *getRegs(void);

term *getPairs(void);

#endif /* io_h */
