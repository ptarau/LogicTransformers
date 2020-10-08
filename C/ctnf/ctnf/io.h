#ifndef io_h
#define io_h

#include <stdio.h>
#include "istack.h"
#include "dict.h"
#include "idict.h"

typedef struct rets {
  term goal;
  stack code;
  stack syds;
  IdDict preds;
} *rets;

void pp(term t);

void ppi(instr ins);

void ppc(stack s);

void ppa(action a);

void ppts(istack s);

char *opn(OP op);

void n(void);

void sp(void);

char **file2toks(char *fname);

void file2code(char *fname,rets);

void pterm(term x);

#endif /* io_h */
