#ifndef vm_h
#define vm_h

typedef struct term {
  int tag;
  union pick {
    struct var {
      struct term *val;
      long id;
    } var;
    struct pair {
      struct term *left;
      struct term *right;
    } pair;
    struct atom {
      long id;
      const char *sym;
    } atom;
    struct num {
      const long whole;
      const double dec;
    } num;
  } pick;
} *term;

typedef enum TAGS {
  VAR,
  PAIR,
  ATOM,
  NUM
} TAG;

typedef enum OPS {
  D,
  U,
  B,
  P
} OP;

typedef enum ACTS {
  FAIL,
  DO,
  DONE,
  UNDO
} ACT;

typedef struct instr {
  OP op;
  term x1;
  term x2;
  term x3;
} *instr;

typedef struct action {
  ACT act;
  term G;
  term OldG;
  long ttop;
  long i;
} *action;

term var(void);
long getId(term);
void setId(term,long);
term atom(const char *,long id);
term pair(const term l,const term r);
term deref(term t);
instr newInstr(OP op,term x1,term x2,term x3);

action newAction(ACT act,term G,term OldG,long ttop,long i);

void interp(void);

#endif /* vm_h */
