#ifndef vm_h
#define vm_h
typedef unsigned long term ;

static const term  NIL=0ul;

#define SHIFT 3

#define HNIL 0
#define  ATOM 1
#define PAIR 2
#define  VAR 3
#define  REF 4

#define MASK 7


void hinit(void);

term  var(void);

term  asVar(term );

term  asRef(term );

term  asPair(term );

term  vget(term  v);

term  vid(term  v);

void vset(term  x,term  val);

term  deref(term  x);

term  pair(term  x,term  y);

term  left(term  p);

term  right(term  p);

term  atom(term  a);

term  aval(term  a);

int tag(term  p);

void pph(void);

void p(term );

void htest(void);

typedef unsigned long term;

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
  term  ht;
} *action;


void interp(void);

#endif /* vm_h */
