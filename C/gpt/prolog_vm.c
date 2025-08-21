
// prolog_vm.c
// Heap-tagged 64-bit Prolog-like engine loading postfix program (bnf_asm*.txt).
// Prints CLS/LINE during load and prints full answers, including lists.
//
// Build: cc -O3 -std=c11 -Wall -Wextra -o prolog_vm prolog_vm.c
// Run:   ./prolog_vm [bnf_asm.txt]
//
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <inttypes.h>

typedef uint64_t term;

#define SHIFT 3u
#define MASK  ((term)7u)

#define ATOM 1u
#define PAIR 2u
#define VAR  3u

#define NIL ((term)0u)

// ---------- tag/val ----------
inline static term tag_u(term x, unsigned t){ return (x<<SHIFT)|(term)t; }
inline static unsigned tag_of(term x){ return (unsigned)(x & MASK); }
inline static term val_of(term x){ return x >> SHIFT; }

// ---------- heap ----------
typedef struct { term *data; size_t cap, top; } Heap;
static Heap HEAP;

inline static void heap_init(Heap *h, size_t cap){
    h->data=(term*)malloc(cap*sizeof(term));
    if(!h->data){fprintf(stderr,"OOM heap\n"); exit(1);}
    h->cap=cap; h->top=0;
}
inline static void heap_reserve(Heap *h, size_t need){
    if(h->top+need<=h->cap) return;
    size_t n=h->cap?h->cap:1024; while(n<h->top+need) n<<=1;
    term*nd=(term*)realloc(h->data,n*sizeof(term));
    if(!nd){fprintf(stderr,"OOM heap grow\n"); exit(1);}
    h->data=nd; h->cap=n;
}
inline static size_t heap_alloc_cell(Heap *h){
    heap_reserve(h,1); return h->top++;
}
inline static size_t heap_alloc2(Heap *h){
    heap_reserve(h,2); size_t base=h->top; h->top+=2; return base;
}

inline static term make_pair(term a, term d){
    size_t k=heap_alloc2(&HEAP);
    HEAP.data[k]=a; HEAP.data[k+1]=d;
    return tag_u((term)k, PAIR);
}
inline static term left(term p){ return HEAP.data[(size_t)val_of(p)]; }
inline static term right(term p){ return HEAP.data[(size_t)val_of(p)+1]; }

// VAR cell: allocate one heap cell and set self-ref VAR(i)
inline static term make_var(void){
    size_t i=heap_alloc_cell(&HEAP);
    HEAP.data[i]=tag_u((term)i, VAR);
    return tag_u((term)i, VAR);
}

// deref: follow bindings; unbound when heap[i] == VAR(i)
inline static term deref(term x){
    while(tag_of(x)==VAR){
        size_t i=(size_t)val_of(x);
        term w=HEAP.data[i];
        if(tag_of(w)==VAR && val_of(w)==(term)i) return x; // unbound
        x=w; // alias or bound
    }
    return x;
}

// ---------- trail ----------
typedef struct{ size_t*data; size_t cap, top; } Trail;
inline static void trail_init(Trail*t,size_t cap){
    t->data=(size_t*)malloc(cap*sizeof(size_t));
    if(!t->data){fprintf(stderr,"OOM trail\n"); exit(1);}
    t->cap=cap; t->top=0;
}
inline static void trail_push(Trail*t,size_t i){
    if(t->top==t->cap){
        size_t n=t->cap?t->cap<<1:1024;
        size_t*nd=(size_t*)realloc(t->data,n*sizeof(size_t));
        if(!nd){fprintf(stderr,"OOM trail grow\n"); exit(1);}
        t->data=nd; t->cap=n;
    }
    t->data[t->top++]=i;
}
inline static void unwind_to(Trail*t,size_t tmark){
    while(t->top>tmark){
        size_t i=t->data[--t->top];
        HEAP.data[i]=tag_u((term)i, VAR);
    }
}
inline static void trim_heap(size_t hmark){ HEAP.top=hmark; }

// ---------- unify (iterative) ----------
typedef struct{ term a,b; } Pair;
typedef struct{ Pair*data; size_t cap, top; } PStack;
inline static void ps_init(PStack*s,size_t cap){
    s->data=(Pair*)malloc(cap*sizeof(Pair));
    if(!s->data){fprintf(stderr,"OOM ps\n"); exit(1);}
    s->cap=cap; s->top=0;
}
inline static void ps_push(PStack*s, term a, term b){
    if(s->top==s->cap){
        size_t n=s->cap?s->cap<<1:1024;
        Pair*nd=(Pair*)realloc(s->data,n*sizeof(Pair));
        if(!nd){fprintf(stderr,"OOM ps grow\n"); exit(1);}
        s->data=nd; s->cap=n;
    }
    s->data[s->top++]=(Pair){a,b};
}
inline static int ps_pop(PStack*s, Pair*out){
    if(!s->top) return 0; *out=s->data[--s->top]; return 1;
}

// htop: heap top BEFORE starting unify (for trailing older vars only)
inline static int unify_htop(term X, term Y, Trail*trail, size_t htop){
    PStack st; ps_init(&st,128);
    ps_push(&st,X,Y);
    Pair p;
    while(ps_pop(&st,&p)){
        term a=deref(p.a), b=deref(p.b);
        if(a==b) continue;
        unsigned ta=tag_of(a), tb=tag_of(b);
        if(ta==VAR && tb==VAR){
            size_t ia=(size_t)val_of(a), ib=(size_t)val_of(b);
            if(ia>ib){ HEAP.data[ia]=tag_u((term)ib,VAR); if(ia<htop) trail_push(trail,ia); }
            else     { HEAP.data[ib]=tag_u((term)ia,VAR); if(ib<htop) trail_push(trail,ib); }
        }else if(ta==VAR){
            size_t i=(size_t)val_of(a); HEAP.data[i]=b; if(i<htop) trail_push(trail,i);
        }else if(tb==VAR){
            size_t i=(size_t)val_of(b); HEAP.data[i]=a; if(i<htop) trail_push(trail,i);
        }else if(ta==ATOM && tb==ATOM){
            if(val_of(a)!=val_of(b)){ free(st.data); return 0; }
        }else if(ta==PAIR && tb==PAIR){
            ps_push(&st,left(a),left(b)); ps_push(&st,right(a),right(b));
        }else if(a==NIL && b==NIL){
            // ok
        }else{ free(st.data); return 0; }
    }
    free(st.data); return 1;
}

// ---------- atoms ----------
typedef struct{ char*s; uint64_t id; } SymEnt;
typedef struct{ SymEnt*tab; size_t cap, sz; } SymTable;
static SymTable SYMS;
static uint64_t LISTCONS_ID = 0; // intern("[|]")

static uint64_t fnv1a(const char*s){
    uint64_t h=1469598103934665603ull; for(;*s;++s){ h^=(unsigned char)*s; h*=1099511628211ull; } return h;
}
inline static void syms_init(SymTable*st,size_t cap){
    st->cap=cap?cap:1024; st->sz=0; st->tab=(SymEnt*)calloc(st->cap,sizeof(SymEnt));
    if(!st->tab){fprintf(stderr,"OOM syms\n"); exit(1);}
}
inline static void syms_grow(SymTable*st){
    size_t n=st->cap<<1; SymEnt*nt=(SymEnt*)calloc(n,sizeof(SymEnt));
    if(!nt){fprintf(stderr,"OOM syms grow\n"); exit(1);}
    for(size_t i=0;i<st->cap;i++) if(st->tab[i].s){
        uint64_t h=fnv1a(st->tab[i].s); size_t j=(size_t)(h & (n-1));
        while(nt[j].s) j=(j+1)&(n-1); nt[j]=st->tab[i];
    }
    free(st->tab); st->tab=nt; st->cap=n;
}
inline static uint64_t sym_intern(const char*s){
    if(!SYMS.cap) syms_init(&SYMS,1024);
    if((SYMS.sz<<1)>=SYMS.cap) syms_grow(&SYMS);
    uint64_t h=fnv1a(s); size_t i=(size_t)(h & (SYMS.cap-1));
    for(;;){
        SymEnt*e=&SYMS.tab[i];
        if(!e->s){ e->s=strdup(s); if(!e->s){fprintf(stderr,"OOM strdup\n"); exit(1);} e->id=++SYMS.sz; return e->id; }
        if(strcmp(e->s,s)==0) return e->id;
        i=(i+1)&(SYMS.cap-1);
    }
}
inline static const char* sym_name(uint64_t id){
    for(size_t i=0;i<SYMS.cap;i++) if(SYMS.tab[i].s && SYMS.tab[i].id==id) return SYMS.tab[i].s;
    return "?";
}
inline static term make_atom(const char*s){ return tag_u(sym_intern(s), ATOM); }

// ---------- generic term printer (with list sugar) ----------
static int is_list_end(term t){
    t = deref(t);
    if(tag_of(t)!=PAIR) return 0;
    term a = deref(left(t));
    term d = deref(right(t));
    if(a!=NIL) return 0;
    return (tag_of(d)==ATOM && val_of(d)==LISTCONS_ID);
}

static int try_print_list(term t){
    // list is nested PAIR where tail finally is ( [] => [|] )
    // Each cell: (head => tail)
    t = deref(t);
    if(tag_of(t)!=PAIR) return 0;
    // We'll scan and collect; if pattern breaks, return 0 and do not print
    // But we don't need to store; we can print streaming
    // First, check if there is at least one element and proper end
    term cur = t;
    // validate
    while(1){
        cur = deref(cur);
        if(tag_of(cur)!=PAIR) return 0;
        term tail = deref(right(cur));
        if(is_list_end(tail)) break;
        if(tag_of(tail)!=PAIR) return 0;
        cur = tail;
    }
    // print
    putchar('[');
    int first = 1;
    cur = t;
    while(1){
        term h = deref(left(cur));
        if(!first) printf(",");
        // recursive print of element
        // forward decl
        void print_term(term);
        print_term(h);
        term tail = deref(right(cur));
        if(is_list_end(tail)) break;
        cur = tail;
        first = 0;
    }
    putchar(']');
    return 1;
}

// forward decl
void print_term(term t);

void print_term(term t){
    t = deref(t);
    if(t==NIL){ printf("[]"); return; }
    unsigned k = tag_of(t);
    if(k==ATOM){ printf("%s", sym_name(val_of(t))); return; }
    if(k==VAR){ printf("_%zu", (size_t)val_of(t)); return; }
    if(k==PAIR){
        if(try_print_list(t)) return;
        putchar('(');
        print_term(left(t));
        printf("=>");
        print_term(right(t));
        putchar(')');
        return;
    }
    printf("?");
}

// ---------- clause printing (clause-local var numbers) ----------
static void print_term_local_rec(term t, size_t begin, size_t end,
                                 int64_t *vmap, int *vcount);

static void print_pair_local(term t, size_t begin, size_t end,
                             int64_t *vmap, int *vcount){
    putchar('(');
    term a = left(t);
    term b = right(t);
    print_term_local_rec(a, begin, end, vmap, vcount);
    printf("=>");
    print_term_local_rec(b, begin, end, vmap, vcount);
    putchar(')');
}

static void print_term_local_rec(term t, size_t begin, size_t end,
                                 int64_t *vmap, int *vcount){
    t=deref(t);
    if(t==NIL){ printf("[]"); return; }
    unsigned k=tag_of(t);
    if(k==ATOM){ printf("%s", sym_name(val_of(t))); return; }
    if(k==PAIR){ print_pair_local(t, begin, end, vmap, vcount); return; }
    if(k==VAR){
        size_t i=(size_t)val_of(t);
        if(i<begin || i>=end){ printf("_%zu", i); return; }
        size_t off=i-begin;
        if(vmap[off]<0){ vmap[off]=(*vcount)++; }
        printf("_%lld",(long long)vmap[off]);
        return;
    }
    printf("?");
}

static void print_clause_local(term hb, size_t begin, size_t end){
    size_t n = (end>begin)? (end-begin) : 0;
    int64_t *vmap = (int64_t*)malloc(sizeof(int64_t)* (n));
    if(!vmap){fprintf(stderr,"OOM vmap print\n"); exit(1);}
    for(size_t i=0;i<n;i++) vmap[i]=-1;
    int vcount=0;
    print_term_local_rec(hb, begin, end, vmap, &vcount);
    free(vmap);
}

// ---------- Program / Clause ----------
typedef struct{ term hb; size_t begin, end; char *line; } Clause;
typedef struct{ Clause*cs; int cap, len; } Program;
static Program PROG;

inline static void prog_init(Program*p){
    p->cap=16; p->len=0; p->cs=(Clause*)malloc(p->cap*sizeof(Clause));
    if(!p->cs){fprintf(stderr,"OOM program\n"); exit(1);}
}
inline static void prog_add_clause(Program*p, term hb, size_t begin, size_t end, const char*line){
    if(p->len==p->cap){ p->cap<<=1; p->cs=(Clause*)realloc(p->cs,p->cap*sizeof(Clause)); if(!p->cs){fprintf(stderr,"OOM program grow\n"); exit(1);} }
    p->cs[p->len++] = (Clause){hb, begin, end, strdup(line)};
}

// ---------- postfix parser (ignore ":-" like Python) ----------
typedef struct{ term*data; int cap, top; } TStack;
inline static void ts_init(TStack*s){ s->cap=16; s->top=0; s->data=(term*)malloc(s->cap*sizeof(term)); if(!s->data){fprintf(stderr,"OOM tstack\n"); exit(1);} }
inline static void ts_push(TStack*s, term t){ if(s->top==s->cap){ s->cap<<=1; s->data=(term*)realloc(s->data,s->cap*sizeof(term)); if(!s->data){fprintf(stderr,"OOM tstack grow\n"); exit(1);} } s->data[s->top++]=t; }
inline static term ts_pop(TStack*s){ if(!s->top){fprintf(stderr,"Parse underflow\n"); exit(1);} return s->data[--s->top]; }
inline static void ts_free(TStack*s){ free(s->data); }

static int is_upper_token(const char*s){ return s[0] && isupper((unsigned char)s[0]); }

// tiny per-line map name->id
typedef struct { char **keys; int *vals; int n, cap; } KVMap;
inline static void kv_init(KVMap*m){ m->n=0; m->cap=16; m->keys=(char**)malloc(m->cap*sizeof(char*)); m->vals=(int*)malloc(m->cap*sizeof(int)); if(!m->keys||!m->vals){fprintf(stderr,"OOM kv\n"); exit(1);} }
inline static void kv_free(KVMap*m){ for(int i=0;i<m->n;i++) free(m->keys[i]); free(m->keys); free(m->vals); }
inline static int kv_get_id(KVMap*m, const char*name){
    for(int i=0;i<m->n;i++) if(strcmp(m->keys[i],name)==0) return m->vals[i];
    if(m->n==m->cap){ m->cap<<=1; m->keys=(char**)realloc(m->keys,m->cap*sizeof(char*)); m->vals=(int*)realloc(m->vals,m->cap*sizeof(int)); if(!m->keys||!m->vals){fprintf(stderr,"OOM kv grow\n"); exit(1);} }
    m->keys[m->n]=strdup(name); if(!m->keys[m->n]){fprintf(stderr,"OOM strdup\n"); exit(1);}
    m->vals[m->n]=m->n;
    return m->n++;
}

// Returns hb term and [begin,end) segment
static term parse_postfix_line(const char*line, size_t*begin_out, size_t*end_out){
    char *buf=strdup(line); if(!buf){fprintf(stderr,"OOM line dup\n"); exit(1);}
    char *save=NULL; char *tok=strtok_r(buf," \t\r\n",&save);

    size_t begin=HEAP.top;
    TStack st; ts_init(&st);
    KVMap kv; kv_init(&kv);

    while(tok){
        if(strcmp(tok,"$")==0){
            term t2=ts_pop(&st), t1=ts_pop(&st);
            ts_push(&st, make_pair(t1,t2));
        }else if(strcmp(tok,":-")==0){
            // ignore
        }else if(strcmp(tok,"[]")==0){
            ts_push(&st, NIL);
        }else if(is_upper_token(tok)){
            int id=kv_get_id(&kv, tok);
            ts_push(&st, tag_u((term)id, VAR));
        }else{
            ts_push(&st, make_atom(tok));
        }
        tok=strtok_r(NULL," \t\r\n",&save);
    }

    term hb=ts_pop(&st);
    ts_free(&st);
    kv_free(&kv);
    free(buf);

    size_t end=HEAP.top;

    // Renumber placeholders to clause-local var cells
    size_t seglen = (end>begin)? (end-begin) : 0;
    size_t *first = (size_t*)malloc(sizeof(size_t)*(seglen+1));
    if(!first){fprintf(stderr,"OOM renum map\n"); exit(1);}
    for(size_t i=0;i<=seglen;i++) first[i]=(size_t)(~0ull);
    for(size_t h=begin; h<end; h++){
        term cell=HEAP.data[h];
        if(tag_of(cell)==VAR){
            size_t pid=(size_t)val_of(cell);
            if(pid>seglen) pid=seglen;
            if(first[pid]==(size_t)(~0ull)){
                first[pid]=h;
                HEAP.data[h]=tag_u((term)h, VAR); // self
            }else{
                HEAP.data[h]=tag_u((term)first[pid], VAR);
            }
        }
    }
    free(first);

    *begin_out=begin; *end_out=end;
    return hb;
}

// ---------- Activation: relocate-copy clause segment ----------
inline static term activate_clause(const Clause*c){
    size_t begin=c->begin, end=c->end;
    size_t htop=HEAP.top;
    size_t off=htop - begin;
    size_t need=end-begin;
    heap_reserve(&HEAP, need);
    for(size_t j=begin;j<end;j++){
        term cell=HEAP.data[j];
        unsigned k=tag_of(cell);
        if(cell==NIL || k==ATOM){
            HEAP.data[HEAP.top++]=cell;
        }else{
            HEAP.data[HEAP.top++]=tag_u(val_of(cell)+off, k);
        }
    }
    term hb0=c->hb;
    term hb=tag_u(val_of(hb0)+off, PAIR);
    return hb;
}

// ---------- Engine ----------
typedef struct{ term G; int next_clause; size_t hmark, tmark; } Frame;
typedef struct{ Frame*data; int cap, top; } FStack;
inline static void fs_init(FStack*s){ s->cap=16; s->top=0; s->data=(Frame*)malloc(s->cap*sizeof(Frame)); if(!s->data){fprintf(stderr,"OOM frames\n"); exit(1);} }
inline static void fs_push(FStack*s, Frame f){ if(s->top==s->cap){ s->cap<<=1; s->data=(Frame*)realloc(s->data,s->cap*sizeof(Frame)); if(!s->data){fprintf(stderr,"OOM frames grow\n"); exit(1);} } s->data[s->top++]=f; }
inline static int  fs_empty(FStack*s){ return s->top==0; }
inline static Frame*fs_top(FStack*s){ return &s->data[s->top-1]; }
inline static void fs_pop(FStack*s){ if(s->top) s->top--; }

static void run_engine(void){
    Trail trail; trail_init(&trail,1024);
    FStack st; fs_init(&st);

    // Initial goal: (Ans => (Cont => goal))
    term Ans = make_var();
    term Cont = make_var();
    term goal = make_atom("goal");
    term G0 = make_pair(Ans, make_pair(Cont, goal));

    // Push root frame
    fs_push(&st,(Frame){.G=G0,.next_clause=0,.hmark=HEAP.top,.tmark=trail.top});

    int solutions=0;

    while(!fs_empty(&st)){
        Frame *F=fs_top(&st);
        // reset to marks
        unwind_to(&trail, F->tmark);
        trim_heap(F->hmark);

        if(F->next_clause >= PROG.len){
            fs_pop(&st);
            continue;
        }

        int i=F->next_clause++;
        size_t htop=HEAP.top;
        term hb=activate_clause(&PROG.cs[i]);
        term H=left(hb);

        if(!unify_htop(F->G, H, &trail, htop)){
            continue; // try next clause
        }

        term B=deref(right(hb));
        if(tag_of(B)==VAR){
            print_term(Ans);
            printf("\n");
            solutions++;
            continue; // explore other choices at same depth
        }else{
            Frame child=(Frame){.G=B,.next_clause=0,.hmark=HEAP.top,.tmark=trail.top};
            fs_push(&st, child);
        }
    }

    if(solutions==0){
        printf("No solutions.\n");
    }
}

// ---------- Loader with CLS/LINE printing ----------
static void rstrip_newline(char*s){
    size_t n=strlen(s);
    while(n && (s[n-1]=='\n' || s[n-1]=='\r')) s[--n]='\0';
}
static void load_program(const char*path){
    FILE*f=fopen(path,"r");
    if(!f){ fprintf(stderr,"Cannot open %s\n", path); exit(1); }
    char *line=NULL; size_t n=0; ssize_t r;
    while((r=getline(&line,&n,f))!=-1){
        int only_ws=1;
        for(ssize_t i=0;i<r;i++) if(!isspace((unsigned char)line[i])){ only_ws=0; break; }
        if(only_ws) continue;
        size_t begin,end;
        term hb=parse_postfix_line(line,&begin,&end);

        // Print CLS and LINE
        printf("CLS: "); print_clause_local(hb, begin, end); printf("\n");
        rstrip_newline(line);
        printf("LINE: %s\n\n", line);

        prog_add_clause(&PROG, hb, begin, end, line);
    }
    free(line); fclose(f);
}

// ---------- main ----------
int main(int argc, char**argv){
    heap_init(&HEAP, 1<<20);
    syms_init(&SYMS, 1024);
    LISTCONS_ID = sym_intern("[|]"); // for list detection
    prog_init(&PROG);
    const char*path=(argc>=2)? argv[1] : "../../out/bnf_asm.txt";
    load_program(path);
    run_engine();
    // cleanup
    for(int i=0;i<PROG.len;i++) free(PROG.cs[i].line);
    free(PROG.cs);
    for(size_t i=0;i<SYMS.cap;i++) if(SYMS.tab[i].s) free(SYMS.tab[i].s);
    free(SYMS.tab);
    free(HEAP.data);
    return 0;
}
