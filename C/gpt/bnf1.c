
// prolog_vm.c
// Single-file, heap-based Prolog-like interpreter with tagged 64-bit terms.
// Emphasis on speed: inline helpers, iterative unify with trail, atom interning.
//
// Build:   cc -O3 -std=c11 -Wall -Wextra -o prolog_vm prolog_vm.c
// Run:     ./prolog_vm
//
// This file includes a tiny demo program (ancestor/2) at the bottom of main().
// You can adapt "add_clause()" calls to build your own program terms.
//
// Representation
// --------------
// term: 64-bit tagged immediate
//   [ ... 61 bits payload ... | 3-bit tag ]
// Tags:
//   0 HNIL  (unused internal, avoid using directly)
//   1 ATOM  (payload = atom id)
//   2 PAIR  (payload = heap index of (left,right) cells)
//   3 VAR   (payload = heap index of variable cell; unbound when REF self)
//   4 REF   (used only inside heap cells: tag(idx,REF) means "unbound ref to self")
// NIL is the 0 value (all-zero) which we treat as the empty list [] for convenience.
//
// Structures and lists
// --------------------
// A k-ary structure f(a1,...,ak) is encoded as: pair( atom("f"), list(a1,...,ak) )
// A list [x1,x2,...,xn] is standard: pair(x1, pair(x2, ... pair(xn, NIL)...))
//
// Unification
// -----------
// Iterative with an explicit stack. Variables are heap REF-cells initially
// self-referential. Bindings overwrite the heap cell and are trailed to unwind
// on backtracking.
//
// Resolution (very small SLD engine)
// ----------------------------------
// Clauses are stored as immutable term trees (with their own VAR cells). Before
// use we "freshen" a clause by deep-cloning with a var-cell map, so each attempt
// gets new VAR heap cells. Choice points save heap/trail tops and a copy of goals.
//
// NOTE: The engine is minimal but fast; it's sufficient to run relational programs
// built with pair/atom terms. No occurs-check for speed (can be added).
//
// -----------------------------------------------------------------------------

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <assert.h>

// ---------- Tagged terms ----------
typedef uint64_t term;

#define SHIFT 3
#define MASK  ((term)7u)

#define HNIL 0u
#define ATOM 1u
#define PAIR 2u
#define VAR  3u
#define REF  4u

#define NIL ((term)0u)

inline static term tag_u(term x, unsigned t) { return (x << SHIFT) | (term)t; }
inline static unsigned tag_of(term x)  { return (unsigned)(x & MASK); }
inline static term val_of(term x)      { return x >> SHIFT; }

// ---------- Heap ----------
typedef struct {
    term *data;
    size_t cap, top;
} Heap;

inline static void heap_init(Heap *h, size_t cap) {
    h->data = (term*)malloc(cap * sizeof(term));
    if (!h->data) { fprintf(stderr, "OOM heap\n"); exit(1); }
    h->cap = cap;
    h->top = 0;
}

inline static void heap_reserve(Heap *h, size_t need) {
    if (h->top + need <= h->cap) return;
    size_t ncap = h->cap ? h->cap : 1024;
    while (ncap < h->top + need) ncap <<= 1;
    term *nd = (term*)realloc(h->data, ncap * sizeof(term));
    if (!nd) { fprintf(stderr, "OOM heap grow\n"); exit(1); }
    h->data = nd;
    h->cap = ncap;
}

inline static size_t heap_alloc_cell(Heap *h) {
    heap_reserve(h, 1);
    return h->top++;
}

inline static size_t heap_alloc2(Heap *h) {
    heap_reserve(h, 2);
    size_t base = h->top;
    h->top += 2;
    return base;
}

// Global heap
static Heap HEAP;

// Accessors for PAIR cells
inline static term make_pair(term a, term b) {
    size_t base = heap_alloc2(&HEAP);
    HEAP.data[base]   = a;
    HEAP.data[base+1] = b;
    return tag_u((term)base, PAIR);
}

inline static term left(term p)  { return HEAP.data[(size_t)val_of(p)]; }
inline static term right(term p) { return HEAP.data[(size_t)val_of(p)+1]; }

// Variables: allocate a REF self cell, return VAR(heap_index)
inline static term make_var(void) {
    size_t i = heap_alloc_cell(&HEAP);
    HEAP.data[i] = tag_u((term)i, REF); // self-ref means unbound
    return tag_u((term)i, VAR);
}

inline static int is_unbound_ref(term cell, size_t idx) {
    return tag_of(cell)==REF && val_of(cell)==(term)idx;
}

// ---------- Trail for backtracking ----------
typedef struct {
    size_t *data;
    size_t cap, top;
} Trail;

inline static void trail_init(Trail *t, size_t cap) {
    t->data = (size_t*)malloc(cap * sizeof(size_t));
    if (!t->data) { fprintf(stderr, "OOM trail\n"); exit(1); }
    t->cap = cap;
    t->top = 0;
}

inline static void trail_push(Trail *t, size_t idx) {
    if (t->top == t->cap) {
        size_t ncap = t->cap ? t->cap<<1 : 1024;
        size_t *nd = (size_t*)realloc(t->data, ncap*sizeof(size_t));
        if (!nd) { fprintf(stderr, "OOM trail grow\n"); exit(1); }
        t->data = nd;
        t->cap = ncap;
    }
    t->data[t->top++] = idx;
}

inline static void unwind_trail_to(Trail *t, size_t tmark) {
    while (t->top > tmark) {
        size_t idx = t->data[--t->top];
        HEAP.data[idx] = tag_u((term)idx, REF); // reset to unbound
    }
}

// ---------- Dereference & bind ----------
inline static term deref(term x) {
    while (tag_of(x) == VAR) {
        size_t i = (size_t)val_of(x);
        term w = HEAP.data[i];
        if (is_unbound_ref(w, i)) return x;
        x = w; // follow binding
    }
    return x;
}

inline static void bind_var(size_t idx, term t, Trail *trail) {
    // Trail then bind
    trail_push(trail, idx);
    HEAP.data[idx] = t;
}

// ---------- Unify ----------
typedef struct { term a, b; } Pair;
typedef struct {
    Pair *data;
    size_t cap, top;
} PStack;

inline static void pstack_init(PStack *s, size_t cap) {
    s->data = (Pair*)malloc(cap*sizeof(Pair));
    if (!s->data) { fprintf(stderr, "OOM pstack\n"); exit(1); }
    s->cap = cap;
    s->top = 0;
}
inline static void pstack_push(PStack *s, term a, term b) {
    if (s->top == s->cap) {
        size_t ncap = s->cap ? s->cap<<1 : 1024;
        Pair *nd = (Pair*)realloc(s->data, ncap*sizeof(Pair));
        if (!nd) { fprintf(stderr, "OOM pstack grow\n"); exit(1); }
        s->data = nd; s->cap = ncap;
    }
    s->data[s->top++] = (Pair){a,b};
}
inline static int pstack_pop(PStack *s, Pair *out) {
    if (!s->top) return 0;
    *out = s->data[--s->top];
    return 1;
}

// Returns 1 on success, 0 on failure. No occurs-check.
inline static int unify(term x, term y, Trail *trail) {
    PStack st; pstack_init(&st, 128);
    pstack_push(&st, x, y);
    Pair p;
    while (pstack_pop(&st, &p)) {
        term a = deref(p.a);
        term b = deref(p.b);
        if (a == b) continue;
        unsigned ta = tag_of(a), tb = tag_of(b);
        if (ta == VAR) {
            size_t ia = (size_t)val_of(a);
            bind_var(ia, b, trail);
        } else if (tb == VAR) {
            size_t ib = (size_t)val_of(b);
            bind_var(ib, a, trail);
        } else if (ta == ATOM && tb == ATOM) {
            if (val_of(a) != val_of(b)) { free(st.data); return 0; }
        } else if (ta == PAIR && tb == PAIR) {
            pstack_push(&st, left(a),  left(b));
            pstack_push(&st, right(a), right(b));
        } else if (a == NIL && b == NIL) {
            // ok (explicit equality handled above anyway)
        } else {
            free(st.data); return 0;
        }
    }
    free(st.data);
    return 1;
}

// ---------- Atom interning ----------
typedef struct {
    char *s;
    uint64_t id;
} SymEnt;

typedef struct {
    SymEnt *tab;
    size_t cap, sz;
} SymTable;

static SymTable SYMS;

static uint64_t fnv1a(const char *s) {
    uint64_t h = 1469598103934665603ull;
    for (; *s; ++s) { h ^= (unsigned char)*s; h *= 1099511628211ull; }
    return h;
}

inline static void syms_init(SymTable *st, size_t cap) {
    st->cap = cap;
    st->sz = 0;
    st->tab = (SymEnt*)calloc(cap, sizeof(SymEnt));
    if (!st->tab) { fprintf(stderr, "OOM syms\n"); exit(1); }
}

inline static void syms_grow(SymTable *st) {
    size_t ncap = st->cap ? st->cap<<1 : 1024;
    SymEnt *nt = (SymEnt*)calloc(ncap, sizeof(SymEnt));
    if (!nt) { fprintf(stderr, "OOM syms grow\n"); exit(1); }
    for (size_t i=0;i<st->cap;i++) if (st->tab[i].s) {
        uint64_t h = fnv1a(st->tab[i].s);
        size_t j = (size_t)(h & (ncap-1));
        while (nt[j].s) j = (j+1) & (ncap-1);
        nt[j] = st->tab[i];
    }
    free(st->tab); st->tab = nt; st->cap = ncap;
}

inline static uint64_t sym_intern(const char *s) {
    if (!SYMS.cap) syms_init(&SYMS, 1024);
    if (SYMS.sz*2 >= SYMS.cap) syms_grow(&SYMS);
    uint64_t h = fnv1a(s);
    size_t i = (size_t)(h & (SYMS.cap-1));
    while (1) {
        SymEnt *e = &SYMS.tab[i];
        if (!e->s) {
            e->s = strdup(s);
            if (!e->s) { fprintf(stderr, "OOM strdup\n"); exit(1); }
            e->id = ++SYMS.sz; // start ids at 1
            return e->id;
        } else if (strcmp(e->s, s)==0) {
            return e->id;
        }
        i = (i+1) & (SYMS.cap-1);
    }
}

inline static const char* sym_name(uint64_t id) {
    // Linear scan (fast enough for demo). Could store reverse map for O(1).
    for (size_t i=0;i<SYMS.cap;i++) if (SYMS.tab[i].s && SYMS.tab[i].id==id) return SYMS.tab[i].s;
    return "?";
}

inline static term make_atom(const char *s) { return tag_u(sym_intern(s), ATOM); }

// ---------- Convenience list/structure builders ----------
inline static term cons(term a, term d) { return make_pair(a,d); }
inline static term list2(term a, term b) { return cons(a, cons(b, NIL)); }

inline static term build_struct_1(const char *f, term a1) {
    return make_pair(make_atom(f), cons(a1, NIL));
}
inline static term build_struct_2(const char *f, term a1, term a2) {
    return make_pair(make_atom(f), cons(a1, cons(a2, NIL)));
}
inline static term build_struct_3(const char *f, term a1, term a2, term a3) {
    return make_pair(make_atom(f), cons(a1, cons(a2, cons(a3, NIL))));
}

// ---------- Pretty printing ----------

static void print_term_rec(term t, int depth);

static void print_list(term xs, int depth) {
    putchar('[');
    int first = 1;
    while (1) {
        xs = deref(xs);
        if (xs == NIL) break;
        if (tag_of(xs) != PAIR) {
            printf("|");
            print_term_rec(xs, depth+1);
            break;
        }
        term h = left(xs);
        if (!first) printf(",");
        print_term_rec(h, depth+1);
        xs = right(xs);
        first = 0;
    }
    putchar(']');
}

static void print_struct(term t, int depth) {
    term fun = left(t);
    term args = right(t);
    if (tag_of(fun) != ATOM) {
        // Fallback generic pair
        putchar('(');
        print_term_rec(fun, depth+1);
        printf(",");
        print_term_rec(args, depth+1);
        putchar(')');
        return;
    }
    printf("%s(", sym_name(val_of(fun)));
    int first = 1;
    while (args != NIL) {
        term a = left(args);
        if (!first) printf(",");
        print_term_rec(a, depth+1);
        args = right(args);
        first = 0;
    }
    putchar(')');
}

static void print_term_rec(term t, int depth) {
    t = deref(t);
    unsigned k = tag_of(t);
    switch (k) {
        case ATOM: printf("%s", sym_name(val_of(t))); break;
        case VAR: {
            size_t i = (size_t)val_of(t);
            printf("_%zu", i);
        } break;
        case PAIR: {
            // Heuristic: if left is ATOM, treat as structure; if PAIR or NIL, maybe list
            term a = left(t);
            if (a == NIL || tag_of(a)==PAIR || tag_of(t)==PAIR && a!=NIL) {
                // Try list print if tail chains like PAIR..NIL
                term aref = deref(a);
                term tail = right(t);
                // If looks like a list: [a|tail]
                int listlike = 0;
                if (tail == NIL) listlike = 1;
                else if (tag_of(tail)==PAIR) listlike = 1;
                if (listlike && tag_of(a) != ATOM) { print_list(t, depth+1); break; }
            }
            if (tag_of(a)==ATOM) print_struct(t, depth+1);
            else {
                putchar('(');
                print_term_rec(left(t), depth+1);
                printf(",");
                print_term_rec(right(t), depth+1);
                putchar(')');
            }
        } break;
        case REF: printf("<ref>"); break;
        default: printf("[]"); break;
    }
}

static void print_term(term t) { print_term_rec(t, 0); }

// ---------- Clause representation ----------
typedef struct {
    term head;
    int body_len;
    term *body; // array of terms
} Clause;

// Program store
typedef struct {
    Clause *cs;
    int cap, len;
} Program;

static Program PROG;

inline static void prog_init(Program *p) {
    p->cap = 16; p->len = 0;
    p->cs = (Clause*)malloc(p->cap*sizeof(Clause));
    if (!p->cs) { fprintf(stderr, "OOM program\n"); exit(1); }
}
inline static void prog_add_clause(Program *p, term head, int body_len, term *body) {
    if (p->len == p->cap) {
        p->cap <<= 1;
        Clause *nc = (Clause*)realloc(p->cs, p->cap*sizeof(Clause));
        if (!nc) { fprintf(stderr, "OOM program grow\n"); exit(1); }
        p->cs = nc;
    }
    Clause c; c.head = head; c.body_len = body_len;
    if (body_len) {
        c.body = (term*)malloc(body_len*sizeof(term));
        if (!c.body) { fprintf(stderr, "OOM clause body\n"); exit(1); }
        for (int i=0;i<body_len;i++) c.body[i] = body[i];
    } else c.body = NULL;
    p->cs[p->len++] = c;
}

// ---------- Clone with var map ----------
// Map from old var heap index -> new var heap index
typedef struct {
    size_t *keys;
    size_t *vals;
    size_t cap, sz;
} VarMap;

inline static void vmap_init(VarMap *m, size_t cap) {
    m->keys = (size_t*)malloc(cap*sizeof(size_t));
    m->vals = (size_t*)malloc(cap*sizeof(size_t));
    if (!m->keys || !m->vals) { fprintf(stderr, "OOM vmap\n"); exit(1); }
    m->cap = cap; m->sz = 0;
}
inline static void vmap_free(VarMap *m) { free(m->keys); free(m->vals); }
inline static int vmap_get(VarMap *m, size_t k, size_t *out) {
    for (size_t i=0;i<m->sz;i++) if (m->keys[i]==k) { *out=m->vals[i]; return 1; }
    return 0;
}
inline static void vmap_put(VarMap *m, size_t k, size_t v) {
    if (m->sz == m->cap) {
        m->cap <<= 1;
        m->keys = (size_t*)realloc(m->keys, m->cap*sizeof(size_t));
        m->vals = (size_t*)realloc(m->vals, m->cap*sizeof(size_t));
        if (!m->keys || !m->vals) { fprintf(stderr, "OOM vmap grow\n"); exit(1); }
    }
    m->keys[m->sz] = k; m->vals[m->sz] = v; m->sz++;
}

static term clone_term_rec(term t, VarMap *vm);

inline static term clone_var(term v, VarMap *vm) {
    size_t old = (size_t)val_of(v);
    size_t nv;
    if (vmap_get(vm, old, &nv)) {
        return tag_u((term)nv, VAR);
    } else {
        term fresh = make_var();
        nv = (size_t)val_of(fresh);
        vmap_put(vm, old, nv);
        return fresh;
    }
}

static term clone_term_rec(term t, VarMap *vm) {
    t = deref(t);
    unsigned k = tag_of(t);
    if (k==VAR) return clone_var(t, vm);
    if (k==ATOM || t==NIL) return t;
    if (k==PAIR) {
        term a = clone_term_rec(left(t), vm);
        term d = clone_term_rec(right(t), vm);
        return make_pair(a,d);
    }
    return t;
}

// Clone a clause (head + body terms) fresh
static void clone_clause(const Clause *c, Clause *out) {
    VarMap vm; vmap_init(&vm, 16);
    out->head = clone_term_rec(c->head, &vm);
    out->body_len = c->body_len;
    if (c->body_len) {
        out->body = (term*)malloc(c->body_len*sizeof(term));
        if (!out->body) { fprintf(stderr, "OOM clone body\n"); exit(1); }
        for (int i=0;i<c->body_len;i++) out->body[i] = clone_term_rec(c->body[i], &vm);
    } else out->body = NULL;
    vmap_free(&vm);
}

// ---------- Goals, Choice points, Solver ----------
typedef struct {
    term *g;
    int len;
    int cap;
} Goals;

inline static void goals_init(Goals *gs) {
    gs->cap = 8; gs->len = 0;
    gs->g = (term*)malloc(gs->cap*sizeof(term));
    if (!gs->g) { fprintf(stderr, "OOM goals\n"); exit(1); }
}
inline static void goals_free(Goals *gs) { free(gs->g); }
inline static void goals_set(Goals *gs, int n, term *arr) {
    if (n > gs->cap) {
        int ncap = gs->cap;
        while (ncap < n) ncap <<= 1;
        gs->g = (term*)realloc(gs->g, ncap*sizeof(term));
        if (!gs->g) { fprintf(stderr, "OOM goals set\n"); exit(1); }
        gs->cap = ncap;
    }
    memcpy(gs->g, arr, n*sizeof(term));
    gs->len = n;
}
inline static void goals_replace_with(Goals *gs, int n, term *arr) {
    goals_set(gs, n, arr);
}

static term* goals_snapshot(const Goals *gs) {
    if (!gs->len) return NULL;
    term *copy = (term*)malloc(gs->len*sizeof(term));
    if (!copy) { fprintf(stderr, "OOM goals snapshot\n"); exit(1); }
    memcpy(copy, gs->g, gs->len*sizeof(term));
    return copy;
}

typedef struct {
    size_t heap_top;
    size_t trail_top;
    int next_clause;
    int saved_goal_len;
    term *saved_goals; // ownership to be freed on pop
} ChoicePoint;

typedef struct {
    ChoicePoint *stk;
    int cap, top;
} CPStack;

inline static void cpstack_init(CPStack *s) {
    s->cap = 8; s->top = 0;
    s->stk = (ChoicePoint*)malloc(s->cap*sizeof(ChoicePoint));
    if (!s->stk) { fprintf(stderr, "OOM cpstack\n"); exit(1); }
}
inline static void cpstack_push(CPStack *s, ChoicePoint cp) {
    if (s->top == s->cap) {
        s->cap <<= 1;
        s->stk = (ChoicePoint*)realloc(s->stk, s->cap*sizeof(ChoicePoint));
        if (!s->stk) { fprintf(stderr, "OOM cpstack grow\n"); exit(1); }
    }
    s->stk[s->top++] = cp;
}
inline static int cpstack_pop(CPStack *s, ChoicePoint *out) {
    if (s->top==0) return 0;
    *out = s->stk[--s->top];
    return 1;
}
inline static void cpstack_free(CPStack *s) { free(s->stk); }

// Solve goals; on each success, call callback(userdata) and return 1 if keep searching
typedef int (*on_solution_fn)(void *userdata);

typedef struct {
    Trail trail;
    Goals goals;
    CPStack cps;
} Engine;

inline static void engine_init(Engine *E) {
    trail_init(&E->trail, 1024);
    goals_init(&E->goals);
    cpstack_init(&E->cps);
}

static int solve(Engine *E, on_solution_fn on_sol, void *ud) {
    int start_clause = 0;

    while (1) {
        if (E->goals.len == 0) {
            // Found a solution
            int keep = on_sol(ud);
            if (!keep) return 1;
            // Backtrack for next
            ChoicePoint cp;
            if (!cpstack_pop(&E->cps, &cp)) return 1;
            HEAP.top = cp.heap_top;
            unwind_trail_to(&E->trail, cp.trail_top);
            // restore goals
            goals_set(&E->goals, cp.saved_goal_len, cp.saved_goals);
            free(cp.saved_goals);
            start_clause = cp.next_clause;
            continue;
        }

        // Take first goal
        term goal = E->goals.g[0];
        int matched = 0;

        for (int i = start_clause; i < PROG.len; i++) {
            // Fresh clone clause
            Clause inst;
            clone_clause(&PROG.cs[i], &inst);

            size_t hmark = HEAP.top;
            size_t tmark = E->trail.top;

            if (!unify(goal, inst.head, &E->trail)) {
                // discard instance and continue
                free(inst.body);
                HEAP.top = hmark;
                unwind_trail_to(&E->trail, tmark);
                continue;
            }

            // Save a choice point for other clauses
            ChoicePoint cp;
            cp.heap_top = HEAP.top;
            cp.trail_top = E->trail.top;
            cp.next_clause = i+1;
            cp.saved_goal_len = E->goals.len;
            cp.saved_goals = goals_snapshot(&E->goals);
            cpstack_push(&E->cps, cp);

            // Build new goals = inst.body ++ E->goals[1:]
            int tail_len = E->goals.len - 1;
            int new_len = inst.body_len + tail_len;
            term *tmp = (term*)malloc(new_len * sizeof(term));
            if (!tmp) { fprintf(stderr, "OOM new goals\n"); exit(1); }
            for (int j=0;j<inst.body_len;j++) tmp[j] = inst.body[j];
            for (int j=0;j<tail_len;j++) tmp[inst.body_len+j] = E->goals.g[1+j];

            // Switch to new goals and restart from first clause
            goals_replace_with(&E->goals, new_len, tmp);
            free(tmp);
            free(inst.body);
            matched = 1;
            start_clause = 0;
            break;
        }

        if (!matched) {
            // Backtrack
            ChoicePoint cp;
            if (!cpstack_pop(&E->cps, &cp)) {
                return 0; // failure overall
            }
            HEAP.top = cp.heap_top;
            unwind_trail_to(&E->trail, cp.trail_top);
            goals_set(&E->goals, cp.saved_goal_len, cp.saved_goals);
            free(cp.saved_goals);
            start_clause = cp.next_clause;
        }
    }
}

// ---------- Demo Program: ancestor/2 ----------
// parent(alice,bob). parent(bob,carol).
// ancestor(X,Y) :- parent(X,Y).
// ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).

typedef struct {
    term Qx, Qy; // query variables to print
} QueryVars;

static int on_solution_print(void *ud) {
    QueryVars *V = (QueryVars*)ud;
    printf("Solution: ");
    print_term(V->Qx); printf(" , "); print_term(V->Qy); printf("\n");
    return 1; // keep searching
}

int main(void) {
    heap_init(&HEAP, 1<<20); // ~1M cells initial
    syms_init(&SYMS, 1024);
    prog_init(&PROG);
    Engine E; engine_init(&E);

    // Build facts: parent(alice,bob). parent(bob,carol).
    term alice = make_atom("alice");
    term bob   = make_atom("bob");
    term carol = make_atom("carol");
    term parent_ab = build_struct_2("parent", alice, bob);
    prog_add_clause(&PROG, parent_ab, 0, NULL);

    term parent_bc = build_struct_2("parent", bob, carol);
    prog_add_clause(&PROG, parent_bc, 0, NULL);

    // Rule 1: ancestor(X,Y) :- parent(X,Y).
    term X1 = make_var();
    term Y1 = make_var();
    term anc_XY_1 = build_struct_2("ancestor", X1, Y1);
    term par_XY_1 = build_struct_2("parent", X1, Y1);
    term body1[1] = { par_XY_1 };
    prog_add_clause(&PROG, anc_XY_1, 1, body1);

    // Rule 2: ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).
    term X2 = make_var();
    term Y2 = make_var();
    term Z2 = make_var();
    term anc_XY_2 = build_struct_2("ancestor", X2, Y2);
    term par_XZ_2 = build_struct_2("parent", X2, Z2);
    term anc_ZY_2 = build_struct_2("ancestor", Z2, Y2);
    term body2[2] = { par_XZ_2, anc_ZY_2 };
    prog_add_clause(&PROG, anc_XY_2, 2, body2);

    // Query: ancestor(alice, Y)?
    term Qx = make_var();
    term Qy = make_var();
    term goal = build_struct_2("ancestor", alice, Qy);

    // Set initial goal list
    goals_set(&E.goals, 1, &goal);

    QueryVars Vars = { Qx, Qy }; // not using Qx, but keep for demo

    int ok = solve(&E, on_solution_print, &Vars);
    if (!ok) {
        printf("No solutions.\n");
    }

    // cleanup
    for (int i=0;i<PROG.len;i++) free(PROG.cs[i].body);
    free(PROG.cs);
    free(SYMS.tab);
    free(HEAP.data);
    free(E.trail.data);
    goals_free(&E.goals);
    cpstack_free(&E.cps);
    return 0;
}
