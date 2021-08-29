DEB = True


# load from an "assembler" code file
def load(fname='out/bineq_asm.txt'):
    def to_const(x):
        try:
            return int(x), INT
        except ValueError:
            try:
                return float(x), FLOAT
            except ValueError:
                return atom(x)

    with open(fname, 'r') as f:
        txt = f.read()
    ls = txt.split('\n')
    code = []
    vs = dict()
    cs = []
    for line in ls:
        xs = line[:-1].split(' ')
        if len(xs) <= 1: continue  # skip extra new lines
        for j, x in enumerate(xs):
            if j == 0: continue
            if x[0].isupper():
                if x in vs:
                    v = vs[x]
                else:
                    v = var(len(vs))  # , x
                    vs[x] = v
                xs[j] = v
            elif x[0] == "_":
                v = var(len(vs)),  # x
                vs[x] = v
                xs[j] = v
            elif x == '[|]':
                xs[j] = to_const('.')
            else:
                xs[j] = to_const(x)

        cs.append(xs)
        if xs[0] == 'p':
            code.append(cs)
            vs = dict()  # new vs scoped over next clause
            cs = []
    return code


# runtime-system

heap = []
syms = dict()
sids = []


def sym(s):
    if DEB: return s
    if s in syms: return syms[s]
    i = len(sids)
    syms[s] = i
    sids.append(s)
    return i


if DEB:
    VAR, ARITY, CONST, INT, FLOAT = 'VAR', 'ARITY', 'CONST', 'INT', 'FLOAT'
    READ, WRITE = 'READ', 'WRITE'
else:
    VAR, ARITY, CONST, INT, FLOAT = 1, 2, 3, 4, 5
    READ, WRITE = 1, 2


def arity(n):
    assert isinstance(n, int)
    return (n, ARITY)


def atom(s):
    assert isinstance(s, str)
    return sym(s), CONST


def var(x):
    assert x is None or isinstance(x, int)
    return (x, VAR)


def put_fun(n, ft):
    n = as_val(n)
    ft = as_val(ft)
    h = len(heap)
    heap.append((n[0], ARITY))
    heap.append(ft)
    heap.extend([var(None)] * n[0])
    return arity(h)


def put_arg(i_, h_, x):
    i, ti = i_
    h, th = h_
    assert VAR == ti
    assert VAR == th
    hi = h + i
    heap[hi] = x
    return var(hi)


def get_fun(n, ft):
    n = as_val(n)
    ft = as_val(ft)
    h = len(heap)
    heap.append((n[0], ARITY))
    heap.append(ft)
    heap.extend([var(None)] * n[0])
    return arity(h)

def unify_arg(i_, h_, x, trail, htop):
    i, ti = as_val(i_)
    h, th = as_val(h_)
    assert VAR == ti
    assert VAR == th
    y = heap[h + i]
    return unify(x, y, trail, htop)


def as_val(v):
    assert isinstance(v, tuple)
    assert len(v) == 2
    assert isinstance(v[0], int) or isinstance(v[0], str)
    return v


def as_var(v):
    assert isinstance(v, tuple)
    assert len(v) == 2
    assert isinstance(v[0], int)
    return v


def get_val(v):
    v = as_val(v)
    r = heap[v[0]]
    return as_val(r)


def set_val(v, t):
    v = as_val(x)
    t = as_val(t)
    heap[v[0]] = t


def deref(o):
    while True:
        x, t = o
        if t == VAR:
            v, tv = get_val(x)
            if v is None:
                assert VAR == tv
                return o
            if VAR == tv and v > x:
                print('DEREF:', v, '>', x)
                assert v < x
            o = v, tv

        else:
            return o


# unify two terms
def unify(x, y, trail, htop):
    ustack = []
    ustack.append(y)
    ustack.append(x)
    while ustack:
        x1, t1 = deref(ustack.pop())
        x2, t2 = deref(ustack.pop())
        if (x1, t1) == (x2, t2) and t1 != ARITY:
            pass
        elif VAR == t1 and VAR == t2:
            if x1 > x2:
                set_val(x1, (x2, t2))
                if x1 < htop: trail.append(x1)
            else:
                set_val(x2, (x1, t1))
                if x2 < htop: trail.append(x2)
        elif VAR == t1:
            set_val(x1, (x2, t2))
            if x1 < htop: trail.append(x1)
        elif VAR == t2:
            set_val(x2, (x1, t1))
            if x2 < htop: trail.append(x2)
        elif t1 != t2:
            return False
        elif t1 in (CONST, INT, FLOAT):
            if x1 != x2:
                return False
        else:
            assert t1 == ARITY
            assert t2 == ARITY
            if x1 != x2:
                return False
            for i in range(x1 + 1, 0, -1):
                a = get_val(x1 + i)
                b = get_val(x2 + i)
                ustack.append(b)
                ustack.append(a)
    return True


def unwind(trail, ttop):
    for _ in range(len(trail) - ttop):
        v = trail.pop()
        set_val(v, (v, VAR))


def trim_heap(htop):
    # return
    l = len(heap)
    for _ in range(htop, l):
        heap.pop()


def get_goal():
    h = put_fun((2, 'ARITY'), ('goal', CONST))
    return h


def activate(G, clause, trail, ttop, htop):
    hb, ctag = clause.c

    ok = unify(left(hb), G, trail, htop)
    unwind(trail, ttop)
    if not ok: return False

    begin = clause.begin
    end = clause.end
    h = htop - begin

    for j in range(begin, end):
        x, t = heap[j]
        if CONST == t:
            heap.append((x, t))
        else:
            heap.append((x + h, t))
    r = h + hb, ctag
    return r


FAIL, DO, DONE, UNDO = 0, 1, 2, 3


def step(G, code, trail, goal, i):
    l = len(code)
    htop = len(heap)
    ttop = len(trail)
    G = deref(G)
    assert G[0] < htop
    while i < l:
        unwind(trail, ttop)
        trim_heap(htop)
        clause = activate(G, code[i], trail, ttop, htop)
        i += 1
        if clause:
            hb, thb = clause
            assert PAIR == thb
            H = left(hb)
            assert H[0] >= htop
            assert G[0] < htop
            unify(G, H, trail, htop)
            b, tb = deref(right(hb))
            if VAR == tb:
                # yield p(left(goal[0]))
                # print("GOAL",iron(goal))
                print(p(left(goal[0])))
                return (DONE, G, ttop, htop, i)
            else:
                NewG = b, tb
                assert b < len(heap)
                # yield from loop(NewG,k+1)
                return (DO, (NewG, G), ttop, htop, i)
    return (FAIL, None, ttop, htop, i)


# code interpreter
def interp():
    goal = get_goal()
    code = load()
    # pc(code)
    l = len(code)
    trail = []
    todo = [(DO, (goal, None), 0, len(heap), l)]

    while (todo):
        op, G, ttop, htop, i = todo.pop()
        if DO == op:
            (NewG, OldG) = G
            if i < l: ensure_undo(OldG, todo, ttop, htop, i, l);
            todo.append(step(NewG, code, trail, goal, 0))

        elif DONE == op:
            # yield p(answer)
            if i < l: ensure_undo(G, todo, ttop, htop, i, l)

        elif UNDO == op:
            unwind(trail, ttop)
            trim_heap(htop)
            if i < l: todo.append(step(G, code, trail, goal, i))

        else:  # FAIL == op:
            pass


def ensure_undo(G, todo, ttop, htop, i, l):
    instr = (UNDO, G, ttop, htop, i)
    if todo:
        (op, G1, ttop1, htop1, i1) = todo[-1]
        if (op, i1, G) == (UNDO, i, G1) and ttop >= ttop1:
            return
    todo.append(instr)


def go():
    interp()


####### tests #####

def ltest():
    print('testing')
    code = load()
    # print(code)
    for xs in code:
        for x in xs:
            pass
            print(x)
    print('syms')
    print(syms)


if __name__ == "__main__":
    ltest()
    go()
