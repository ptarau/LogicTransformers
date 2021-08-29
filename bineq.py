DEB = True


# load from an "assembler" code file
def load(fname='out/bineq_asm.txt'):
    def to_const(x):
        try:
            return tag(int(x), INT)
        except ValueError:
            try:
                return tag(float(x), FLOAT)
            except ValueError:
                return tag(x,CONST)

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
                    v = tag(len(vs),VAR)  # , x
                    vs[x] = v
                xs[j] = v
            elif x[0] == "_":
                v = tag(len(vs),VAR),  # x
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


def tag_of(x):
    return x[1]


def val(x):
    return x[0]


def tag(x, t):
    return (x, t)


def vget(h):
    assert isinstance(h, int)
    x = heap[h]
    assert isinstance(x, tuple)
    return x


def vset(h, x):
    assert isinstance(h, int)
    assert isinstance(x, tuple)
    heap[h] = x


def put_size(arity):
    h = len(heap)
    n = val(arity)
    heap.append(arity)
    heap.extend([tag(None, VAR)] * n)
    return tag(h, VAR)


def get_size(arity, v):
    n = val(arity)
    m = val(v)
    t = tag_of(v)
    return ARITY == t and n == m


def put_arg(i_, h_, x):
    i = val(i_)
    ti = tag_of(i_)
    h = val(h_)
    th = tag_of(h_)
    assert INT == ti
    assert VAR == th
    hi = h + i
    vset(hi, x)


def unify_arg(i_, h_, x, trail, htop):
    i = val(i_)
    ti = tag_of(i_)
    h = val(h_)
    th = tag_of(h_)
    assert INT == ti
    assert VAR == th
    hi = h + i
    y = vget(hi)
    return unify(x, y, trail, htop)


def deref(o):
    while True:
        x, tx = o
        if tx == VAR:
            v, tv = vget(x)
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
                vset(x1, (x2, t2))
                if x1 < htop: trail.append(x1)
            else:
                vset(x2, (x1, t1))
                if x2 < htop: trail.append(x2)
        elif VAR == t1:
            vset(x1, (x2, t2))
            if x1 < htop: trail.append(x1)
        elif VAR == t2:
            vset(x2, (x1, t1))
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
                a = vget(x1 + i)
                b = vget(x2 + i)
                ustack.append(b)
                ustack.append(a)
    return True


def unwind(trail, ttop):
    for _ in range(len(trail) - ttop):
        v = trail.pop()
        vset(v, (v, VAR))


def trim_heap(htop):
    # return
    hl = len(heap)
    for _ in range(htop, hl):
        heap.pop()


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
        clause = code[i]
        i += 1
        print(clause)
    return (FAIL, None, ttop, htop, i)


def get_goal():
    h = put_size(tag(2,ARITY))
    put_arg(tag(1,INT), h, tag('goal',CONST))
    put_arg(tag(2,INT), h, tag(None,VAR))
    return h


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
            print("$$$$ G=", G)
            if i < l: ensure_undo(OldG, todo, ttop, htop, i, l)
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


# tests

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
    print('clauses:', len(code))


if __name__ == "__main__":
    ltest()
    go()
