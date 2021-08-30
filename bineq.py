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
                return tag(x, CONST)

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
                    v = tag(len(vs), VAR)  # , x
                    vs[x] = v
                xs[j] = v
            elif x[0] == "_":
                v = tag(len(vs), VAR),  # x
                vs[x] = v
                xs[j] = v
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


def put_size(arity, v, regs):
    h = len(heap)
    n = val(arity)
    heap.append(arity)
    for i in range(1, n + 1):
        heap.append(tag(h + i, VAR))
    regs[val(v)] = h


def get_size(arity, v, regs):
    n = val(arity)
    other = heap[regs[val(v)]]
    m = val(other)
    return n == m


def put_arg(i_, v, x, regs):
    i = val(i_)
    h = regs[val(v)]
    hi = h + i
    vset(hi, x)


def unify_arg(i_, v_, x, trail, htop, regs):
    i = val(i_)
    v = val(v_)
    assert v is not None
    h = regs[v]
    hi = h + i
    y = vget(hi)
    return unify(x, y, trail, htop)

def get_var(v_,regs) :
    v = val(v_)
    assert v is not None
    h = regs[v]
    y = vget(h)
    return y



def deref(o):
    while True:
        x, t = o
        if t == VAR:
            v, tv = vget(x)
            if v == x:
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
    cl = len(code)
    htop = len(heap)
    ttop = len(trail)
    G = deref(G)
    assert val(G) < htop
    while i < cl:
        unwind(trail, ttop)
        trim_heap(htop)
        clause = code[i]
        i += 1
        regs = [None] * len(clause)
        for j, instr in enumerate(clause):
            op = instr[0]
            x = instr[1]
            if 'd' == op:
                regs[0] = val(x)

            elif 'r' == op:
                v = instr[2]
                if not get_size(x, v, regs):
                    if j == 1:
                        print('FAILING cls =', i, deref(v))
                        break
                    print('SUCCEDS cls = ',i )
                    put_size(x, v, regs)

            elif 'u' == op:
                print(op, x, instr[2], instr[3])
                if not unify_arg(x, instr[2], instr[3], trail, htop, regs):
                    break

            elif 'w' == op:
                print(op, x)
                v = instr[2]
                put_size(x, v, regs)

            elif 'b' == op:
                # put_arg(i_, h_, x):
                print(op, x, instr[2], instr[3])
                put_arg(x, instr[2], instr[3], regs)

            else:
                assert 'p' == op
                v=instr[1]

                y=get_var(v,regs)
                print(op, v, 'y:',y)

                NewG = deref(y)
                if VAR == tag_of(NewG):
                    return (DONE, G, ttop, htop, i)
                else:
                    print('HERE:',NewG)
                    return (DO, (NewG, G), ttop, htop, i)
    return (FAIL, None, ttop, htop, i)


def get_goal():
    h = len(heap)
    heap.append(tag(3, ARITY))
    heap.append(tag('goal', CONST))
    heap.append(tag(2, VAR))
    heap.append(tag(3, VAR))
    return tag(h, VAR)


# code interpreter
def interp():
    goal = get_goal()
    code = load()
    # pc(code)
    cl = len(code)
    trail = []
    todo = [(DO, (goal, None), 0, len(heap), cl)]

    fuel = 20
    while (todo):
        fuel-=1
        if fuel == 0:
            print('EXITING')
            return

        print("TODO:", todo)
        op, G, ttop, htop, i = todo.pop()
        if DO == op:
            (NewG, OldG) = G

            if i < cl: ensure_undo(OldG, todo, ttop, htop, i, cl)
            todo.append(step(NewG, code, trail, goal, 0))

        elif DONE == op:
            # yield p(answer)
            print("DONE ------------->", G)
            if i < cl: ensure_undo(G, todo, ttop, htop, i, cl)

        elif UNDO == op:
            unwind(trail, ttop)
            trim_heap(htop)
            if i < cl: todo.append(step(G, code, trail, goal, i))

        else:  # FAIL == op:
            pass


def ensure_undo(G, todo, ttop, htop, i, cl):
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
    # ltest()
    go()
