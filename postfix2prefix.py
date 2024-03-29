class arity(int):
    def __repr__(self):
        return f'$({int(self)})'


def to_postfix(term):
    args = [term]
    stack = []
    while args:
        t = args.pop()
        if not isinstance(t, tuple):
            stack.append(t)
        else:
            stack.append(arity(len(t)))
            for x in reversed(t):
                args.append(x)
    return list(reversed(stack))


def from_postfix(ws):
    stack = []
    for w in ws:
        if not isinstance(w, arity):
            stack.append(w)
        else:
            xs = []
            for _ in range(w):
                x = stack.pop()
                xs.append(x)
            stack.append(tuple(xs))
    return stack.pop()


def to_heap(term):
    args = [term]
    stack = []
    while args:
        t = args.pop()
        if not isinstance(t, tuple):
            stack.append(t)
        else:
            stack.append(arity(len(t)))
            for x in reversed(t):
                args.append(x)
    return list(stack)



t = (1, ((2,), 3, 3.14), (4, 5), (6, (7, 8)), 9, 'ten')
print(t)
xs = to_postfix(t)
print(xs)
tt = from_postfix(xs)
print()
print(tt)
ys = to_heap(t)
print(ys)
