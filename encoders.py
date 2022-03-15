from collections import defaultdict
import csv
import pprint


# turns .tsv file into list of lists
def tsv2mat(fname):
    with open(fname) as f:
        yield from csv.reader(f, delimiter='\t')


class Indexer:
    def __init__(self, fname='data/triplets.tsv'):
        a=defaultdict(list)
        d = defaultdict(set)
        for (at, path_code, val) in tsv2mat(fname):
            at=int(at)
            path = path_code.split('v')
            path = tuple(int(x) for x in path)
            p=(val,path)
            a[at].append(p)
            d[p].add(at)
            if at == 42: print('!!!', at, (val, path))
        self.a = a
        self.d = d

    def find(self, pairs):
        if not pairs: return range(self.count)
        sets = [self.d[pair] for pair in pairs]

        ats=sets[0].intersection(*sets[1:])
        for at in ats: yield at,self.a[at]


fname = 'data/triplets.tsv'


def t1():
    Ind = Indexer(fname=fname)
    print('START')
    for k, v in I.d.items():
        if len(v) > 4:
            print(k, ':', v)
    print('END')


def t2():
    Ind = Indexer(fname=fname)
    xs = [
      #('straight', (1, 1, 1, 1, 1, 1, 8, 1, 1)),
      #('edge', (1, 1, 1, 1, 1, 2, 0)),
      ('subgraph', (1, 1, 1, 1, 1, 3))
    ]
    print('SEARCHING:')
    print('>>>',Ind.d[('edge', (1, 1, 1, 1, 1, 2, 0))])
    for at,kv in Ind.find(xs):
        print('FOUND at:', at)
        pprint.pprint(kv)


if __name__ == "__main__":
    t2()
