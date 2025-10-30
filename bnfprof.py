from bnf import go
import cProfile
def prof():
   

    p = cProfile.Profile()


    print("PROFILING STARTED")
    p.runcall(go)
    p.print_stats(sort=1)

prof()