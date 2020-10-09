VAR, REF, PAIR, CONST = 1, 2, 3, 4

mutable struct Var
    val::Any
    age::Int
    name::String
end

# new variables have empty as their value
empty="#"

# creates a new variable
function ivar(age, name)
    Var(empty, age, name)
end

# returns the type of our terms
function type_of(x)
    if x isa Var
        if x.val == empty
            VAR
        else
            REF
        end
    elseif x isa Pair
        PAIR
    else
        CONST
    end
end

# binds a variable to a value, if born before age
function bindVar(v,t,trail,ctr)
    v.val = t
    if v.age<ctr
        push!(trail,v)
    end
end

# dereferences a variable over a chain of value slots
function deref(x)
    #println("DEREF<<<:",x,':',type_of(x))
    while true
        t = type_of(x)
        if t == REF
            x = x.val
        else
            #println("DEREF>>>:",x)
            @assert(x!=empty,"!!!!NOT EMPTY")
            return x, t
        end
    end
end

# unifies two terms, places them on thrail if born before ctr
function unify(x,y,trail,ctr)
    ustack=[]
    push!(ustack,y)
    push!(ustack,x)
    while(!isempty(ustack))
        x1,t1=deref(pop!(ustack))
        x2,t2=deref(pop!(ustack))
        #println("### UNIFY ");pt(x1);pt(x2);println()
        if x1===x2
            continue
        elseif VAR==t1 && VAR==t2
          if x1.age>x2.age
              bindVar(x1,x2,trail,ctr)
          else
              bindVar(x2,x1,trail,ctr)
          end
        elseif VAR==t1
            bindVar(x1,x2,trail,ctr)
        elseif VAR==t2
            bindVar(x2,x1,trail,ctr)
        elseif t1!=t2
            return false
        elseif t1==CONST
            if x1!=x2
                return false
            end
        else
            @assert(PAIR==t1,"PAIR expected")
            a1,b1=x1
            a2,b2=x2
            push!(ustack,b2)
            push!(ustack,b1)
            push!(ustack,a2)
            push!(ustack,a1)
        end
    end
    return true
end

# undoes binding by reseting vars on the trail
function unwind(trail,ttop)
  l=length(trail)
  #println("ENTER UNW ",l,',',ttop)
  for _ in ttop+1:l
      v=pop!(trail)
      #println("UNW",pt(v))
      v.val=empty
  end
end



fuel=1000000000

# basic instruction  processing step
function step_(G,i,code,trail,varctr)
    ttop=length(trail)
    l=length(code)+1
    fail=(FAIL,nothing,ttop,i)
    global fuel;fuel-=1;if fuel<=0;return fail;end
    while i<l
        unwind(trail,ttop)
        clause,k=code[i]
        vs=[]
        i+=1
        #println("\n!!! ENTERING step: i=",i-1)
        for templ in clause
            (op,c1,c2,c3)=instr=activate(templ,k,vs)
            if op=='u'
                old,oldt=deref(c3)
                if VAR==oldt
                    old.val=Pair(c1,c2)
                    continue
                else
                    @assert(PAIR==oldt,pt(c3))
                    ok= unify(c1,old.first,trail,varctr.val)
                    if !ok
                        break
                    end
                    ok= unify(c2,old.second,trail,varctr.val)
                    if !ok
                        break
                    end
                end
                continue
            elseif op=='b'
                old,oldt=deref(c3)
                old.val=Pair(c1,c2)
                continue
            elseif op=='d'
                c1.val=G
                continue
            else
                @assert(op=='p',"EXPECTED: p")
                varctr.val+=k
                NewG,tg=deref(c1)

                if NewG=="true" && CONST == tg
                    return (DONE,G,ttop,i)
                else
                    @assert(PAIR==tg,"!!!PAIR")
                    return (DO,(NewG,G),ttop,i)
                end
            end
        end
    end
    fail
end

# trampoline state machine states
FAIL,DONE,DO,UNDO=1,2,3,4

opn=["FAIL","DONE","DO","UNDO"]

function ensure_undo(G,todo,ttop,i,l)
    instr = (UNDO, G, ttop, i)
    push!(todo,instr)
end

# goal for entry point convention
# assuming execution starts from predicate goal(ANSWER)
# and when found, answer is printed out
function get_goal()
    answer=ivar(0,"ANSWER")
    Pair(answer,Pair("true","goal"))
end

function interp()
  global fuel;fuel-=1;if fuel<=0;return;end
  code=tload()
  l=length(code)+1
  todo=[];trail=[]
  goal=get_goal()
  answer=goal.first
  push!(todo,(DO,(goal,nothing),0,l+1))

  varctr=ctr(1)
  while(!isempty(todo))
      action=pop!(todo)
      (op,G,ttop,i)=action

      if DO==op # advance forward oin AND branch
          NewG,OldG=G
          if i<l
              ensure_undo(OldG,todo,ttop,i,l)
          end
          r=step_(NewG,1,code,trail,varctr)
          push!(todo,r)
      elseif DONE==op # show ANSWER
          println(">>>ANSWER:",pt(answer))
          if i<l
              ensure_undo(G,todo,ttop,i,l)
          end
      elseif UNDO==op # explore next OR alternative
          unwind(trail,ttop)
          if i<l
              push!(todo,step_(G,i,code,trail,varctr))
          end
      else # FAIL - done with finding matching clauses
      end
  end
end

# IO

# more human readable string representation
function pt(z, size = 2000)
    if z==nothing;return z;end
    function pt0(a, k)
        if k <= 0
            return "<?>"
        else
            x, t = deref(a)
            if t == PAIR
                u, v = x
                k -= 1
                s1=pt0(u, k)
                s2=pt0(v, k)
                return string("(", s1, "->", s2, ")")
            elseif t == VAR
                #return string("_", string(objectid(x)))
                return string(x.name,"",x.age)
            else
                @assert(CONST==t,"should be CONST!")
                return string(x)
            end
        end
    end
    return pt0(z, size)
end

# pair made of a dictionary and a list
mutable struct ST
    d::Any
    a::Any
end

# creats empty dict+array pair
function new_st()
    ST(Dict(), [])
end

# add clause var inless seen already
function add_cvar(w,st,ctr)
    if haskey(st.d, w)
        st.d[w]
    else
        ctr.val+=1
        push!(st.a, w)
        l = length(st.a)
        v = ivar(l,w)
        st.d[w] = ivar(l, w)
        v
    end
end

# vars are uppercvas othes are constants
function vc(w,st,ctr)::Any
    if isuppercase(w[1])
        add_cvar(w,st,ctr)
    else
        w
    end
end

# extract instruction template from tokes on a line
function to_instr(toks,st,ctr)
    op = toks[1]
    @assert(op!=nothing,"OP!!!")
    if (op == "d") || (op == "p")
        instr = (op[1], vc(toks[2],st,ctr), nothing, nothing)
    else
        instr = (op[1], vc(toks[2],st,ctr),
        vc(toks[3],st,ctr), vc(toks[4],st,ctr))
    end
end

# mutable counter
mutable struct ctr
    val
end

# creates new variable from templat unless arleady in vs
function nv(t,k,vs)
    if t isa Var
        if(t.age<=length(vs))
            return vs[t.age]
        else
          v=ivar(t.age+k,t.name)
          push!(vs,v)
          return v
      end
    else
        t
    end
end

# activates variables for instruction template
function activate(ts,k,vs)
   ts[1],nv(ts[2],k,vs),nv(ts[3],k,vs),nv(ts[4],k,vs)
end

function tload(fname = "../out/tnf_asm.txt")
    lines = readlines(fname)
    st=new_st()
    code=[]
    cls=[]
    count=ctr(0)
    for line in lines
        if length(line) < 2
            continue
        end
        #println("LINE:",line)
        toks = split(line)
        #for t in toks;println("TOK=",String(t));end;println()
        push!(cls,to_instr(toks,st,count))
        if toks[1]=="p"
            push!(code,(cls,count.val))
            st=new_st()
            cls=[]
            count=ctr(0)
        end
    end

    for i in 1:length(code)
        c,count=code[i]
        vs=[]
        for x in c
            #println('X',deref(x[1]))
            #pti(x)
            a=activate(x,100,vs)

        end
        #println("count: i=",i," var count=",count) #;ptrail(vs)
    end

    code
end

# show trail
function ptrail(xs)
    println("TRAIL:")
       for x in xs
           println(pt(x))
       end
       println("")
   end

# show todo stack
function ptodo(xs)
       println("TODO:")
          for x in xs
              pta(x)
          end
          println("")
end

# show instruction
function pti(instr)
    s=" , "
    op,x1,x2,x3=instr
    println("<",op,">::",pt(x1),s,pt(x2),s,pt(x3))
end

# show state machine action
function pta(action)
    s=" , "
    act,G,ttop,i=action
    if act==DO
        println(opn[act],": ",pt(G[1]),s,pt(G[2]),s,ttop,i)
    else
        println(opn[act],": ",pt(G),s,s,ttop,i)
    end
end

########## tests ##########
function test()
    println("TEST")
    k=10
    trail=[]
    v=ivar(1,"V")
    u=ivar(2,"U")
    x=ivar(3,"X")
    y=ivar(4,"Y")
    bindVar(x,v,trail,k)
    bindVar(y,u,trail,k)
    println("DEREF: ",pt(x))
    p1=Pair(x,"a")
    p2=Pair("b",y)

    println("UNIF BEFORE: ",pt(p1)," ==== ",pt(p2))
    unify(p1,p2,trail,k)
    println("UNIF AFTER:  ",pt(p1)," ==== ",pt(p2))
    ptrail(trail)
    println(length(trail))
    unwind(trail,0)
    println("UNWINDED")
    ptrail(trail)

end

#clearconsole()

#test()
interp()
