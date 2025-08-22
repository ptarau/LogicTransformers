import Foundation

class Term : Equatable & CustomStringConvertible {
  static func ==(this:Term,that:Term) -> Bool {
    return this === that
  }
  
  func deref() -> Term {
    return self
  }
  
  var description : String {
    return "<?>"
  }
}

class Empty : Term {
  override var description : String {
    return "empty"
  }
}

class NoCont : Term {
  override var description : String {
    return "nocont"
  }
}

class Absent : Term {
  override var description : String {
    return "absent"
  }
  
  override func deref() -> Term {
    //assert(false,"Absent, not to be dereffed")
    return self
  }
  
}

let empty=Empty()

let nocont = NoCont()

let absent = Absent()


class Var : Term  {
  static var ctr = 0
  
  var val : Term
  let id : Int
  
  override init() {
    val = empty
    id = Var.ctr
    Var.ctr+=1
  }
  
  override func deref() -> Term {
    if val === empty {
      return self
    }
    else {
      return val.deref()
    }
  }
  
  func free() -> Bool {
    val === empty
  }
  
  func bind(val: Term) {
    self.val=val
  }
  
  func unbind() {
    self.val=empty
  }
  
  override var description : String {
    if self.free() {
      return "_"+String(self.id)
    }
    else {
      return val.description
    }
  }
}

/*
class Const : Term  {
  let val : Int
  init(val : String) {
    var s=Const.syms[val]
    if nil==s {
      s=Const.syms.count
      Const.syms[val]=s
      Const.ints.append(val)
      //print("!!",val,s!)
    }
    self.val=s!
  }
  static func ==(this:Const,that:Const) -> Bool {
    return this.val == that.val
  }
  static var syms = Dictionary<String,Int>()
  static var ints = [String]()
  
  override var description : String {
    return Const.ints[val]
  }
}
*/


class Const : Term  {
  let val : String
  init(val : String) {
    self.val=val
  }
  static func ==(this:Const,that:Const) -> Bool {
    return this.val == that.val
  }
  override var description : String {
    return val
  }
}



class Pair : Term {
  let left : Term
  let right : Term
  
  init(left:Term,right:Term) {
    self.left=left
    self.right=right
  }
  
  override var description : String {
    return "("+left.description+"=>"+right.description+")"
  }
}

func unwind(trail:inout [Var],ttop:Int) {
  var i = trail.count-ttop
  while i>0 {
    let v = trail.popLast()!
    v.unbind()
    i-=1
  }
}

func unify(this:Term,that:Term, trail:inout [Var], umax:Int) -> Bool {
  var ts = [Term]()
  ts.append(that)
  ts.append(this)
  while ts.count>0 {
    let t1=ts.popLast()!
    let t2=ts.popLast()!
    let x1=t1.deref()
    let x2=t2.deref()
    
    if x1 === x2 {continue}
    else if x1 is Var {
      let v1 = x1 as! Var
      v1.bind(val:x2)
      if v1.id<umax {trail.append(v1)}
    }
    else if x2 is Var {
      let v2 = x2 as! Var
      v2.bind(val:x1)
      if v2.id<umax {trail.append(v2)}
    }
    else if x1 is Const && x2 is Const {
      let c1 = x1 as! Const
      let c2 = x2 as! Const
      let eq=(c1==c2)
      if !eq {return false}
    }
    else if x1 is Pair && x2 is Pair {
      let p1 = x1 as! Pair
      let p2 = x2 as! Pair
      let a1=p1.left
      let b1=p1.right
      let a2=p2.left
      let b2=p2.right
      ts.append(b2)
      ts.append(b1)
      ts.append(a2)
      ts.append(a1)
    }
    else {
      return false
    }
  }
  return true
}

func toVar(x:String, vars:inout Dictionary<String,Var>) -> Term {
  let c: Character = x[x.startIndex]
  if c.isUppercase {
    if let v = vars[x] {
      return v
    }
    else {
      let v=Var()
      vars[x]=v
      return v
    }
  }
  if x == "[|]" {
     return Const(val:".")
  }
  return Const(val:x)
}

func newVar(x:Term, vars:inout [Var]) -> Term {
  if x is Var {
    let v=x as! Var
    let i=v.id
    if i<vars.count {
      return vars[i]
    }
    else {
      let w=Var()
      vars.append(w)
      return w
    }
  }
  else {return x}
}


func activate(templ:[String],vars : inout Dictionary<String,Var>) -> (String,Term,Term,Term) {
  let op=templ[0]
  let x1=toVar(x: templ[1], vars: &vars)
  if op == "d" || op == "p" {
    let x2=absent
    let x3=absent
    return (op,x1,x2,x3)
  }
  else {
    let x2=toVar(x: templ[2],vars: &vars)
    let x3=toVar(x: templ[3],vars: &vars)
    return (op,x1,x2,x3)
  }
}


func reactivate(templ:(String, Term, Term, Term),vars : inout [Var]) -> (String,Term,Term,Term) {
  
  let (op,c1,c2,c3)=templ
  let x1=newVar(x: c1, vars: &vars)
  let x2=newVar(x: c2, vars: &vars)
  let x3=newVar(x: c3, vars: &vars)
  return (op,x1,x2,x3)
}

func getGoal()->Pair {
  assert(Var.ctr==0,"Var ctr expected 0")
  let answer = Var()
  //let cont=Const(val: "true")
  let cont=nocont
  let goal=Const(val: "goal")
  let cpair = Pair(left:cont,right:goal)
  let pair = Pair(left:answer,right:cpair)
  //return  (answer,(cont,'goal'))
  return pair
}

let FAIL=0,DO=1,DONE=2,UNDO=3

typealias Action = (Int,Term,Term,Int,Int)

func step(G:Term,cls:Int,code:[[(String, Term, Term, Term)]], trail:inout [Var])->Action {
  let ttop=trail.count
  var i=cls
  let umax=Var.ctr
  while i<code.count {
    unwind(trail: &trail,ttop: ttop)
    let clause : [(String, Term, Term, Term)]=code[i]
    i+=1
    
    //print("@@@ CLAUSE:",clause)
    
    var vars = [Var]()
    
    for templ : (String, Term, Term, Term) in clause {
      
      //print("!!!",templ)
      
      let c=reactivate(templ: templ,vars: &vars)
      
      let (op,c1,c2,c3)=c
      
      if "u"==op {
        //print("!!!--------UUUUU--------: ",c1,"=>",c2,"==",c3,"\n")
        
        let old = c3.deref()
        if old is Var {
          let p=Pair(left:c1,right:c2)
          let v=old as! Var
          v.bind(val: p)
          continue
        }
        else {
          assert(old is Pair,"EXPECTED old=Pair, got")
          let p = old as! Pair
          var ok = unify(this: c1,that: p.left,trail: &trail,umax:umax)
          if ok {ok = unify(this: c2,that: p.right,trail: &trail,umax:umax)}
          if ok {continue}
          break
        }
      }
      else if "b" == op {
        let old = c3.deref() as! Var
        let p=Pair(left:c1,right:c2)
        old.bind(val: p)
        continue
      }
        
      else if "d"==op {
        let v=c1 as! Var
        v.bind(val: G)
        continue
      }
      else { // "p"
        //assert("p"==op,"EXPECTED op=p")
        let NewG=c1.deref()
        
        if NewG is NoCont {
          return (DONE,absent,G,ttop,i)
        }
        else {
          return (DO,NewG,G,ttop,i)
        }
        
      }
    }
  }
  
  return (FAIL,absent,absent,0,0)
}

func interp(code:[[(String, Term, Term, Term)]]) {
  let l=code.count
  let goal : Pair = getGoal()
  let answer = goal.left
  var todo = [Action]()
  var trail = [Var]()
  todo.append((DO,goal,absent,0,l))
  var mtr=0
  var mtd=0
  while todo.count > 0 {
    let (op,G,oldG,ttop,i) = todo.popLast()!
    
    if DO==op {
      mtr=max(mtr,trail.count)
      mtd=max(mtd,todo.count)
      let r=step(G: G,cls: 0,code: code,trail: &trail)
      if i<l {
        todo.append((UNDO, oldG,absent,ttop,i))
      }
      todo.append(r)
    }
      
    else if DONE==op {
      if i<l {
        todo.append((UNDO, oldG,absent,ttop,i))
      }
      print("ANSWER:",answer,"TR:",mtr,mtd)
    }
      
    else if UNDO==op {
      unwind(trail: &trail, ttop: ttop)
      todo.append(step(G: G,cls: i, code: code,trail: &trail))
    }
      
    else if FAIL==op {
      continue
    }
      
    else {
      print("BAD op:",op)
    }
  }
}

func go() {
  //let f="../../../out/tnf_asm.txt"
  let f="/Users/tarau/sit/LogicTransformers/out/tnf_asm.txt"
  let code=file2code(fname:f)
  interp(code: code)
}

// IO
func file2string(path:String)->String {
  do {
    let data = try NSString(contentsOfFile: path,encoding: String.Encoding.ascii.rawValue)
    return data as String
  }
  catch {
    print("no such file:",path)
  }
  return ""
}

func sizeof <T> (_ : T) -> Int
{
  return (MemoryLayout<T>.size)
}

func file2code (fname : String) -> [[(String, Term, Term, Term)]] {
  let text = file2string(path:fname)
  let lines : [String] = text.components(separatedBy: "\n")
  
  var code = [[(String, Term, Term, Term)]]()
  var cs = [(String, Term, Term, Term)]()
  var vars = Dictionary<String,Var>()
  Var.ctr=0
  
  for line in lines {
    let parts : [String] = line.components(separatedBy: " ")
    if parts.count<2 {continue}
    let activated=activate(templ: parts,vars: &vars)
    cs.append(activated)
    if "p"==parts[0] {
      code.append(cs)
      //print("***",cs)
      cs=[]
      vars = Dictionary<String,Var>()
      Var.ctr=0
    }
  }
  Var.ctr=0
  return code
}


// TESTS

func utest() {
  let t1=Pair(left:Const(val:"a"),right:Var())
  let t2=Pair(left:Var(),right:Const(val:"b"))
  let umax=0
  
  let v=Var()
  let u=Var()
  v.bind(val:t1)
  u.bind(val:v)
  
  print(u.deref())
  
  print(Var(),Var())
  
  var trail=[Var]()
  trail.append(Var())
  
  print("unif",unify(this:t1,that:t2,trail:&trail,umax:umax))
  print(t1)
  print("TR",trail)
  unwind(trail:&trail,ttop:0)
  print("UNW",t1,t2)
}

func utest1() {
  let umax=0
  var trail = [Var]()
  let v10=Var()
  let v8=Var()
  let v0=Var()
  
  let goal=Const(val: "goal")
  let true_=Const(val: "true")
  
  let l1 = Pair(left:v8,right:goal)
  let l=Pair(left: v10,right: l1)
  
  let r1=Pair(left: true_, right:goal)
  let r=Pair(left: v0, right: r1)
  
  let ok=unify(this: l,that: r,trail: &trail, umax:umax)
  print("v10",v10,"v8",v8,"v0",v0)
  print(ok,trail)
  print(l,"=",r)
}

go()

/*
 //utest1()
 
 let v=Const(val: "a")
 let u=Const(val: "a")
 print(v==u)
 */

print("----- END ------")
