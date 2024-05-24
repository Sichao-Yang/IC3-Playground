from z3 import *


# conjunction of literals.
class tCube:
    # make a tcube object assosciated with frame t.
    def __init__(self, t=0):
        self.t = t
        self.cubeLiterals = list()

    # 解析 sat 求解出的 model, 并将其加入到当前 tCube 中
    def addModel(self, lMap, model):
        no_primes = [l for l in model if str(l)[-1] != "'"]
        no_input = [l for l in no_primes if str(l)[0] != "i"]
        self.add(simplify(And([lMap[str(l)] == model[l] for l in no_input])))

    # 扩增 CNF 式
    def addAnds(self, ms):
        for i in ms:
            self.add(i)

    # 增加一个公式到当前 tCube() 中
    def add(self, m):
        g = Goal()
        g.add(m)
        t = Tactic("tseitin-cnf")  # 转化得到该公式的 CNF 范式
        for c in t(g)[0]:
            self.cubeLiterals.append(c)
        if len(t(g)[0]) == 0:
            self.cubeLiterals.append(True)

    # 删除第 i 个元素，并返回 tCube
    def delete(self, i: int):
        res = tCube(self.t)
        for it, v in enumerate(self.cubeLiterals):
            if i == it:
                res.add(True)
                continue
            res.add(v)
        return res

    def cube(self):
        return simplify(And(self.cubeLiterals))

    def __repr__(self):
        return str(self.t) + ": " + str(sorted(self.cubeLiterals, key=str))


class PDR:
    def __init__(self, primary_inputs, literals, primes, init, trans, post):
        self.primary_inputs = primary_inputs
        self.init = init
        self.trans = trans
        self.literals = literals
        self.items = self.primary_inputs + self.literals
        self.lMap = {str(l): l for l in self.items}
        self.post = post
        self.frames = list()
        self.primeMap = [(literals[i], primes[i]) for i in range(len(literals))]
        # print("init:")
        # print(self.init.cube())
        # print("trans...")
        # print(self.trans.cube())
        # print("post:")
        # print(self.post.cube())

    def run(self):
        self.frames = list()
        self.frames.append(self.init)

        while True:
            c = self.getBadCube()
            if c is not None:
                # Recursive blocking stage
                # print("get bad cube!")
                trace = self.recBlockCube(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    for f in trace:
                        print(f)
                    return False
                print("recBlockCube Ok! F:")
                for i in self.frames:
                    print(i)
            else:
                print("Adding frame " + str(len(self.frames)) + "...")
                self.frames.append(tCube(len(self.frames)))
                # Propagation stage
                for index, frame in enumerate(self.frames[:-1]):
                    for c in frame.cubeLiterals:
                        s = Solver()
                        # if (F[i] and T and Not(c)') == unsat, it means F[i] & T => c', c can be added to F[i+1]
                        s.add(And(frame.cube(), self.trans.cube(), Not(substitute(c, self.primeMap)))) 
                        if s.check() == unsat:
                            self.frames[index + 1].add(c)
                    if self.checkForInduction(frame):
                        print("Fond inductive invariant:\n" + str(frame.cube()))
                        return True
                print("New Frame " + str(len(self.frames) - 1) + ": ")
                print(self.frames[-1].cube())

    def checkForInduction(self, frame):
        print("check for Induction now...")
        s = Solver()
        # if unsat, it means F[i] & T => F[i]' is valid
        s.add(And(self.trans.cube(),frame.cube(),Not(substitute(frame.cube(), self.primeMap))))  
        if s.check() == unsat:
            return True
        return False

    def recBlockCube(self, s0: tCube):
        print("recBlockCube now...")
        Q = [s0]
        while len(Q) > 0:
            s = Q[-1]
            if s.t == 0:
                return Q
            z = self.solveRelative(s)
            if z is None:
                Q.pop()
                s = self.MIC(s)
                for i in range(1, s.t + 1):
                    self.frames[i].add(Not(s.cube()))
            else:
                Q.append(z)
        return None

    def MIC(self, q: tCube):
        # Generalization
        for i in range(len(q.cubeLiterals)):
            q1 = q.delete(i)
            if self.down(q1):
                q = q1
        return q
        # i = 0
        # while True:
        #     print(i)
        #     if i < len(q.cubeLiterals) - 1:
        #         i += 1
        #     else:
        #         break
        #     q1 = q.delete(i)
        #     if self.down(q1):
        #         q = q1
        # return q

    def down(self, q: tCube):
        while True:
            s = Solver()
            s.push()
            s.add(And(self.frames[0].cube(), Not(q.cube())))
            if unsat == s.check():
                return False
            s.pop()
            s.push()
            s.add(
                And(self.frames[q.t].cube(), Not(q.cube()), self.trans.cube(), substitute(q.cube(), self.primeMap))
            )  # Fi and not(q) and T and q'
            if unsat == s.check():
                return True
            # m = s.model()
            # q.addModel(self.lMap, m)
            # s.pop()
            return False

    # tcube is bad state
    def solveRelative(self, tcube):
        cubePrime = substitute(tcube.cube(), self.primeMap)
        s = Solver()
        s.add(self.frames[tcube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(Not(tcube.cube()))
        s.add(cubePrime)  # F[i - 1] and T and Not(badCube) and badCube'
        if s.check() == sat:
            model = s.model()
            c = tCube(tcube.t - 1)
            c.addModel(self.lMap, model)  # c = sat_model
            return c
        return None

    def getBadCube(self):
        print("seek for bad cube...")
        model = And(Not(self.post.cube()), self.frames[-1].cube())  # F[k] and Not(p)
        s = Solver()
        s.add(model)
        if s.check() == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, s.model())  # res = sat_model
            print("get bad cube:")
            print(res.cube())
            return res
        else:
            return None


if __name__ == "__main__":
    pass
