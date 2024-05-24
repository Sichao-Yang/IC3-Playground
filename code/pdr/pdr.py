from z3 import *

DEV = True


# This helper class specifies a cube and a frame
# in which it is reachable.
class Cube(object):
    def __init__(self, model, variable_lookup, frame_id=None):
        self.values = [simplify(variable_lookup[str(v)] == model[v]) for v in model if str(v) in variable_lookup]
        self.frame_id = frame_id

    @property
    def cube(self):
        return And(*self.values)

    @property
    def not_cube(self):
        return Or(*[Not(value) for value in self.values])

    def __repr__(self):
        return "{" + ("" if self.frame_id == None else str(self.frame_id) + ": ") + str(self.values) + "}"


class StackFrame(object):
    def __init__(self, *cubes):
        self.cubes = list(cubes)
        self.expression = And(*cubes)

    def add_cube(self, cube):
        self.cubes.append(cube)
        self.expression = And(*self.cubes)


class PDR(object):
    def __init__(self, variables, primes, init, trans, post):
        self.variables = variables
        self.variable_dict = {str(v): v for v in self.variables}
        self.primes = primes
        self.vTOp = [*zip(variables, primes)]
        self.init = init
        self.trans = trans
        self.post = post

        self.stack_frames = [StackFrame(init)]
        self.stack_trace = []

    # Finds a cube in ~post and the latest frame
    def get_bad_cube(self, base):
        s = Solver()
        if base:
            badstate_formula = And(self.stack_frames[self.N].expression, Not(self.post))
        else:
            if DEV:
                # T&F&!p'
                badstate_formula = And(
                    self.trans, self.stack_frames[self.N].expression, Not(substitute(self.post, self.vTOp))
                )
            else:
                # F&!p
                badstate_formula = And(Not(self.post), self.stack_frames[self.N].expression)
        s.add(badstate_formula)
        if s.check() == sat:
            return Cube(s.model(), self.variable_dict, self.N)
        return None

    def newFrame(self):
        print("Add new frame", self.N)
        sys.stdout.flush()
        if DEV:
            newframe = StackFrame(self.post)  # F=p
        else:
            newframe = StackFrame()  # F=[]
        self.stack_frames.append(newframe)

    # Checks whether a cube has been entirely blocked
    # in the given frame, only for performance
    def isBlocked(self, cube, i):
        s = Solver()
        s.add(And(self.stack_frames[i].expression, cube))
        return s.check() == unsat

    # Tries to find a cube in the previous frame that would
    # reach the given cube
    def solveRelative(self, cube):
        cubePrime = substitute(cube.cube, self.vTOp)
        s = Solver()
        s.add(self.stack_frames[cube.i - 1].expression)
        s.add(self.trans)
        s.add(cubePrime)
        if s.check() == unsat:
            return None
        return s.model()

    # Checks whether the we have found an inductive invariant
    def check_ind_invariant(self):
        for i, frame in enumerate(self.stack_frames[:-1]):
            check_frame = frame.expression
            s = Solver()
            s.add(And(self.trans, check_frame, Not(substitute(check_frame, self.vTOp))))
            invariant = s.check() == unsat
            if invariant:
                return check_frame
        return None

    # block a cube recursively
    # Returns None if the cube was able to be blocked
    # Returns a stack trace if the cube cannot be blocked
    def rec_block_cube(self, cube):
        # If solution is for frame 0, we have found a stack trace reaching ~post
        if cube.i == 0:
            return [cube]
        while True:
            assert not self.isBlocked(cube.cube, cube.i)
            solution = self.solveRelative(cube)
            # The cube is found to be unreachable by the previous frame
            if solution == None:
                # Block it in the frame it is found in and all previous frames
                for i in range(1, cube.i + 1):
                    if not self.isBlocked(cube.cube, i):
                        self.stack_frames[i].add_cube(simplify(cube.not_cube))
                return None
            # The cube is found to be reachable by the previous frame
            else:
                candidate = {v: solution[v] for v in solution if str(v) in self.variable_dict}
                candidateCube = Cube(candidate, self.variable_dict, cube.i - 1)
                # Attempt to block this new candidate as well
                trace = self.rec_block_cube(candidateCube)
                if trace:
                    return trace + [cube]
        return None

    # Main entry point of PDR
    def run(self):
        # base case
        cube = self.get_bad_cube(base=True)
        if cube:
            return False, [cube]
        print("Passed base check: I&P")
        self.newFrame()
        while True:
            cube = self.get_bad_cube(base=False)
            if cube:
                trace = self.rec_block_cube(cube)
                if trace != None:  # found CTI
                    return False, trace
            else:
                # TODO: push forward?
                invariant = self.check_ind_invariant()
                if invariant is not None:
                    return True, invariant
                self.newFrame()

    @property
    def N(self):
        return len(self.stack_frames) - 1
