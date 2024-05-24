from z3 import *
from queue import PriorityQueue
import collections
DEV = True


# This helper class specifies a cube and a frame
# in which it is reachable.
class Cube(object):
    def __init__(self, model, variable_lookup, frame_id=None):
        self.values = [simplify(variable_lookup[str(v)] == model[v]) for v in model if str(v) in variable_lookup]
        self.frame_id = frame_id

    def __lt__(self, other):
        return self.frame_id < other.frame_id

    def __eq__(self, other) : 
        return collections.Counter(self.values) == collections.Counter(other.values)

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


def get_trace_from_PQ(pq):
    trace = list()
    while not pq.empty():
        idx, cube = pq.get()
        trace.append(cube)
    return trace


class PDR(object):
    def __init__(self, variables, primes, init, trans, post, rec=True):
        self.variables = variables
        self.variable_dict = {str(v): v for v in self.variables}
        self.primes = primes
        self.vTOp = [*zip(variables, primes)]
        self.init = init
        self.trans = trans
        self.post = post
        self.rec = rec

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
    def is_blocked(self, cube, i):
        s = Solver()
        s.add(And(self.stack_frames[i].expression, cube))
        return s.check() == unsat

    # Tries to find a cube in the previous frame that would
    # reach the given cube
    def check_from_last_frame(self, cube):
        s = Solver()
        # Fi-1&T->s
        s.add(And(self.stack_frames[cube.frame_id - 1].expression, self.trans, substitute(cube.cube, self.vTOp)))
        if s.check() == unsat:
            return None
        return s.model()

    def check_from_current_frame(self, cube):
        s = Solver()
        # Fi-1&T->s
        s.add(And(self.stack_frames[cube.frame_id].expression, cube.cube))
        if s.check() == unsat:
            return None
        return s.model()

    # Checks whether the we have found an inductive invariant
    def check_ind_invariant(self):
        for frame in self.stack_frames:
            check_frame = frame.expression
            s = Solver()
            s.add(And(self.trans, check_frame, Not(substitute(check_frame, self.vTOp))))
            if s.check() == unsat:
                return check_frame
        return None

    def make_cube_from_solution(self, solution, i):
        cube = {v: solution[v] for v in solution if str(v) in self.variable_dict}
        return Cube(cube, self.variable_dict, i)

    # block a cube recursively
    # Returns None if the cube was able to be blocked
    # Returns a stack trace if the cube cannot be blocked
    def rec_block_cube(self, cube):
        # If solution is for frame 0, we have found a stack trace reaching ~post
        if cube.frame_id == 0:
            return [cube]
        assert not self.is_blocked(cube.cube, cube.frame_id)
        solution = self.check_from_last_frame(cube)
        # The cube is found to be unreachable by the previous frame
        if solution == None:
            # Block it in the frame it is found in and all previous frames
            for i in range(1, cube.frame_id + 1):
                # TODO: generalization on bad cube s
                if DEV:  # -13s
                    self.stack_frames[i].add_cube(simplify(cube.not_cube))
                else:
                    if not self.is_blocked(cube.cube, i):
                        self.stack_frames[i].add_cube(simplify(cube.not_cube))
            return None  # blocked
        # The cube is found to be reachable by the previous frame
        else:
            pre_cube = self.make_cube_from_solution(solution, cube.frame_id - 1)
            # block this new pre_cube as well
            trace = self.rec_block_cube(pre_cube)
            if trace is not None:
                return trace + [cube]
            else:
                # we still need to block current cube after block the pre_cube in last frame
                self.rec_block_cube(cube)

    def non_rec_block_cube(self, cube):
        Q = PriorityQueue()
        Q.put((cube.frame_id, cube))
        while not Q.empty():
            i, s = Q.get()
            if i == 0:  # CEX found!
                Q.put((i, s))
                return get_trace_from_PQ(Q)
            if self.check_from_current_frame(s) is None:
                continue
            solution = self.check_from_last_frame(s)
            if solution is not None:
                Q.put((s.frame_id - 1, self.make_cube_from_solution(solution, s.frame_id - 1)))
                Q.put((i, s))
            else:
                for i in range(1, s.frame_id + 1):
                    self.stack_frames[i].add_cube(simplify(s.not_cube))
                if s.frame_id < self.N:
                    s_up = copy.deepcopy(s)
                    s_up.frame_id = s.frame_id + 1
                    Q.put((s_up.frame_id, s_up))
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
                if self.rec:
                    trace = self.rec_block_cube(cube)
                else:
                    trace = self.non_rec_block_cube(cube)
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
