import operator
import numpy as np
import gurobipy as gp
GRB = gp.GRB


def add_np_mat_vars(model: gp.Model, shape, *args, **kwargs) -> np.ndarray:
  gp_vars = model.addVars(*shape, *args, **kwargs)
  ret = np.empty(shape, dtype=object)
  for coord, v in gp_vars.items():
    ret[coord] = v
  return ret


# Create a new model
m = gp.Model("miqp")
m.setParam("NonConvex", 2)

# Create variables
x = m.addVar(lb=0, ub=10, vtype=GRB.INTEGER, name="x")
# y = add_np_mat_vars(m, (2,), lb=-10, ub=10, vtype=GRB.INTEGER, name="y")

print(x)
b = m.addVar(vtype=GRB.BINARY, name="b")

# m.addConstr((b == 1) >> (x[0] * x[1] >= 2))
# m.addConstr((b == 1) >> (x <= 2))

# Set objective: x^2 + x*y + y^2 + y*z + z^2 + 2 x
# a = np.ones((2, 2))
# d = a.dot(y)
# obj = x.dot(y)
m.setObjective(x, GRB.MINIMIZE)
# Add constraint: x + 2 y + 3 z <= 4
# [m.addConstr(x <= 3) for x in a.dot(x)]
# m.addConstr(3 * x * x + 2 * y >= x * y, "c1")

m.optimize()

for v in m.getVars():
  print('%s %g' % (v.varName, v.x))

# print('Obj: %g' % obj.getValue())
