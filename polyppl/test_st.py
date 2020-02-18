import copy
import numpy as np


def f(x):
  return x * 2 + 1


def f1(N, A, B):
  A, B = map(copy.deepcopy, [A, B])
  for c0 in range(0, N, 1):
    for c1 in range(0, c0, 1):
      A[c0] += B[c1]
    B[c0] = f(A[c0])
  return A, B


def f2(N, A, B):
  A, B = map(copy.deepcopy, [A, B])
  A_add = np.zeros_like(A)
  A_sub = np.zeros_like(A)
  for c0 in range(0, N, 1):
    for c1 in range(max(0, c0 - 3), c0, 1):
      A_add[c0] += B[c1]
    if c0 >= 4:
      A[c0] = A_add[c0] + A[c0 + -3]
    elif c0 >= 1:
      A[c0] = A_add[c0]
    B[c0] = f(A[c0])
  return A, B


N = 10

A = np.zeros((N,), dtype=int)
B = np.ones((N,), dtype=int)

print(f1(N, A, B))
print(f2(N, A, B))