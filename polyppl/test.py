import numpy as np

N = 20
B = np.random.randint(0, high=5, size=N + 1)
x = np.arange(N * 2) % 5
y = np.arange(N * 2) % 4

f = lambda x: x + 1
g = f


def f1(N, B, x, y):
  B = np.array(B)
  A = np.zeros_like(B)
  for c0 in range(0, N, 1):
    for c1 in range(0, c0, 1):
      if x[c0] == A[c0 - 1]:
        A[c0] += f(B[c1])
    B[c0 + 1] = g(A[c0])
  return B


def f2(N, B, x, y):
  B = np.array(B)
  A = np.zeros((N * 10,) + B.shape, dtype=int)
  for c0 in range(0, N, 1):
    for c1 in range(0, c0, 1):
      A[A[x[c0 - 1]][c0 - 1]][c0] += f(B[c1])
    B[c0 + 1] = g(A[x[c0]][c0])
  return B


print(f1(N, B, x, y))
print(f2(N, B, x, y))
