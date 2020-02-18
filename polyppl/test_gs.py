def gs(A, b, x, sigma, N, T):
  x_new = np.zeros_like(x)
  sigma1 = sigma
  sigma2 = np.zeros_like(sigma)
  c0 = 0
  while c0 < T:
    c1 = 0
    while c1 < N:
      c2 = c1 + 1
      while c2 < N:
        sigma2[c1, c0] += A[c1, c2] * x[c2, c0]
        c2 += 1
      x_new[c1, c0] = (b[c1] - sigma1[c1, c0] - sigma2[c1, c0]) / A[c1, c1]
      if T >= c0 + 2:
        x[c1, c0 + 1] = x_new[c1, c0]
      c2 = N + c1 + 1
      while c2 < 2 * N:
        sigma1[-N + c2, c0] += A[-N + c2, c1] * x_new[c1, c0]
        c2 += 1
      c1 += 1
    c0 += 1


def gs_correct(A, b, x, T):
  for it_count in range(1, T):
    x_new = np.zeros_like(x)
    print("Iteration {0}: {1}".format(it_count, x))
    for i in range(A.shape[0]):
      s1 = np.dot(A[i, :i], x_new[:i])
      s2 = np.dot(A[i, i + 1:], x[i + 1:])
      print("sigma", s1 + s2)
      x_new[i] = (b[i] - s1 - s2) / A[i, i]
    if np.allclose(x, x_new, rtol=1e-8):
      break
    x = x_new


N = 2
T = 10
import numpy as np
A = np.array([[16, 3], [7, -11]])
x = np.array([0.8122, -0.6650])
b = np.array([11, 13])
print("b:", b)
x_solve = np.linalg.solve(A, b)
print("Correct:", x)
print("Correct solve:", x_solve)
phi = np.zeros((N, T))
sigma = np.zeros((N, T))
phi[:, 0] = np.array([1, 1])
print(phi)
gs(A, b, phi, sigma, N, T)
print(phi)
gs_correct(A, b, np.array([1, 1]), T)