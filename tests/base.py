import unittest

import islpy


class PolyPPLTestCaseBase(unittest.TestCase):

  def setUp(self):
    self.isl_ctx = islpy.Context()
    self.isl_ctx.set_on_error(1)  # continue then raise exception
