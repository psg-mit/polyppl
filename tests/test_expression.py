import unittest

import islpy
from polyppl.ir import *  # pylint: disable=unused-wildcard-import
from polyppl.expression import *  # pylint: disable=unused-wildcard-import

from tests.base import PolyPPLTestCaseBase


class TestIR(PolyPPLTestCaseBase):

  def test_affine_expression_cast(self):
    exp = AffineExpression("+", [
        AffineExpression("+", [
            RefExpression("x"),
            AffineExpression("+", [
                RefExpression("y"),
                AffineExpression("+", [
                    OpExpression("-", [RefExpression("z")]),
                    ConstExpression(1)
                ])
            ])
        ])
    ])
    aff_exp = expression_to_isl(exp, ["x", "y"], params=["z"], ctx=self.isl_ctx)
    aff_exp_correct = islpy.Aff.read_from_str(
        self.isl_ctx, "[z] -> { [x, y] -> [x + y - z + 1] }")
    self.assertEqual(aff_exp, aff_exp_correct)


if __name__ == '__main__':
  unittest.main()
