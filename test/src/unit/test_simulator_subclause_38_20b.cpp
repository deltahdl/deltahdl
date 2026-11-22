#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class MultiIndexOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Select(vpiHandle ref, std::vector<PLI_INT32> indices) {
    return vpi_handle_by_multi_index(
        ref, static_cast<PLI_INT32>(indices.size()), indices.data());
  }

  static int ValueOf(vpiHandle ref, std::vector<PLI_INT32> indices) {
    vpiHandle obj = Select(ref, std::move(indices));
    if (obj == nullptr) return -1;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(MultiIndexOfARun, AVariableArraysIndicesAreDeclaredValuesLeftmostFirst) {
  Run("module top; int a[1:0][4:2];\n"
      "  initial for (int i = 0; i < 2; i++)\n"
      "    for (int j = 2; j < 5; j++) a[i][j] = 10 * i + j;\n"
      "endmodule\n");
  vpiHandle a = By("top.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Select(a, {0, 3})), vpiIntVar);
  EXPECT_EQ(ValueOf(a, {0, 3}), 3);
  EXPECT_EQ(ValueOf(a, {1, 4}), 14);
  EXPECT_EQ(ValueOf(a, {1, 2}), 12);
  EXPECT_EQ(Select(a, {4, 1}), nullptr);
  EXPECT_EQ(Select(a, {0, 0}), nullptr);
  EXPECT_EQ(Select(a, {2, 3}), nullptr);
}

TEST_F(MultiIndexOfARun, ANetArraysIndicesAreDeclaredValues) {
  Run("module top; wire [7:0] w [1:2][3:5];\n"
      "  assign w[1][3] = 8'd13; assign w[1][4] = 8'd14;\n"
      "  assign w[1][5] = 8'd15; assign w[2][3] = 8'd23;\n"
      "  assign w[2][4] = 8'd24; assign w[2][5] = 8'd25;\n"
      "  initial $noop; endmodule\n");
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Select(w, {2, 4})), vpiNet);
  EXPECT_EQ(ValueOf(w, {2, 4}), 24);
  EXPECT_EQ(ValueOf(w, {1, 3}), 13);
  EXPECT_EQ(ValueOf(w, {1, 5}), 15);
  EXPECT_EQ(Select(w, {0, 0}), nullptr);
  EXPECT_EQ(Select(w, {3, 3}), nullptr);
  EXPECT_EQ(Select(w, {4, 2}), nullptr);
}

TEST_F(MultiIndexOfARun,
       DISABLED_ANetArraysIndicesDescendOnToABitOfTheElement) {
  Run("module top; wire [7:0] w [1:2][3:5];\n"
      "  assign w[2][4] = 8'b0001_1000; initial $noop; endmodule\n");
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  vpiHandle bit = Select(w, {2, 4, 3});
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiNetBit);
  EXPECT_EQ(ValueOf(w, {2, 4, 3}), 1);
  EXPECT_EQ(ValueOf(w, {2, 4, 0}), 0);
  EXPECT_EQ(vpi_compare_objects(bit, vpi_handle_by_index(Select(w, {2, 4}), 3)),
            1);
}

TEST_F(MultiIndexOfARun, ABitSelectFollowsTheIndicesOfAVariableArray) {
  Run("module top; logic [7:0] mem [0:3]; logic [7:0] m [2][3];\n"
      "  initial begin mem[2] = 8'b0010_0000; m[1][2] = 8'h80; end\n"
      "endmodule\n");
  vpiHandle mem = By("top.mem");
  vpiHandle m = By("top.m");
  ASSERT_NE(mem, nullptr);
  ASSERT_NE(m, nullptr);
  vpiHandle bit = Select(mem, {2, 5});
  ASSERT_NE(bit, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bit), vpiVarBit);
  EXPECT_EQ(vpi_compare_objects(
                bit, vpi_handle_by_index(vpi_handle_by_index(mem, 2), 5)),
            1);
  EXPECT_EQ(ValueOf(mem, {2, 5}), 1);
  EXPECT_EQ(ValueOf(mem, {2, 4}), 0);
  EXPECT_EQ(ValueOf(m, {1, 2, 7}), 1);
  EXPECT_EQ(ValueOf(m, {1, 2, 6}), 0);
}

TEST_F(MultiIndexOfARun, ABitSelectFollowsTheIndexOfANetArray) {
  Run("module top; wire [7:0] w [0:3];\n"
      "  assign w[2] = 8'b0010_0000; initial $noop; endmodule\n");
  vpiHandle w = By("top.w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Select(w, {2, 5})), vpiNetBit);
  EXPECT_EQ(ValueOf(w, {2, 5}), 1);
  EXPECT_EQ(ValueOf(w, {2, 4}), 0);
}

TEST_F(MultiIndexOfARun, AVectorTakesItsSoleIndexAsABitSelect) {
  Run("module top; logic [7:0] v = 8'h20; initial $noop; endmodule\n");
  vpiHandle v = By("top.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, Select(v, {5})), vpiVarBit);
  EXPECT_EQ(ValueOf(v, {5}), 1);
  EXPECT_EQ(ValueOf(v, {4}), 0);
  EXPECT_EQ(Select(v, {8}), nullptr);
}

TEST_F(MultiIndexOfARun, ABitSelectOutsideTheElementsRangeNamesNothing) {
  Run("module top; logic [7:0] mem [0:3]; initial $noop; endmodule\n");
  vpiHandle mem = By("top.mem");
  ASSERT_NE(mem, nullptr);
  EXPECT_NE(Select(mem, {2, 7}), nullptr);
  EXPECT_NE(Select(mem, {2, 0}), nullptr);
  EXPECT_EQ(Select(mem, {2, 8}), nullptr);
  EXPECT_EQ(Select(mem, {2, -1}), nullptr);
}

TEST_F(MultiIndexOfARun, AScalarElementTakesNoBitSelect) {
  Run("module top; logic s [0:3]; initial $noop; endmodule\n");
  vpiHandle s = By("top.s");
  ASSERT_NE(s, nullptr);
  EXPECT_NE(Select(s, {2}), nullptr);
  EXPECT_EQ(Select(s, {2, 0}), nullptr);
}

TEST_F(MultiIndexOfARun, DISABLED_AnUnpackedStructElementTakesNoBitSelect) {
  Run("module top; typedef struct { logic a; logic b; } st;\n"
      "  st us [0:1]; initial $noop; endmodule\n");
  vpiHandle us = By("top.us");
  ASSERT_NE(us, nullptr);
  EXPECT_NE(Select(us, {1}), nullptr);
  EXPECT_EQ(Select(us, {1, 0}), nullptr);
  EXPECT_EQ(Select(us, {1, 1}), nullptr);
}

TEST_F(MultiIndexOfARun, ABitSelectGivenTooEarlyIsReadAsAnArrayIndex) {
  Run("module top; logic [7:0] m [2][3]; initial $noop; endmodule\n");
  vpiHandle m = By("top.m");
  ASSERT_NE(m, nullptr);
  EXPECT_NE(Select(m, {1, 2}), nullptr);
  EXPECT_EQ(Select(m, {1, 7}), nullptr);
}

TEST_F(MultiIndexOfARun, IndicesThatFormNoLegalSelectOfARegArrayNameNothing) {
  Run("module top; reg [7:0] m [4:7][3:1];\n"
      "  initial begin m[5][2] = 8'h01; m[4][1] = 8'h02; m[7][3] = 8'h03; end\n"
      "endmodule\n");
  vpiHandle m = By("top.m");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(ValueOf(m, {5, 2}), 1);
  EXPECT_EQ(ValueOf(m, {4, 1}), 2);
  EXPECT_EQ(ValueOf(m, {7, 3}), 3);
  EXPECT_EQ(Select(m, {3, 2}), nullptr);
  EXPECT_EQ(Select(m, {-1, 2}), nullptr);
  EXPECT_EQ(Select(m, {2, 5}), nullptr);
  EXPECT_EQ(ValueOf(m, {5, 2, 0}), 1);
  EXPECT_EQ(ValueOf(m, {5, 2, 1}), 0);
  EXPECT_EQ(Select(m, {5, 2, 0, 0}), nullptr);
}

TEST_F(MultiIndexOfARun, OnlyNumIndexIndicesApply) {
  Run("module top; int m [2][3];\n"
      "  initial for (int i = 0; i < 2; i++)\n"
      "    for (int j = 0; j < 3; j++) m[i][j] = 10 * i + j;\n"
      "endmodule\n");
  vpiHandle m = By("top.m");
  ASSERT_NE(m, nullptr);
  PLI_INT32 indices[] = {1, 2};
  ASSERT_NE(vpi_handle_by_multi_index(m, 2, indices), nullptr);
  vpiHandle row = vpi_handle_by_multi_index(m, 1, indices);
  ASSERT_NE(row, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, row), 3);
  vpiHandle cell = vpi_handle_by_index(row, 2);
  ASSERT_NE(cell, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(cell, &value);
  EXPECT_EQ(value.value.integer, 12);
}

TEST_F(MultiIndexOfARun, NoIndicesOrANegativeCountNameNothing) {
  Run("module top; int m [2][3]; initial $noop; endmodule\n");
  vpiHandle m = By("top.m");
  ASSERT_NE(m, nullptr);
  PLI_INT32 indices[] = {1, 2};
  ASSERT_NE(vpi_handle_by_multi_index(m, 2, indices), nullptr);
  EXPECT_EQ(vpi_handle_by_multi_index(m, 0, indices), nullptr);
  EXPECT_EQ(vpi_handle_by_multi_index(m, -1, indices), nullptr);
}

TEST_F(MultiIndexOfARun,
       DISABLED_APackedMultidimensionalVectorYieldsItsSubvector) {
  Run("module top; logic [1:0][3:0] p = 8'hA6; initial $noop; endmodule\n");
  vpiHandle p = By("top.p");
  ASSERT_NE(p, nullptr);
  vpiHandle upper = Select(p, {1});
  ASSERT_NE(upper, nullptr);
  EXPECT_EQ(vpi_get(vpiSize, upper), 4);
  EXPECT_EQ(ValueOf(p, {1}), 0xA);
  EXPECT_EQ(ValueOf(p, {0}), 0x6);
  EXPECT_EQ(vpi_get(vpiType, Select(p, {1, 3})), vpiVarBit);
  EXPECT_EQ(ValueOf(p, {1, 3}), 1);
  EXPECT_EQ(ValueOf(p, {1, 2}), 0);
  EXPECT_EQ(ValueOf(p, {0, 1}), 1);
  EXPECT_EQ(ValueOf(p, {0, 0}), 0);
  EXPECT_EQ(Select(p, {2, 0}), nullptr);
  EXPECT_EQ(Select(p, {1, 4}), nullptr);
}

TEST_F(MultiIndexOfARun, AnInterfaceOrProgramArrayIsIndexedLikeAModulesOne) {
  Run("interface ifc; int im [2][3] = '{'{0, 0, 0}, '{0, 0, 8}};\n"
      "endinterface\n"
      "program prg; int gm [2][3] = '{'{0, 0, 0}, '{0, 0, 9}}; endprogram\n"
      "module top; ifc i(); prg g(); initial $noop; endmodule\n");
  vpiHandle im = By("top.i.im");
  vpiHandle gm = By("top.g.gm");
  ASSERT_NE(im, nullptr);
  ASSERT_NE(gm, nullptr);
  EXPECT_EQ(ValueOf(im, {1, 2}), 8);
  EXPECT_EQ(ValueOf(im, {1, 1}), 0);
  EXPECT_EQ(Select(im, {2, 0}), nullptr);
  EXPECT_EQ(ValueOf(gm, {1, 2}), 9);
  EXPECT_EQ(ValueOf(gm, {1, 1}), 0);
  EXPECT_EQ(Select(gm, {2, 0}), nullptr);
}

TEST_F(MultiIndexOfARun, DISABLED_APackagesArrayIsIndexedLikeAModulesOne) {
  Run("package pk; int pm [2][3] = '{'{0, 0, 0}, '{0, 0, 7}}; endpackage\n"
      "module top; initial $noop; endmodule\n");
  vpiHandle pm = By("pk::pm");
  ASSERT_NE(pm, nullptr);
  EXPECT_EQ(ValueOf(pm, {1, 2}), 7);
  EXPECT_EQ(ValueOf(pm, {1, 1}), 0);
  EXPECT_EQ(Select(pm, {2, 0}), nullptr);
}

TEST_F(MultiIndexOfARun,
       DISABLED_ADynamicArrayOfUnpackedArraysIsIndexedThroughBoth) {
  Run("module top; int d [][3];\n"
      "  initial begin d = new[2]; d[1][2] = 5; d[0][2] = 4; end\n"
      "endmodule\n");
  vpiHandle d = By("top.d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(ValueOf(d, {1, 2}), 5);
  EXPECT_EQ(ValueOf(d, {0, 2}), 4);
  EXPECT_EQ(ValueOf(d, {1, 1}), 0);
  EXPECT_EQ(Select(d, {2, 0}), nullptr);
  EXPECT_EQ(Select(d, {1, 3}), nullptr);
}

TEST_F(MultiIndexOfARun, AnObjectWithoutAccessByIndexNamesNothing) {
  Run("module sub; endmodule\n"
      "module top; parameter int P = 3; sub u(); initial $noop; endmodule\n");
  vpiHandle p = Named(vpiParameter, By("top"), "P");
  vpiHandle u = By("top.u");
  ASSERT_NE(p, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(Select(p, {0}), nullptr);
  EXPECT_EQ(Select(u, {0}), nullptr);
}

}  // namespace
}  // namespace delta
