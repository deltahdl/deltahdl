#include <gtest/gtest.h>

#include <string>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ExpressionValuesOfARun : public VpiDesignRun {
 protected:
  // The right side of the continuous assignment `scope` holds.
  static vpiHandle RhsIn(const char* scope) {
    vpiHandle it = vpi_iterate(vpiContAssign, By(scope));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  // The integer value of an object, or -1 where the routine fills none.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

// §38.15 with §37.3.5: an operation is an expression vpi_get_value can read,
// its value the expression evaluated, its names read where the source wrote
// them -- in the top, and in a child instance whose port names the same as a
// variable of the top. The operation held no storage and gave no value.
TEST_F(ExpressionValuesOfARun, AnOperationReadsAsItsExpressionEvaluates) {
  Run("module child(input logic [7:0] a); logic [7:0] b = 30;\n"
      "  wire [7:0] y; assign y = a + b;\n"
      "endmodule\n"
      "module top; logic [7:0] a = 5, b = 7; wire [7:0] y;\n"
      "  assign y = a + b; child u(.a(8'd1));\n"
      "endmodule\n");
  vpiHandle top = RhsIn("top");
  vpiHandle child = RhsIn("top.u");
  ASSERT_NE(top, nullptr);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(vpi_get(vpiType, top), vpiOperation);
  EXPECT_EQ(IntOf(top), 12);
  EXPECT_EQ(IntOf(child), 31);
}

// §37.17 detail 26 with §37.3.5: a select whose index is an operation stands
// for the element the operation's value names, m[2] for `m[i + 1]` with i 1,
// read and written alike. The index's value was taken from storage the
// operation does not have, so the select named no element: it read x and a
// put to it wrote nothing.
TEST_F(ExpressionValuesOfARun, ASelectIndexedByAnOperationNamesItsElement) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211; integer i = 1;\n"
      "  wire [7:0] y; assign y = m[i + 1];\n"
      "endmodule\n");
  vpiHandle select = RhsIn("top");
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(IntOf(select), 0x33);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x55;
  vpi_put_value(select, &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(By("top.m")), 0x44552211);
}

// §38.15 with §37.3.5: a function call and a system function call are
// expressions vpi_get_value reads by evaluating them, as is a select whose
// index is a call: f(5) is 10, $clog2(5) is 3, and m[f(i)] with f(1) 2 is
// m[2]. The calls held no storage and gave no value, and the select named no
// element.
TEST_F(ExpressionValuesOfARun, ACallReadsAsItsCallEvaluates) {
  Run("module top; logic [7:0] a = 5; logic [3:0][7:0] m = 32'h44332211;\n"
      "  integer i = 1; wire [7:0] y; wire [31:0] z; wire [7:0] w;\n"
      "  function automatic logic [7:0] f(input logic [7:0] x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  function automatic integer g(input integer x); return x + 1;\n"
      "  endfunction\n"
      "  assign y = f(a); assign z = $clog2(a); assign w = m[g(i)];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle system_call = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle select = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(call, nullptr);
  ASSERT_NE(system_call, nullptr);
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_EQ(IntOf(call), 10);
  EXPECT_EQ(vpi_get(vpiType, system_call), vpiSysFuncCall);
  EXPECT_EQ(IntOf(system_call), 3);
  EXPECT_EQ(IntOf(select), 0x33);
}

// §11.5.1 with §37.17 detail 26: a select whose index holds x, or names no
// element of the dimension it indexes, selects nothing, and reads x in each of
// its bits out of a 4-state vector and 0 out of a 2-state one, all 64 of them
// for an element as wide as a word; a value put to it is written nowhere.
TEST_F(ExpressionValuesOfARun, ASelectNamingNoElementReadsItsVectorsDefault) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211; integer i = 'x;\n"
      "  bit [3:0][7:0] b = 32'h44332211; integer j = 9;\n"
      "  logic [1:0][63:0] w = 0; integer k = 5;\n"
      "  wire [7:0] y, z; wire [63:0] v;\n"
      "  assign y = m[i]; assign z = b[j]; assign v = w[k];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle x_index = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle two_state = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle wide = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(x_index, nullptr);
  ASSERT_NE(two_state, nullptr);
  ASSERT_NE(wide, nullptr);
  s_vpi_value value = {};
  value.format = vpiBinStrVal;
  vpi_get_value(x_index, &value);
  EXPECT_STREQ(value.value.str, "xxxxxxxx");
  vpi_get_value(two_state, &value);
  EXPECT_STREQ(value.value.str, "00000000");
  vpi_get_value(wide, &value);
  EXPECT_EQ(std::string(value.value.str), std::string(64, 'x'));

  s_vpi_value put = {};
  put.format = vpiIntVal;
  put.value.integer = 0x55;
  EXPECT_EQ(vpi_put_value(x_index, &put, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(IntOf(By("top.m")), 0x44332211);
}

// §27.4 with §37.17 detail 26: a select written in a loop generate block
// whose index is the loop's genvar stands for the element the genvar names in
// the block instance, m[2] for g 2. The loop makes one instance, a
// continuous assignment in a block being one VPI object for every instance
// of it (#5694).
TEST_F(ExpressionValuesOfARun, AGenvarIndexedSelectNamesItsBlocksElement) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211;\n"
      "  for (genvar g = 2; g < 3; g++) begin : gb\n"
      "    wire [7:0] y; assign y = m[g];\n"
      "  end\n"
      "endmodule\n");
  vpiHandle select = RhsIn("top");
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(IntOf(select), 0x33);
}

}  // namespace
}  // namespace delta
