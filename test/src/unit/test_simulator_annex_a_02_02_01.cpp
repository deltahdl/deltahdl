#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeLogicRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hAB;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomByteRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte b;\n"
      "  initial b = 8'h7F;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomIntRuntimeWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  int i;\n"
      "  initial i = 32'hDEAD_BEEF;\n"
      "endmodule\n",
      "i");
  EXPECT_EQ(val, 0xDEADBEEFull);
}

TEST(NetAndVariableTypeSimulation, SigningSignedExtendsThroughArithmetic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] y;\n"
      "  initial begin\n"
      "    s = -4'sd3;\n"
      "    y = s;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val & 0xFFu, 0xFDu);
}

TEST(NetAndVariableTypeSimulation, NetTypeWireDrivesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  assign w = 4'hA;\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(NetAndVariableTypeSimulation, StructUnionPackedMemberAccess) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "  logic [3:0] y;\n"
      "  initial begin\n"
      "    s = 8'hA5;\n"
      "    y = s.lo;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 0x5u);
}

TEST(NetAndVariableTypeSimulation, EnumNameValueResolvesAtRuntime) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef enum logic [2:0] { A = 0, B = 1, C = 4 } e_t;\n"
      "  e_t e;\n"
      "  logic [2:0] y;\n"
      "  initial begin\n"
      "    e = C;\n"
      "    y = e;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 4u);
}

TEST(NetAndVariableTypeSimulation, PackedDimensionDrivesRuntimeWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter int W = 12;\n"
      "  logic [W-1:0] data;\n"
      "  initial data = '0;\n"
      "endmodule\n",
      f, "data");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
}

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeBitIsTwoState) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [3:0] b;\n"
      "  initial b = 4'b1010;\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0xAu);
}

// A variable declared through `$unit ::` holds what the compilation unit's
// type holds, though the module declares a wider type of the same name: the
// unit's T is 4 bits, so 8'hAB keeps its low nibble, where m's byte T would
// keep all of it (#7595).
TEST(NetAndVariableTypeSimulation, VariableOfAUnitScopedTypeHasTheUnitsWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "typedef logic [3:0] T;\n"
      "module t;\n"
      "  typedef byte T;\n"
      "  $unit::T a;\n"
      "  initial a = 8'hAB;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

// A nettype may rename one named through `$unit ::` as a data_type of A.2.2.1:
// the module's own nt, resolved by mres, hides the unit's, and unt renames the
// unit's nt all the same, so a net of unt resolves through ures, which ANDs the
// two drivers, 3 & 5 = 1, where mres would OR them to 7 (#7595).
TEST(NetAndVariableTypeSimulation,
     NettypeRenamedThroughTheUnitScopeIsTheUnits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("function automatic logic [3:0] ures(input logic [3:0] "
                 "d[]);\n"
                 "  ures = 4'hf;\n"
                 "  foreach (d[i]) ures = ures & d[i];\n"
                 "endfunction\n"
                 "nettype logic [3:0] nt with ures;\n"
                 "module t;\n"
                 "  function automatic logic [3:0] mres(input logic [3:0] "
                 "d[]);\n"
                 "    mres = 0;\n"
                 "    foreach (d[i]) mres = mres | d[i];\n"
                 "  endfunction\n"
                 "  nettype logic [3:0] nt with mres;\n"
                 "  nettype $unit::nt unt;\n"
                 "  unt n;\n"
                 "  assign n = 4'h3;\n"
                 "  assign n = 4'h5;\n"
                 "  initial begin\n"
                 "    #1;\n"
                 "    $display(\"%0h\", n);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1\n");
}

}  // namespace
