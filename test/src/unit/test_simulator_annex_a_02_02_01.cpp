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

// A class property written with `var` and an implicit_data_type of packed
// dimensions alone is as wide as they make it: 300 stored in an 8-bit
// property reads back as 44.
TEST(NetAndVariableTypeSimulation, VarClassPropertyOfImplicitTypeHasItsWidth) {
  auto val = RunAndGet(
      "class C;\n"
      "  var [7:0] z;\n"
      "endclass\n"
      "module t;\n"
      "  int out;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.z = 300;\n"
      "    out = c.z;\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(val, 44u);
}

// A.2.2.1 counts a type_reference among the data types (§6.23). A typedef of
// one names x's int, so v holds -5 whole where an implicit type's one bit would
// hold 1; a nettype of one has y's four bits, all of which n carries; and a
// structure member of one is an int, which holds -5 for r to read back.
TEST(NetAndVariableTypeSimulation, TypeReferencesNameTheReferencedType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  logic [3:0] y;\n"
      "  typedef type(x) xt;\n"
      "  nettype type(y) nt;\n"
      "  xt v;\n"
      "  nt n;\n"
      "  struct packed { type(x) f; bit k; } s;\n"
      "  int r;\n"
      "  assign n = 4'hA;\n"
      "  initial begin\n"
      "    v = -5;\n"
      "    s.f = -5;\n"
      "    r = s.f;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"v", 0xFFFFFFFBu}, {"n", 0xAu}, {"r", 0xFFFFFFFBu}});
}

// A class property and a subroutine's formals take a type_reference after
// `var` (§6.23): w, y and z are each x's int, so -5 stands whole in each,
// where a one-bit one would hold 1.
TEST(NetAndVariableTypeSimulation, PropertyAndFormalsOfATypeReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  var type(x) w;\n"
      "endclass\n"
      "module t;\n"
      "  int x;\n"
      "  int rw, ry, rz;\n"
      "  C c;\n"
      "  function automatic int f(input var type(x) y);\n"
      "    return y;\n"
      "  endfunction\n"
      "  function automatic int g;\n"
      "    input var type(x) z;\n"
      "    return z;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.w = -5;\n"
      "    rw = c.w;\n"
      "    ry = f(-5);\n"
      "    rz = g(-5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"rw", 0xFFFFFFFBu}, {"ry", 0xFFFFFFFBu}, {"rz", 0xFFFFFFFBu}});
}

// A class property's type reference names another property of its class,
// found past the class's other members, a method and a property of another name
// among them, a built-in type, or a value of the scope around the class
// (§6.23). w is z's byte, and k and u, of the compilation unit's g, are each an
// int, so each holds -5 for rw, rk and ru to read back, where a one-bit
// property would hold 1. e's argument is an expression rather than a name,
// which the compilation unit has no values to type, and the class stands with
// it all the same.
TEST(NetAndVariableTypeSimulation,
     PropertyTypeReferencesFindAPropertyOrABuiltInType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "int g;\n"
      "class C;\n"
      "  function void touch();\n"
      "  endfunction\n"
      "  int x;\n"
      "  byte z;\n"
      "  var type(z) w;\n"
      "  var type(int) k;\n"
      "  var type(g) u;\n"
      "  var type(x + 1) e;\n"
      "endclass\n"
      "module t;\n"
      "  int rw, rk, ru;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.w = -5;\n"
      "    c.k = -5;\n"
      "    c.u = -5;\n"
      "    rw = c.w;\n"
      "    rk = c.k;\n"
      "    ru = c.u;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"rw", 0xFFFFFFFBu}, {"rk", 0xFFFFFFFBu}, {"ru", 0xFFFFFFFBu}});
}

}  // namespace
