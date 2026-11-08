#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(UtilitySystemTaskTest, BitsResultIsInteger) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("v", 7);
  var->value = MakeLogic4VecVal(f.arena, 7, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(PrimarySim, BitsOfCurrentlyEmptyQueueReturnsZero) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 0u);
}

TEST(PrimarySim, BitsOfNonEmptyQueueReportsLiveBitStreamSize) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

TEST(PrimarySim, BitsOf4StateVectorEqualsDeclaredWidth) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  int n;\n"
      "  initial begin\n"
      "    v = 32'bx;\n"
      "    n = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 32u);
}

TEST(PrimarySim, BitsOfPackedStructTypedefMatchesMemberSum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic valid; bit [8:1] data; } MyType;\n"
      "  int w_type;\n"
      "  int w_var;\n"
      "  MyType m;\n"
      "  initial begin\n"
      "    w_type = $bits(MyType);\n"
      "    w_var = $bits(m);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w_type = f.ctx.FindVariable("w_type");
  auto* w_var = f.ctx.FindVariable("w_var");
  ASSERT_NE(w_type, nullptr);
  ASSERT_NE(w_var, nullptr);
  EXPECT_EQ(w_type->value.ToUint64(), 9u);
  EXPECT_EQ(w_var->value.ToUint64(), 9u);
}

TEST(PrimarySim, BitsOfRangedDataTypeArg) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  initial n = $bits(logic [7:0]);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 8u);
}

TEST(PrimarySim, BitsOfDynamicArrayFromNewReportsLiveBitStreamSize) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int d[] = new[3];\n"
      "  int n;\n"
      "  initial n = $bits(d);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

TEST(PrimarySim, BitsResultUsableAsLocalparamValue) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  localparam int W = $bits(16'h0);\n"
      "  logic [W-1:0] v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 16u);
}

TEST(PrimarySim, BitsOfAModuleLocalClassScopedTypedefVariable) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  class Cfg;\n"
      "    typedef byte my_type;\n"
      "  endclass\n"
      "  Cfg::my_type v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 8u);
}

TEST(PrimarySim, BitsOfFixedSizeUnpackedArraysCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [7:0] m [0:1];\n"
                       "  wire [7:0] w [0:1];\n"
                       "  logic [7:0] md [2][3];\n"
                       "  int a [4];\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(m), "
                       "$bits(w), $bits(md), $bits(md[1]), $bits(a));\n"
                       "endmodule\n",
                       f),
            "16 16 48 24 128\n");
}

TEST(PrimarySim, BitsOfHierarchicallyNamedArraysCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic [7:0] mem[2:5];\n"
                       "  logic [3:0] m2[2][3];\n"
                       "  int q[$] = '{1, 2, 3};\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub u();\n"
                       "  initial $display(\"%0d %0d %0d %0d\", $bits(u.mem), "
                       "$bits(u.m2), $bits(u.m2[1]), $bits(u.q));\n"
                       "endmodule\n",
                       f),
            "32 24 12 96\n");
}

TEST(PrimarySim, BitsOfClassArrayPropertiesCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    logic [7:0] data[1:3];\n"
                       "    int d[];\n"
                       "    function int own; return $bits(data); endfunction\n"
                       "  endclass\n"
                       "  C m = new;\n"
                       "  initial begin\n"
                       "    m.d = new[2];\n"
                       "    $display(\"%0d %0d %0d\", $bits(m.data), m.own(), "
                       "$bits(m.d));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "24 24 64\n");
}

TEST(PrimarySim, BitsOfClassAndPackageScopedTypedefs) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef shortint T;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  class C;\n"
                       "    typedef byte T;\n"
                       "    class N;\n"
                       "      typedef bit [3:0] T;\n"
                       "    endclass\n"
                       "  endclass\n"
                       "  typedef C::T U;\n"
                       "  C::T x;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(x), "
                       "$bits(U), $bits(C::T), $bits(p::T), $bits(C::N::T));\n"
                       "endmodule\n",
                       f),
            "8 8 8 16 4\n");
}

TEST(PrimarySim, BitsOfAnUnpackedArrayTypedefName) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit Bits [36:1];\n"
      "  typedef bit B8 [8:1];\n"
      "  typedef byte M [2][3];\n"
      "  typedef Bits BB [2];\n"
      "  Bits b;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(Bits), $bits(b),\n"
      "                   $bits(B8), $bits(M), $bits(BB));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "36 36 8 48 72\n");
}

TEST(BitsSim, ATypeNameAtRunTimeIsItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter W = 10;\n"
                       "  typedef logic [W-1:0] word_t;\n"
                       "  word_t arr[3];\n"
                       "  initial $display(\"%0d %0d %0d %0d\", $bits(word_t), "
                       "$bits(arr), $bits(int), $bits(byte));\n"
                       "endmodule\n",
                       f),
            "10 30 32 8\n");
}

TEST(BitsSim, ACallIsSizedWithoutBeingMade) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int calls = 0;\n"
                       "  function int f();\n"
                       "    calls++;\n"
                       "    return 5;\n"
                       "  endfunction\n"
                       "  function logic [11:0] g();\n"
                       "    calls++;\n"
                       "    return 0;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d %0d\", $bits(f()), "
                       "$bits(g()), calls);\n"
                       "endmodule\n",
                       f),
            "32 12 0\n");
}

TEST(BitsSim, AUserSystemFunctionIsSizedWithoutItsCalltfRunning) {
  static int calls = 0;
  calls = 0;
  VpiContext vpi;
  SetGlobalVpiContext(&vpi);
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = VpiText("$user_f");
  data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
    ++calls;
    return 0;
  };
  data.sizetf = [](PLI_BYTE8*) -> PLI_INT32 { return 16; };
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  SimFixture f;
  const std::string kOut = RunCapture(
      "module t;\n"
      "  initial $display(\"%0d\", $bits($user_f()));\n"
      "endmodule\n",
      f);
  SetGlobalVpiContext(nullptr);
  EXPECT_EQ(kOut, "16\n");
  EXPECT_EQ(calls, 0);
}

}  // namespace
