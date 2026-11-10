#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(NameSpaceSimulation, PackageNameSpaceValueAtRuntime) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int V = 7;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::V;\n"
      "  logic [31:0] y;\n"
      "  initial y = V;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 7u);
}

TEST(NameSpaceSimulation, ModuleNameSpaceInstanceAddressableAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] v;\n"
      "  initial v = 8'h55;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    #1;\n"
      "    r = c1.v;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0x55u);
}

TEST(NameSpaceSimulation, BlockNameSpaceIsolatesLocalVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin : b1\n"
      "    int x;\n"
      "    x = 1;\n"
      "    r1 = x;\n"
      "  end\n"
      "  initial begin : b2\n"
      "    int x;\n"
      "    x = 2;\n"
      "    r2 = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("r1");
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 1u);
  EXPECT_EQ(v2->value.ToUint64(), 2u);
}

TEST(NameSpaceSimulation, ModulesOwnEnumConstantNamedLikeAnOuterOne) {
  const char* const kSources[] = {
      "typedef enum {RED, BLUE, GREEN} color_t;\n"
      "module top;\n"
      "  typedef enum {A, GREEN} c_t;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
      "typedef enum {RED, BLUE, GREEN} color_t;\n"
      "module top;\n"
      "  enum {A, GREEN} v;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
      "package p;\n"
      "  typedef enum {RED, BLUE, GREEN} color_t;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef enum {A, GREEN} c_t;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
      "package p;\n"
      "  typedef enum {RED, BLUE, GREEN} color_t;\n"
      "endpackage\n"
      "import p::*;\n"
      "module top;\n"
      "  typedef enum {A, GREEN} c_t;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
  };
  for (const char* src : kSources) EXPECT_EQ(RunAndGet(src, "y"), 1u) << src;
}

TEST(NameSpaceSimulation, OuterEnumConstantReadWhereTheModuleDeclaresNone) {
  const char* const kSources[] = {
      "typedef enum {RED, BLUE, GREEN} color_t;\n"
      "module top;\n"
      "  typedef enum {A, B} c_t;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
      "package p;\n"
      "  typedef enum {RED, BLUE, GREEN} color_t;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef enum {A, B} c_t;\n"
      "  logic [31:0] y;\n"
      "  initial y = GREEN;\n"
      "endmodule\n",
  };
  for (const char* src : kSources) EXPECT_EQ(RunAndGet(src, "y"), 2u) << src;
}

TEST(NameSpaceSimulation, ModuleAndPackageOfOneNameAreBothReached) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package shared;\n"
                       "  localparam int K = 4;\n"
                       "endpackage\n"
                       "module shared;\n"
                       "  initial $display(\"module %0d\", shared::K);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  shared s();\n"
                       "endmodule\n",
                       f),
            "module 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(NameSpaceSimulation, NestedModuleNamedLikeATopLevelModuleIsNoClash) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  initial #1 $display(\"outer %m\");\n"
                       "endmodule\n"
                       "module holder;\n"
                       "  module leaf;\n"
                       "    initial $display(\"inner %m\");\n"
                       "  endmodule\n"
                       "  leaf l();\n"
                       "endmodule\n"
                       "module top;\n"
                       "  holder h();\n"
                       "  leaf o();\n"
                       "endmodule\n",
                       f),
            "inner top.h.l\nouter top.o\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
