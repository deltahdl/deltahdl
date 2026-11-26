#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstConstantElaboration, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "const variable 'x' must be initialized", 2,
                            "6.20.6"));
}

TEST(ConstConstantElaboration, ConstIntWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            3, "6.20"));
}

TEST(ConstConstantElaboration, ConstNonblockingReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            3, "6.20"));
}

TEST(ConstConstantElaboration, ConstReassignmentInAlwaysFfIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  logic clk;\n"
      "  always_ff @(posedge clk) x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            4, "6.20"));
}

TEST(ConstConstantElaboration, ConstInitializedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top #(parameter P = 5);\n"
      "  const int x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromLocalparamSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam LP = 10;\n"
      "  const int x = LP;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromAnotherConstSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int a = 5;\n"
      "  const int b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  const int LIMIT = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "LIMIT") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstConstantElaboration, ConstInitializedFromEnumNameSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum int {RED, GREEN, BLUE} color_t;\n"
      "  const int x = GREEN;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromConstantFunctionSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int double_it(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  const int x = double_it(21);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstWithHierarchicalNameInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const logic option = a.b.c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromGenvarSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    const int x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstAutomaticAcceptsRuntimeInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int add_one(int a);\n"
      "    const int local_c = a + 1;\n"
      "    return local_c;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstClassHandleDeclarationSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new(int a);\n"
      "    x = a;\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstClassHandleReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj = new();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'obj'", 7, "6.20"));
}

TEST(ConstConstantElaboration, ConstObjectMemberWriteSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj.x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kHandleClass =
    "class C;\n"
    "  int x;\n"
    "  function new(int v);\n"
    "    x = v;\n"
    "  endfunction\n"
    "endclass\n";

TEST(ConstConstantElaboration, ConstClassHandleAsAnOutputOrRefActualIsError) {
  ElabFixture f;
  ElaborateSrc(std::string(kHandleClass) +
                   "module top;\n"
                   "  const C obj = new(5);\n"
                   "  task t1(output C o); endtask\n"
                   "  task automatic t2(ref C o); endtask\n"
                   "  initial begin\n"
                   "    t1(obj);\n"
                   "    t2(obj);\n"
                   "  end\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant 'obj' cannot be the actual of output argument 'o' of 't1'", 12,
      "6.20"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "constant 'obj' cannot be the actual of ref argument 'o' of 't2'", 13,
      "6.20"));
}

TEST(ConstConstantElaboration,
     ConstClassHandleAsAnInputOrConstRefActualIsAccepted) {
  ElabFixture f;
  auto* design =
      ElaborateSrc(std::string(kHandleClass) +
                       "module top;\n"
                       "  const C obj = new(5);\n"
                       "  task t3(input C o); endtask\n"
                       "  task automatic t4(const ref C o); endtask\n"
                       "  initial begin\n"
                       "    t3(obj);\n"
                       "    t4(obj);\n"
                       "  end\n"
                       "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

std::string StaticConstReadReport(const std::string& constant,
                                  const std::string& name) {
  return "static constant '" + constant + "' cannot be set from '" + name +
         "', which is a variable, net or port rather than a constant";
}

TEST(ConstConstantElaboration, StaticConstSetFromAVariableNetOrPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input int a);\n"
      "  int v;\n"
      "  wire [3:0] w;\n"
      "  typedef struct { int f; } s_t;\n"
      "  s_t s;\n"
      "  const int c1 = v;\n"
      "  const int c2 = w + 1;\n"
      "  const int c3 = a;\n"
      "  const int c4 = s.f;\n"
      "  const bit c5 = v[0];\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("c1", "v"), 6, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("c2", "w"), 7, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("c3", "a"), 8, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("c4", "s"), 9, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("c5", "v"), 10, "6.20.6"));
}

TEST(ConstConstantElaboration,
     StaticConstSetFromAVariableInAnInterfaceProgramOrGenerateBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  int iv;\n"
      "  const int ic = iv;\n"
      "endinterface\n"
      "program p;\n"
      "  int pv;\n"
      "  const int pc = pv;\n"
      "endprogram\n"
      "module m;\n"
      "  int mv;\n"
      "  if (1) begin : g\n"
      "    const int gc = mv;\n"
      "  end\n"
      "  i ii();\n"
      "  p pp();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("ic", "iv"), 3, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("pc", "pv"), 7, "6.20.6"));
  EXPECT_TRUE(
      ReportedError(diags, StaticConstReadReport("gc", "mv"), 12, "6.20.6"));
}

TEST(ConstConstantElaboration, StaticConstSetFromConstantsBesideAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  int v = 9;\n"
      "endmodule\n"
      "module m;\n"
      "  int v;\n"
      "  parameter P = 2;\n"
      "  localparam LP = 3;\n"
      "  typedef enum {A, B} e_t;\n"
      "  const int k = 1;\n"
      "  const int c = P + LP + B + k + $bits(v);\n"
      "  sub u();\n"
      "  const int d = u.v;\n"
      "  function automatic int fa(int a);\n"
      "    const int e = a + v;\n"
      "    return e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
