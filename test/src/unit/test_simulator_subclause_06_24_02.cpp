#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

RtlirDesign* ElaborateLowerRun(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) {
    return nullptr;
  }
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return design;
}

void RunEnumCast(SimFixture& f, const std::string& body, uint64_t& ok_out,
                 uint64_t& c_out) {
  std::string src =
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int ok;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateLowerRun(f, src);
  ASSERT_NE(design, nullptr);

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  ok_out = ok->value.ToUint64();
  c_out = c->value.ToUint64();
}

void RunEnumCondCast(SimFixture& f, const std::string& body, uint64_t& flag_out,
                     uint64_t& c_out) {
  std::string src =
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  int flag;\n"
      "  initial begin\n"
      "    flag = 0;\n" +
      body +
      "  end\n"
      "endmodule\n";
  auto* design = ElaborateLowerRun(f, src);
  ASSERT_NE(design, nullptr);

  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  flag_out = flag->value.ToUint64();
  c_out = c->value.ToUint64();
}

TEST(DynamicCastSim, CastEnumSuccess) {
  SimFixture f;
  uint64_t ok = 0, c = 0;
  RunEnumCast(f, "    ok = $cast(c, 1);\n", ok, c);
  EXPECT_EQ(ok, 1u);
  EXPECT_EQ(c, 1u);
}

TEST(DynamicCastSim, CastEnumTaskValid) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  initial begin\n"
                        "    $cast(c, 2);\n"
                        "  end\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(DynamicCastSim, CastEnumInCondition) {
  SimFixture f;
  uint64_t flag = 0, c = 0;
  RunEnumCondCast(f,
                  "    if ($cast(c, 1))\n"
                  "      flag = 1;\n",
                  flag, c);
  EXPECT_EQ(flag, 1u);
}

TEST(DynamicCastSim, TaskFormInvalidLeavesDestUnchanged) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  initial begin\n"
                        "    $cast(c, 1);\n"
                        "    $cast(c, 10);\n"
                        "  end\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$cast task could not assign the source expression "
                            "to the destination; assignment is invalid",
                            6, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormInvalidRaisesRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    $cast(c, 10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$cast task could not assign the source expression",
                            5, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormValidRaisesNoError) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  initial begin\n"
                        "    $cast(c, 2);\n"
                        "  end\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, FunctionFormInvalidRaisesNoError) {
  SimFixture f;
  uint64_t ok = 0, c = 0;
  RunEnumCast(f, "    ok = $cast(c, 10);\n", ok, c);
  EXPECT_EQ(ok, 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, FunctionFormInvalidPreservesDestValue) {
  SimFixture f;
  uint64_t ok = 0, c = 0;
  RunEnumCast(f,
              "    $cast(c, 1);\n"
              "    ok = $cast(c, 10);\n",
              ok, c);
  EXPECT_EQ(ok, 0u);
  EXPECT_EQ(c, 1u);
}

TEST(DynamicCastSim, FunctionFormInvalidConditionNotTaken) {
  SimFixture f;
  uint64_t flag = 0, c = 0;
  RunEnumCondCast(f,
                  "    if ($cast(c, 10))\n"
                  "      flag = 1;\n",
                  flag, c);
  EXPECT_EQ(flag, 0u);
}

TEST(DynamicCastSim, CastEnumWithExpression) {
  SimFixture f;
  uint64_t ok = 0, c = 0;
  RunEnumCast(f, "    ok = $cast(c, 1 + 1);\n", ok, c);
  EXPECT_EQ(ok, 1u);
  EXPECT_EQ(c, 2u);
}

TEST(DynamicCastSim, CastEnumFirstMember) {
  SimFixture f;
  uint64_t ok = 0, c = 0;
  RunEnumCast(f,
              "    $cast(c, 2);\n"
              "    ok = $cast(c, 0);\n",
              ok, c);
  EXPECT_EQ(ok, 1u);
  EXPECT_EQ(c, 0u);
}

TEST(DynamicCastSim, FunctionFormIntegralCastSucceeds) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  int d;\n"
                                   "  int ok;\n"
                                   "  initial begin\n"
                                   "    ok = $cast(d, 5);\n"
                                   "  end\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 5u);
}

TEST(DynamicCastSim, FunctionFormParameterSourceSucceeds) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  parameter int P = 2;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  int ok;\n"
                        "  initial ok = $cast(c, P);\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 1u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(DynamicCastSim, FunctionFormParameterSourceOutOfRangeFails) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  parameter int P = 9;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  int ok;\n"
                        "  initial begin\n"
                        "    c = GREEN;\n"
                        "    ok = $cast(c, P);\n"
                        "  end\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* ok = f.ctx.FindVariable("ok");
  ASSERT_NE(ok, nullptr);
  EXPECT_EQ(ok->value.ToUint64(), 0u);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
}

TEST(DynamicCastSim, TaskFormLocalparamSourceAssigns) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  localparam int LP = 1;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  initial $cast(c, LP);\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, TaskFormIntegralCastAssignsNoError) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  int d;\n"
                                   "  initial begin\n"
                                   "    $cast(d, 5);\n"
                                   "  end\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);

  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->value.ToUint64(), 5u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DynamicCastSim, TaskCallInvalidAssignmentNames6_24_2) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  typedef enum {LOW, HIGH} lvl_t;\n"
                                   "  lvl_t v;\n"
                                   "  initial begin\n"
                                   "    $cast(v, 1);\n"
                                   "    $cast(v, 9);\n"
                                   "  end\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment is invalid", 6,
                            "6.24.2"));
}

const char* const kInvalidCastInFunction =
    "module t;\n"
    "  typedef enum {RED, GREEN, BLUE} color_t;\n"
    "  color_t c;\n"
    "  function void f;\n"
    "    $cast(c, 10);\n"
    "  endfunction\n"
    "  initial begin\n"
    "    c = GREEN;\n"
    "    f();\n"
    "  end\n"
    "endmodule\n";

TEST(DynamicCastSim, TaskFormInvalidInFunctionBodyRaisesRuntimeError) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f, kInvalidCastInFunction);
  ASSERT_NE(design, nullptr);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$cast task could not assign",
                            5, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormInvalidInFunctionBodyNames6_24_2) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f, kInvalidCastInFunction);
  ASSERT_NE(design, nullptr);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$cast task could not assign",
                            5, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormInvalidInFunctionBodyLeavesDestUnchanged) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f, kInvalidCastInFunction);
  ASSERT_NE(design, nullptr);

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 1u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$cast task could not assign the source expression "
                            "to the destination; assignment is invalid",
                            5, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormInvalidInClassMethodRaisesRuntimeError) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  class C;\n"
                        "    function void bad();\n"
                        "      $cast(c, 10);\n"
                        "    endfunction\n"
                        "  endclass\n"
                        "  initial begin\n"
                        "    C obj;\n"
                        "    obj = new;\n"
                        "    obj.bad();\n"
                        "  end\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$cast task could not assign",
                            6, "6.24.2"));
}

TEST(DynamicCastSim, TaskFormValidInFunctionBodyRaisesNoError) {
  SimFixture f;
  auto* design =
      ElaborateLowerRun(f,
                        "module t;\n"
                        "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                        "  color_t c;\n"
                        "  function void f;\n"
                        "    $cast(c, 2);\n"
                        "  endfunction\n"
                        "  initial f();\n"
                        "endmodule\n");
  ASSERT_NE(design, nullptr);

  EXPECT_EQ(FindDiag(f, "$cast task could not assign"), nullptr);
}

}  // namespace
