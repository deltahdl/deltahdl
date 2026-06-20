#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates `src`, lowers it, and runs the scheduler. Returns the elaborated
// design (or nullptr on elaboration failure) so callers can assert on it.
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

// Builds the standard color_t-enum module whose `initial` block contains `body`
// (with `c` declared as color_t and `ok` as int), elaborates/lowers/runs it,
// then reads back `ok` and `c`. Asserts both variables exist.
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

// Builds the color_t-enum module with an int `flag` (initialized to 0) and `c`,
// whose `initial` block runs `body` after the `flag = 0;` init. Reads back
// `flag` and `c`. Asserts both variables exist.
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

  EXPECT_TRUE(f.diag.HasErrors());
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

// §6.24.2: casting between cast-compatible singular (integral) operands is a
// valid assignment, so the function form assigns the destination and returns 1.
// Exercises the success path for a non-enum destination.
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

// §6.24.2: the task form of a valid integral cast assigns the destination and,
// because the assignment is valid, raises no run-time error.
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

}  // namespace
