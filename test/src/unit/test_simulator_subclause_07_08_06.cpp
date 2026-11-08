#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

struct RunResult {
  bool ok = false;
  uint64_t value = 0;
  bool unknown = false;
  uint32_t warnings = 0;
};

RunResult RunObserving(const std::string& src, const char* var_name) {
  SimFixture f;
  RunResult r;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return r;
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return r;
  r.ok = true;
  r.value = var->value.ToUint64();
  r.unknown = HasUnknownBits(var->value);
  r.warnings = f.diag.WarningCount();
  return r;
}

TEST(AssocInvalidIndex, XzIndexRead2StateWarnsReturnsZero) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    idx = 'x;\n"
      "    result = aa[idx];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 0u);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, XzIndexRead4StateWarnsReturnsX) {
  auto r = RunObserving(
      "module t;\n"
      "  integer aa[integer];\n"
      "  integer idx;\n"
      "  integer result;\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    result = aa[idx];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_TRUE(r.unknown);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, MissingIntKeyRead2StateWarnsReturnsZero) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 42;\n"
      "    result = aa[999];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 0u);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, MissingIntKeyRead4StateWarnsReturnsX) {
  auto r = RunObserving(
      "module t;\n"
      "  integer aa[int];\n"
      "  integer result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_TRUE(r.unknown);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, MissingStringKeyReadWarnsReturnsZero) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"hello\"] = 10;\n"
      "    result = aa[\"missing\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 0u);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, PresentIntKeyReadReturnsValueNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[10] = 42;\n"
      "    result = aa[10];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 42u);
  EXPECT_EQ(r.warnings, 0u);
}

TEST(AssocInvalidIndex, PresentStringKeyReadReturnsValueNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"hello\"] = 10;\n"
      "    result = aa[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 10u);
  EXPECT_EQ(r.warnings, 0u);
}

TEST(AssocInvalidIndex, MissingIntKeyReadWithDefaultNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[int] = '{10:42, default:77};\n"
      "  int result;\n"
      "  initial result = aa[999];\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 77u);
  EXPECT_EQ(r.warnings, 0u);
}

TEST(AssocInvalidIndex, XzIndexReadWithDefaultNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[integer] = '{5:42, default:55};\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    result = aa[idx];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 55u);
  EXPECT_EQ(r.warnings, 0u);
}

TEST(AssocInvalidIndex, MissingStringKeyReadWithDefaultNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[string] = '{\"a\":10, default:88};\n"
      "  int result;\n"
      "  initial result = aa[\"missing\"];\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 88u);
  EXPECT_EQ(r.warnings, 0u);
}

TEST(AssocInvalidIndex, XzIndexWriteIgnoredWarns) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    aa[idx] = 99;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 0u);
  EXPECT_GE(r.warnings, 1u);
}

TEST(AssocInvalidIndex, XzIndexWriteDoesNotClobberExisting) {
  auto count = RunObserving(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    idx = 'x;\n"
      "    aa[idx] = 99;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(count.ok);
  EXPECT_EQ(count.value, 1u);
  EXPECT_GE(count.warnings, 1u);

  auto v = RunAndGet(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    idx = 'x;\n"
      "    aa[idx] = 99;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocInvalidIndex, XzIndexWriteFromFunctionBodyStoresNothing) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  function void store();\n"
      "    aa[idx] = 99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    store();\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 0u);
}

TEST(AssocInvalidIndex, ValidIndexWriteNotIgnoredNoWarning) {
  auto r = RunObserving(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 99;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  ASSERT_TRUE(r.ok);
  EXPECT_EQ(r.value, 99u);
  EXPECT_EQ(r.warnings, 0u);
}

void RunForDiags(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST(AssocInvalidIndex, MissingIndexReadWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aa[integer];\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "': read of non-existent index", 4, "7.8.6"));
}

TEST(AssocInvalidIndex, XzIndexReadWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    result = aa[idx];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "': index contains x/z", 7,
                              "7.8.6"));
}

TEST(AssocInvalidIndex, XzIndexWriteWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    aa[idx] = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "associative array index contains x/z", 6,
                              "7.8.6"));
}

TEST(AssocInvalidIndex, XzIndexWriteFromFunctionBodyWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  function void store();\n"
      "    aa[idx] = 99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    idx = 'x;\n"
      "    store();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "associative array index contains x/z", 5,
                              "7.8.6"));
}

TEST(AssocInvalidIndex, XzMethodIndexWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aa[integer];\n"
      "  integer idx;\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 8;\n"
      "    idx = 'x;\n"
      "    result = aa.exists(idx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "associative array index contains x/z", 8,
                              "7.8.6"));
}

TEST(AssocInvalidIndex, MissingElementQueueReadWarningNames7_8_6) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aq[string][$];\n"
      "  int af[int][2];\n"
      "  int n, v;\n"
      "  initial begin\n"
      "    n = aq[\"x\"].size();\n"
      "    v = af[9][1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "associative array 'aq': read of non-existent index", 6, "7.8.6"));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(),
      "associative array 'af': read of non-existent index", 7, "7.8.6"));
}

TEST(AssocInvalidIndex, QueueMethodStatementOnAMissingElementDoesNotWarn) {
  SimFixture f;
  RunForDiags(
      "module t;\n"
      "  int aq[string][$];\n"
      "  int n;\n"
      "  initial begin\n"
      "    aq[\"b\"].push_back(1);\n"
      "    aq[\"c\"].push_front(2);\n"
      "    n = aq[\"b\"][0] + aq[\"c\"][0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 3u);
}

TEST(AssocInvalidIndex, MissingEntryOfAStructureReadsMemberByMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; logic [3:0] b; int c = 5; } s_t;\n"
      "  s_t m[int];\n"
      "  s_t w[string];\n"
      "  s_t r, rw;\n"
      "  initial begin\n"
      "    m[1] = '{1, 4'h1, 2};\n"
      "    r = m[7];\n"
      "    rw = w[\"k\"];\n"
      "    $display(\"%0d %h %0d\", r.a, r.b, r.c);\n"
      "    $display(\"%0d %h %0d\", rw.a, rw.b, rw.c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 x 5\n0 x 5\n");
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "associative array 'm': read of non-existent index",
      8, "7.8.6"));
}

}  // namespace
