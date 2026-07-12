// Tests for IEEE 1800-2023 §7.8.6 -- accessing invalid indices of an
// associative array. Three runtime rules, all observed end-to-end (parse ->
// elaborate -> lower -> run) so the behavior reflects the production
// read/write paths rather than a hand-built AssocArrayObject:
//
//   R1  A read whose index is a 4-state expression carrying x/z, or a read of
//       a nonexistent entry, issues a warning and returns the nonexistent-entry
//       value for the array's element type (Table 7-1, §7.4.5): 0 for a 2-state
//       element, all-x for a 4-state element.
//   R2  When the array has a user-specified default (the §7.9.11 default:value
//       form), an invalid read issues NO warning and returns that default.
//   W1  A write through an invalid (x/z) index is ignored and issues a warning.
//
// The invalid index and the element-type default both depend on how the array
// is declared and how the index variable is produced, so every case is built
// from real declaration/initializer syntax. Only a 4-state type (e.g.
// `integer`) can carry x/z into an index, so the x/z cases route the unknown
// value through such a variable.

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Run real source through the full pipeline and expose the diagnostic engine so
// both a result variable and the warning count are observable in one run.
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

// --- R1(a): a read with an x/z index warns and returns the type default ------

// 2-state element: the x/z read yields 0 and raises a warning.
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

// 4-state element: the x/z read yields the all-x default and raises a warning.
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

// --- R1(b): a read of a nonexistent entry warns and returns the type default -

// Missing integer key, 2-state element: returns 0 and warns.
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

// Missing integer key, 4-state element: returns all-x and warns.
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

// Missing string key: returns 0 and warns.
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

// --- R1 negative: a valid read returns the stored value and does not warn
// -----

// The closest accepting input to R1: a present integer key reads back its value
// with no diagnostic.
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

// String-keyed accepting variant.
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

// --- R2: a user-specified default suppresses the warning (§7.9.11 value)
// ------

// Missing integer key with a declared default: returns the default, no warning.
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

// x/z index read with a declared default: the invalid-index warning is likewise
// suppressed and the default is returned. This is the §7.8.6-specific angle --
// the default silences the x/z path, not just the missing-entry path.
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

// String-keyed default-suppression variant.
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

// --- W1: a write through an invalid (x/z) index is ignored and warns ---------

// The x/z write stores nothing (num() stays 0) and raises a warning.
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

// An ignored x/z write leaves already-present entries untouched: the pre-seeded
// entry still reads back, the entry count stays 1, and a warning is raised.
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

// --- W1 negative: a valid write is not ignored -------------------------------

// The closest accepting input to W1: a write through a well-defined index is
// stored and reads back, with no diagnostic.
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

}  // namespace
