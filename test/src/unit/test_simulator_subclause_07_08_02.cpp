#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §7.8.2: the ordering of a string-indexed associative array is lexicographical
// (lesser to greater). Insert keys through real source syntax in a deliberately
// non-sorted order and confirm the production storage that the insertions build
// iterates them lexicographically.
TEST(StringIndexAssocArraySimulation, LexicographicOrdering) {
  RunAndExpectStringKeys(
      "module t;\n"
      "  int aa[string];\n"
      "  initial begin\n"
      "    aa[\"cherry\"] = 3;\n"
      "    aa[\"apple\"] = 1;\n"
      "    aa[\"banana\"] = 2;\n"
      "  end\n"
      "endmodule\n",
      "aa", {"apple", "banana", "cherry"});
}

// §7.8.2: lexicographic ordering edge cases, driven through the full pipeline.
// The empty string is the least key, and a prefix sorts before its extension
// ("a" before "ab"). Keys are inserted out of order via real source syntax.
TEST(StringIndexAssocArraySimulation, OrderingWithEmptyAndPrefixKeys) {
  RunAndExpectStringKeys(
      "module t;\n"
      "  int aa[string];\n"
      "  initial begin\n"
      "    aa[\"ab\"] = 2;\n"
      "    aa[\"b\"] = 3;\n"
      "    aa[\"\"] = 0;\n"
      "    aa[\"a\"] = 1;\n"
      "  end\n"
      "endmodule\n",
      "aa", {"", "a", "ab", "b"});
}

TEST(StringIndexAssocArraySimulation, EndToEndMultipleKeys) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"a\"] = 10;\n"
      "    aa[\"b\"] = 20;\n"
      "    aa[\"c\"] = 30;\n"
      "    result = aa[\"b\"];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 20u);
}

TEST(StringIndexAssocArraySimulation, EndToEndOverwrite) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 100;\n"
      "    aa[\"k\"] = 999;\n"
      "    result = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 999u);
}

// §7.8.2: a string-typed variable (§6.16) is a valid index. Drive a write and
// read keyed by a string variable through the full pipeline and confirm the
// stored value is retrieved by the same key.
TEST(StringIndexAssocArraySimulation, EndToEndStringVariableIndex) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = \"gamma\";\n"
      "    aa[s] = 42;\n"
      "    result = aa[s];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 42u);
}

// §7.8.2: the empty string is a valid index. Assign to and read back the ""
// key through the full lowering and evaluation path.
TEST(StringIndexAssocArraySimulation, EndToEndEmptyStringIndex) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"\"] = 7;\n"
      "    result = aa[\"\"];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 7u);
}

}  // namespace
