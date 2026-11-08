#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

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
