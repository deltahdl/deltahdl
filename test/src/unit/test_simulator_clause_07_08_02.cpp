#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StringIndexAssocArraySimulation, EmptyStringIndex) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data[""] = MakeLogic4VecVal(f.arena, 32, 99);

  EXPECT_EQ(aa->str_data.count(""), 1u);
  EXPECT_EQ(aa->str_data[""].ToUint64(), 99u);
}

TEST(StringIndexAssocArraySimulation, LexicographicOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);

  auto it = aa->str_data.begin();
  EXPECT_EQ(it->first, "apple");
  ++it;
  EXPECT_EQ(it->first, "banana");
  ++it;
  EXPECT_EQ(it->first, "cherry");
}

// §7.8.2: lexicographic ordering edge cases. The empty string is the least
// key, and a prefix sorts before its extension ("a" before "ab").
TEST(StringIndexAssocArraySimulation, OrderingWithEmptyAndPrefixKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["ab"] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->str_data[""] = MakeLogic4VecVal(f.arena, 32, 0);
  aa->str_data["b"] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->str_data["a"] = MakeLogic4VecVal(f.arena, 32, 1);

  auto it = aa->str_data.begin();
  EXPECT_EQ(it->first, "");
  ++it;
  EXPECT_EQ(it->first, "a");
  ++it;
  EXPECT_EQ(it->first, "ab");
  ++it;
  EXPECT_EQ(it->first, "b");
}

TEST(StringIndexAssocArraySimulation, EndToEndWriteRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"hello\"] = 55;\n"
      "    result = aa[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 55u);
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
