#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §7.8.2: Write and read back with a string key.
TEST(StringIndexAssocArraySimulation, WriteAndRead) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(aa->str_data["hello"].ToUint64(), 42u);
}

// §7.8.2: Empty string "" is a valid index.
TEST(StringIndexAssocArraySimulation, EmptyStringIndex) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data[""] = MakeLogic4VecVal(f.arena, 32, 99);

  EXPECT_EQ(aa->str_data.count(""), 1u);
  EXPECT_EQ(aa->str_data[""].ToUint64(), 99u);
}

// §7.8.2: Ordering is lexicographical (lesser to greater).
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

// §7.8.2: Multiple string keys stored independently.
TEST(StringIndexAssocArraySimulation, MultipleKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["x"] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->str_data["y"] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->str_data["z"] = MakeLogic4VecVal(f.arena, 32, 30);

  EXPECT_EQ(aa->Size(), 3u);
  EXPECT_EQ(aa->str_data["x"].ToUint64(), 10u);
  EXPECT_EQ(aa->str_data["y"].ToUint64(), 20u);
  EXPECT_EQ(aa->str_data["z"].ToUint64(), 30u);
}

// §7.8.2: Overwriting an existing string key updates the value.
TEST(StringIndexAssocArraySimulation, OverwriteKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["key"] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->str_data["key"] = MakeLogic4VecVal(f.arena, 32, 200);

  EXPECT_EQ(aa->str_data["key"].ToUint64(), 200u);
}

// §7.8.2: End-to-end write and read with string-indexed array.
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

// §7.8.2: End-to-end multiple string keys.
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

// §7.8.2: End-to-end overwrite with string key.
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

}  // namespace
