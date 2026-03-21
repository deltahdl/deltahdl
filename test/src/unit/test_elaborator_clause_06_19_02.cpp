#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.19.2 Enumerated type ranges

TEST(Elaboration, EnumRangeNExpandsNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "sub1");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "sub2");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNWithValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {add=10, sub[3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 4u);
  EXPECT_EQ(it->second[0].name, "add");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "sub0");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[2].name, "sub1");
  EXPECT_EQ(it->second[2].value, 12);
  EXPECT_EQ(it->second[3].name, "sub2");
  EXPECT_EQ(it->second[3].value, 13);
}

TEST(Elaboration, EnumRangeNMExpandsNames) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {jmp[6:8]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "jmp6");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "jmp7");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "jmp8");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNMWithValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[2:4] = 10} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "register2");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "register3");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[2].name, "register4");
  EXPECT_EQ(it->second[2].value, 12);
}

TEST(Elaboration, EnumRangeNMDecrementing) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {cnt[5:3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "cnt5");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "cnt4");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "cnt3");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeLrmExample) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {add=10, sub[5], jmp[6:8]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 9u);
  EXPECT_EQ(it->second[0].name, "add");
  EXPECT_EQ(it->second[0].value, 10);
  EXPECT_EQ(it->second[1].name, "sub0");
  EXPECT_EQ(it->second[1].value, 11);
  EXPECT_EQ(it->second[5].name, "sub4");
  EXPECT_EQ(it->second[5].value, 15);
  EXPECT_EQ(it->second[6].name, "jmp6");
  EXPECT_EQ(it->second[6].value, 16);
  EXPECT_EQ(it->second[8].name, "jmp8");
  EXPECT_EQ(it->second[8].value, 18);
}

}  // namespace
