#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(Elaboration, EnumRangeNMEqualBoundsSingle) {
  // Boundary of the name[N:M] form where N == M: neither incrementing nor
  // decrementing, so exactly one constant nameN is generated. This exercises a
  // distinct expansion path from the incrementing/decrementing cases.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3:3]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 1u);
  EXPECT_EQ(it->second[0].name, "sub3");
  EXPECT_EQ(it->second[0].value, 0);
}

TEST(Elaboration, EnumRangeNWithValueOnRangedMember) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[3] = 20} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 20);
  EXPECT_EQ(it->second[1].name, "sub1");
  EXPECT_EQ(it->second[1].value, 21);
  EXPECT_EQ(it->second[2].name, "sub2");
  EXPECT_EQ(it->second[2].value, 22);
}

TEST(Elaboration, EnumRangeNZeroIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[0]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumRangeNMNegativeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[-1:2]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumRangeNOneProducesSingle) {
  // Boundary of the positive-N rule: N == 1 is the smallest legal count and
  // yields exactly one generated constant, name0.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[1]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 1u);
  EXPECT_EQ(it->second[0].name, "sub0");
  EXPECT_EQ(it->second[0].value, 0);
}

TEST(Elaboration, EnumRangeNMZeroBoundsAllowed) {
  // Zero is a legal bound for the name[N:M] form, since both bounds need only
  // be non-negative. The label uses `register` (not `reg`, a reserved keyword)
  // matching the §6.19 example name[N:M] form.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[0:2]} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 3u);
  EXPECT_EQ(it->second[0].name, "register0");
  EXPECT_EQ(it->second[0].value, 0);
  EXPECT_EQ(it->second[1].name, "register1");
  EXPECT_EQ(it->second[1].value, 1);
  EXPECT_EQ(it->second[2].name, "register2");
  EXPECT_EQ(it->second[2].value, 2);
}

TEST(Elaboration, EnumRangeNMNegativeEndIsError) {
  // A negative upper bound violates the non-negative requirement on the second
  // bound of name[N:M].
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef enum {sub[2:-1]} E1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumRangeSecondLrmExample) {
  // The second worked example of §6.19.2: two ranged members, each with its own
  // value. The name[N]=C form seeds the first generated constant with C and
  // increments; a following name[N:M]=C form must RESET the running value to
  // its own C rather than continue from the previous member's last value.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {register[2] = 1, register[2:4] = 10} E1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  auto it = mod->enum_types.find("E1");
  ASSERT_NE(it, mod->enum_types.end());
  ASSERT_EQ(it->second.size(), 5u);
  EXPECT_EQ(it->second[0].name, "register0");
  EXPECT_EQ(it->second[0].value, 1);
  EXPECT_EQ(it->second[1].name, "register1");
  EXPECT_EQ(it->second[1].value, 2);
  EXPECT_EQ(it->second[2].name, "register2");
  EXPECT_EQ(it->second[2].value, 10);
  EXPECT_EQ(it->second[3].name, "register3");
  EXPECT_EQ(it->second[3].value, 11);
  EXPECT_EQ(it->second[4].name, "register4");
  EXPECT_EQ(it->second[4].value, 12);
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
