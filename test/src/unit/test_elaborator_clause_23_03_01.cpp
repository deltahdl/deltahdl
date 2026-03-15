// §23.3.1

#include "fixture_elaborator.h"

namespace {

TEST(TopLevelModules, EmptySourceTopNotFoundReturnsNull) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(BuildingBlockElaboration, ElaboratedDesignContainsTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(BuildingBlockElaboration, SelectSpecificTopFromMultipleModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "b");
}

TEST(TopLevelModules, NonexistentTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

TEST(TopLevelModules, UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
