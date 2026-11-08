#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(ConfigDesignElementNameSpace, ConfigSharesAModulesName) {
  ElabFixture f;
  ElabOk(
      "module foo; endmodule\n"
      "config foo;\n"
      "  design work.foo;\n"
      "endconfig\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigDesignElementNameSpace, ConfigSharesAModulesNameWrittenFirst) {
  ElabFixture f;
  ElabOk(
      "config foo;\n"
      "  design work.foo;\n"
      "endconfig\n"
      "module foo; endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigDesignElementNameSpace, DuplicateConfigNames) {
  ElabFixture f;
  ElabOk(
      "module m; endmodule\n"
      "config dup;\n"
      "  design work.m;\n"
      "endconfig\n"
      "config dup;\n"
      "  design work.m;\n"
      "endconfig\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'dup'", 5, "33.2"));
}

TEST(ConfigDesignElementNameSpace, DistinctConfigAndModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "config c;\n"
             "  design work.m;\n"
             "endconfig\n"));
}

TEST(ConfigDesignElementNameSpace, ConfigCollidesWithInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface bar; endinterface\n"
      "module top; endmodule\n"
      "config bar;\n"
      "  design work.top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'bar'", 3, "33.2"));
}

TEST(ConfigDesignElementNameSpace, ConfigCollidesWithProgram) {
  ElabFixture f;
  ElaborateSrc(
      "program baz; endprogram\n"
      "module top; endmodule\n"
      "config baz;\n"
      "  design work.top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'baz'", 3, "33.2"));
}

TEST(ConfigDesignElementNameSpace, ConfigSharesAPrimitivesName) {
  ElabFixture f;
  ElaborateSrc(
      "primitive qux(output y, input a);\n"
      "  table 0 : 1 ; 1 : 0 ; endtable\n"
      "endprimitive\n"
      "module top; endmodule\n"
      "config qux;\n"
      "  design work.top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigInstanceSourceMapping, EveryInstanceMappedToSourceDescription) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid; leaf u_leaf(); endmodule\n"
      "module top; mid u_mid(); endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules.front();
  ASSERT_EQ(top->children.size(), 1u);
  auto* mid = top->children.front().resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->children.size(), 1u);
  auto* leaf = mid->children.front().resolved;
  ASSERT_NE(leaf, nullptr);

  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(ConfigInstanceSourceMapping, UnlocatableSubinstanceIsError) {
  ElabFixture f;
  ElaborateSrc("module top; missing u_missing(); endmodule\n", f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'missing'", 1,
                            "23.3.2"));
}

TEST(ConfigInstanceSourceMapping, UnlocatableNestedSubinstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module mid; ghost u_ghost(); endmodule\n"
      "module top; mid u_mid(); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'ghost'", 1,
                            "23.3.2"));
}

}  // namespace
