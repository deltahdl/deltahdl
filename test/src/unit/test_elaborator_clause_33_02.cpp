#include "fixture_elaborator.h"

namespace {

// A config name and a module name in the same compilation unit collide.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModule) {
  EXPECT_FALSE(
      ElabOk("module foo; endmodule\n"
             "config foo;\n"
             "  design work.foo;\n"
             "endconfig\n"));
}

// Reverse declaration order — collision is order-independent.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModuleReverseOrder) {
  EXPECT_FALSE(
      ElabOk("config foo;\n"
             "  design work.foo;\n"
             "endconfig\n"
             "module foo; endmodule\n"));
}

// Two configs sharing a name in the same compilation unit collide.
TEST(ConfigDesignElementNameSpace, DuplicateConfigNames) {
  EXPECT_FALSE(
      ElabOk("module m; endmodule\n"
             "config dup;\n"
             "  design work.m;\n"
             "endconfig\n"
             "config dup;\n"
             "  design work.m;\n"
             "endconfig\n"));
}

// Distinct names — config and module coexist without conflict.
TEST(ConfigDesignElementNameSpace, DistinctConfigAndModuleOk) {
  EXPECT_TRUE(
      ElabOk("module m; endmodule\n"
             "config c;\n"
             "  design work.m;\n"
             "endconfig\n"));
}

// Config name shares the design-element space with interfaces too.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface bar; endinterface\n"
      "module top; endmodule\n"
      "config bar;\n"
      "  design work.top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Config name shares the design-element space with programs too.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithProgram) {
  ElabFixture f;
  ElaborateSrc(
      "program baz; endprogram\n"
      "module top; endmodule\n"
      "config baz;\n"
      "  design work.top;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
