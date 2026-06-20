#include "fixture_elaborator.h"

namespace {

TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModule) {
  EXPECT_FALSE(
      ElabOk("module foo; endmodule\n"
             "config foo;\n"
             "  design work.foo;\n"
             "endconfig\n"));
}

TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModuleReverseOrder) {
  EXPECT_FALSE(
      ElabOk("config foo;\n"
             "  design work.foo;\n"
             "endconfig\n"
             "module foo; endmodule\n"));
}

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// §33.2: a config shares the SystemVerilog design-element name space with
// every design element kind, primitives included, so a config name reused by
// a primitive is a collision.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithPrimitive) {
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
  EXPECT_TRUE(f.has_errors);
}

// §33.2: a design description starts at a top-level module and the source
// descriptions for the module definitions of its subinstances are located,
// recursively, until every instance in the design is mapped to a source
// description. The recursive descent walks top -> child -> grandchild and
// every instance binds to the module definition that supplies its source.
TEST(ConfigInstanceSourceMapping, EveryInstanceMappedToSourceDescription) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid; leaf u_leaf(); endmodule\n"
      "module top; mid u_mid(); endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  // Each subinstance located the source description of its module definition.
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules.front();
  ASSERT_EQ(top->children.size(), 1u);
  auto* mid = top->children.front().resolved;
  ASSERT_NE(mid, nullptr);
  ASSERT_EQ(mid->children.size(), 1u);
  auto* leaf = mid->children.front().resolved;
  ASSERT_NE(leaf, nullptr);

  // Every module definition reached by the walk is mapped in the design.
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

// §33.2: when a subinstance has no source description to be located, the
// instance cannot be mapped and elaboration reports the failure.
TEST(ConfigInstanceSourceMapping, UnlocatableSubinstanceIsError) {
  ElabFixture f;
  ElaborateSrc("module top; missing u_missing(); endmodule\n", f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §33.2: the descent continues into each located definition's own
// subinstances, so a definition that cannot be located deeper in the
// hierarchy still leaves an instance unmapped and is reported.
TEST(ConfigInstanceSourceMapping, UnlocatableNestedSubinstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module mid; ghost u_ghost(); endmodule\n"
      "module top; mid u_mid(); endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
