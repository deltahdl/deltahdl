#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §33.2.1 (printed page 935): "The optional :config extension shall be used
// explicitly to refer to a config in the case where a config has the same name
// as a module/primitive", so a config and a module of one name are two cells
// of one library, told apart by the suffix, and neither is defined twice.
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

// The same with the config written first.
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

// Two configs of one name collide: §33.2 puts a config in the SystemVerilog
// name space, and no suffix tells two configs apart, so the second reuses a
// name already used there.
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
  // The second `config dup` is the later insertion, so the report stands at its
  // `config` keyword on line 5.
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

// §33.2: "the config is a design element, similar to a module, which exists in
// the SystemVerilog name space", and the :config extension §33.2.1 provides
// tells a config apart from a module or primitive only, so an interface of the
// config's name collides, and the report carries §33.2.
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

// The program form of the same collision, reported under the same §33.2.
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

// §33.2.1 names the primitive beside the module as the design element a
// config may share a name with.
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
// instance cannot be mapped and elaboration reports the failure. §33.2
// describes that walk and states no prohibition of its own, so the report is
// the one for an instantiation naming no module definition and carries
// §23.3.2, where module_instantiation and its module_identifier are defined.
TEST(ConfigInstanceSourceMapping, UnlocatableSubinstanceIsError) {
  ElabFixture f;
  ElaborateSrc("module top; missing u_missing(); endmodule\n", f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'missing'", 1,
                            "23.3.2"));
}

// §33.2: the descent continues into each located definition's own
// subinstances, so a definition that cannot be located deeper in the
// hierarchy still leaves an instance unmapped and is reported, by the same
// report and under the same §23.3.2.
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
