#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §33.2: "the config is a design element, similar to a module, which exists in
// the SystemVerilog name space." §3.13(a) forbids reusing a name in the
// definitions name space but enumerates only the module, primitive, program and
// interface, so a collision that involves a config rests on §33.2 and the
// report carries §33.2.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModule) {
  ElabFixture f;
  ElabOk(
      "module foo; endmodule\n"
      "config foo;\n"
      "  design work.foo;\n"
      "endconfig\n",
      f);
  // The config loop in ValidateNameSpaceDefinitions runs after the module loop,
  // so the config is the later insertion and the report stands at the `config`
  // keyword on line 2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'foo'", 2, "33.2"));
}

// The same collision with the config written first. §33.2 makes the config a
// design element in the name space whichever order the two are written in, so
// the report is the same one and carries the same §33.2.
TEST(ConfigDesignElementNameSpace, ConfigCollidesWithModuleReverseOrder) {
  ElabFixture f;
  ElabOk(
      "config foo;\n"
      "  design work.foo;\n"
      "endconfig\n"
      "module foo; endmodule\n",
      f);
  // The config loop still runs last, so the report stands at the `config`
  // keyword on line 1 even though the module is written after it.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'foo'", 1, "33.2"));
}

// Two configs of one name collide for the same §33.2 reason: both occupy the
// SystemVerilog name space, so the second reuses a name already used there.
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

// The name space §33.2 puts the config into is the one §3.13(a) unifies across
// design element kinds, so an interface of the config's name collides too, and
// the report carries §33.2.
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

// §33.2: a config shares the SystemVerilog design-element name space with
// every design element kind, primitives included, so a config name reused by
// a primitive is a collision, reported under the same §33.2.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate definition of 'qux'", 5, "33.2"));
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
