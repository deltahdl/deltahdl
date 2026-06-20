#include "fixture_elaborator.h"

namespace {

TEST(ConfigDefaultClause, DuplicateDefaultLiblistRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "  default liblist other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(ConfigDefaultClause, SingleDefaultLiblistAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

// §33.4.1.2: the default clause selects every instance that no more-specific
// selection clause matches. Here `top` instantiates two like-named `leaf`
// cells; an instance clause names a library list for `top.b`, while a default
// liblist governs the rest. The default must reach `top.a` (unmatched by the
// instance clause). Returns the cell bound to the named child of the elaborated
// config, or nullptr.
RtlirModule* BindChildUnderTop(ElabFixture& f, const std::string& config_body,
                               std::string_view child_inst) {
  std::string src;
  src += "module leaf; endmodule\n";
  src += "module leaf; endmodule\n";
  src += "module top; leaf a(); leaf b(); endmodule\n";
  src += config_body;
  auto fid = f.mgr.AddFile("<test>", std::move(src));
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = "libA";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "libC";
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  for (const auto& inst : design->top_modules[0]->children) {
    if (inst.inst_name == child_inst) return inst.resolved;
  }
  return nullptr;
}

// The instance that no more-specific clause matches (`top.a`) is bound by the
// default liblist (libA).
TEST(ConfigDefaultClause, DefaultSelectsInstanceWithoutSpecificClause) {
  ElabFixture f;
  auto* bound = BindChildUnderTop(f,
                                  "config c;\n"
                                  "  design top;\n"
                                  "  default liblist libA;\n"
                                  "  instance top.b liblist libB;\n"
                                  "endconfig\n",
                                  "a");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libA");
}

// The instance a more-specific clause matches (`top.b`) is bound by that
// clause (libB), not by the default, confirming the default yields to it.
TEST(ConfigDefaultClause, MoreSpecificClauseOverridesDefault) {
  ElabFixture f;
  auto* bound = BindChildUnderTop(f,
                                  "config c;\n"
                                  "  design top;\n"
                                  "  default liblist libA;\n"
                                  "  instance top.b liblist libB;\n"
                                  "endconfig\n",
                                  "b");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

// §33.4.1.2: with no more-specific selection clause present, the default
// selects every instance. Both `top.a` and `top.b` fall to the default
// liblist (libA), exercising the "selects all instances" reach of the rule.
TEST(ConfigDefaultClause, DefaultGovernsEveryInstanceAbsentSpecificClause) {
  const char* cfg =
      "config c;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "endconfig\n";
  ElabFixture fa;
  auto* a = BindChildUnderTop(fa, cfg, "a");
  ElabFixture fb;
  auto* b = BindChildUnderTop(fb, cfg, "b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->library, "libA");
  EXPECT_EQ(b->library, "libA");
}

// §33.4.1.2: a cell selection clause is "more specific" than the default, so
// the default does not select the cell it names. `top` instantiates a `leaf`
// (named by a cell clause) and a `mid` (named by nothing). The cell clause
// binds `leaf` to libB while the default reaches `mid`, binding it to libA.
TEST(ConfigDefaultClause, CellClauseOverridesDefaultForNamedCellOnly) {
  ElabFixture f;
  std::string src;
  src += "module leaf; endmodule\n";
  src += "module leaf; endmodule\n";
  src += "module mid; endmodule\n";
  src += "module mid; endmodule\n";
  src += "module top; leaf x(); mid y(); endmodule\n";
  src +=
      "config c;\n"
      "  design top;\n"
      "  default liblist libA;\n"
      "  cell leaf liblist libB;\n"
      "endconfig\n";
  auto fid = f.mgr.AddFile("<test>", std::move(src));
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->modules[0]->library = "libA";  // leaf
  cu->modules[1]->library = "libB";  // leaf
  cu->modules[2]->library = "libA";  // mid
  cu->modules[3]->library = "libB";  // mid
  cu->modules[4]->library = "libC";  // top
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  RtlirModule* leaf_bound = nullptr;
  RtlirModule* mid_bound = nullptr;
  for (const auto& inst : design->top_modules[0]->children) {
    if (inst.inst_name == "x") leaf_bound = inst.resolved;
    if (inst.inst_name == "y") mid_bound = inst.resolved;
  }
  ASSERT_NE(leaf_bound, nullptr);
  ASSERT_NE(mid_bound, nullptr);
  EXPECT_EQ(leaf_bound->library, "libB");
  EXPECT_EQ(mid_bound->library, "libA");
}

}  // namespace
