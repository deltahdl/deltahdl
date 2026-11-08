#include <gtest/gtest.h>

#include <utility>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' has 2 default clauses; at most one is "
                            "allowed",
                            5, "33.4.1.2"));
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
  for (auto* cfg : cu->configs) cfg->library = "libC";
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->configs[0]);
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  for (const auto& inst : design->top_modules[0]->children) {
    if (inst.inst_name == child_inst) return inst.resolved;
  }
  return nullptr;
}

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
  cu->modules[0]->library = "libA";
  cu->modules[1]->library = "libB";
  cu->modules[2]->library = "libA";
  cu->modules[3]->library = "libB";
  cu->modules[4]->library = "libC";
  for (auto* cfg : cu->configs) cfg->library = "libC";
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

TEST(ConfigDefaultClause, DuplicateDefaultLiblistNames33_4_1_2) {
  ElabFixture f;
  ElaborateSrc(
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  default liblist work;\n"
      "  default liblist other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "default clauses", 5, "33.4.1.2"));
}

}  // namespace
