#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult310 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult310 Parse(const std::string& src) {
  ParseResult310 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM §3.10 — Configurations
// =============================================================================

// §3.10: "SystemVerilog provides the ability to specify design configurations,
//         which specify the binding information of module instances to specific
//         SystemVerilog source code. Configurations utilize libraries."
TEST(ParserClause03, Cl3_10_ConfigBindingAndLibraries) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "  instance top.u1 use lib2.fast_adder;\n"
      "  cell adder liblist lib1 lib2;\n"
      "endconfig : cfg1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
  // Design statement: binding to specific source (lib.cell notation)
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].first, "work");
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].second, "top");
  // Three rules: default, instance, cell — all configuration binding types
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 3u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(r.cu->configs[0]->rules[0]->liblist.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->liblist[0], "work");
  auto* r1 = r.cu->configs[0]->rules[1];
  EXPECT_EQ(r1->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(r1->inst_path, "top.u1");
  EXPECT_EQ(r1->use_lib, "lib2");
  EXPECT_EQ(r1->use_cell, "fast_adder");
  auto* r2 = r.cu->configs[0]->rules[2];
  EXPECT_EQ(r2->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(r2->cell_name, "adder");
  ASSERT_EQ(r2->liblist.size(), 2u);
}
