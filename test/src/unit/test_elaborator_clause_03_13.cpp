#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// Returns true if elaboration of the last module in src succeeds with no
// errors.
static bool ElabOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  auto *cu = parser.Parse();
  if (diag.HasErrors() || cu->modules.empty()) return false;
  Elaborator elab(arena, diag, cu);
  elab.Elaborate(cu->modules.back()->name);
  return !diag.HasErrors();
}

// =============================================================================
// §3.13 Redeclaration rules (Elaboration)
// =============================================================================

// 34. Redeclaring a variable in the same module scope is an error.
TEST(ElabClause03, Cl3_13_RedeclVarInModuleScope) {
  // Two logic declarations with the same name 'x' in the same module.
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  logic x;\n"
             "endmodule\n"));
}

// 35. Redeclaring a net in the same module scope is an error.
TEST(ElabClause03, Cl3_13_RedeclNetInModuleScope) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  wire w;\n"
             "  wire w;\n"
             "endmodule\n"));
}

// 36. Distinct names in the same module scope are legal.
TEST(ElabClause03, Cl3_13_DistinctNamesInModuleScope) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  logic b;\n"
             "  wire c;\n"
             "endmodule\n"));
}

// 37. Same name in different modules is legal (separate name spaces).
TEST(ElabClause03, Cl3_13_SameNameDifferentModulesElab) {
  // Each module has its own module name space — 'data' in both is fine.
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>",
                         "module a; logic data; endmodule\n"
                         "module b; logic data; endmodule\n");
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  auto *cu = parser.Parse();
  ASSERT_FALSE(diag.HasErrors());
  // Elaborate both modules — neither should produce a redeclaration error.
  Elaborator elab_a(arena, diag, cu);
  elab_a.Elaborate("a");
  EXPECT_FALSE(diag.HasErrors());
  Elaborator elab_b(arena, diag, cu);
  elab_b.Elaborate("b");
  EXPECT_FALSE(diag.HasErrors());
}
