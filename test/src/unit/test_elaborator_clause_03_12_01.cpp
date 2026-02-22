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
// LRM §3.12.1 — Compilation units (Elaboration)
// =============================================================================

// 14. Elaboration: CU-scope function at top level, module elaborates ok.
TEST(ElabClause03, Cl3_12_1_ElabModuleWithCuFunction) {
  // The CU has a top-level function and a module.
  // Elaboration of the module should succeed.
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}
