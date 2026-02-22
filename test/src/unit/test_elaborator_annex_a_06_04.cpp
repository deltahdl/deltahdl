#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

// Elab test fixture
struct ElabA604Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA604Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

} // namespace

// =============================================================================
// A.6.4 Statements — Elaboration
// =============================================================================

// ---------------------------------------------------------------------------
// Elaboration: function_statement context restrictions
// ---------------------------------------------------------------------------

// §13.4.4: return with value in void function is an error
TEST(ElabA604, VoidFunctionReturnWithValueError) {
  ElabA604Fixture f;
  ElaborateSrc("module m;\n"
               "  function void f();\n"
               "    return 42;\n"
               "  endfunction\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4: non-void function can return a value
TEST(ElabA604, NonVoidFunctionReturnWithValue) {
  ElabA604Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  function int f();\n"
                              "    return 42;\n"
                              "  endfunction\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
