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
struct ElabA603Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA603Fixture &f) {
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
// A.6.3 Parallel and sequential blocks — Elaboration
// =============================================================================

// ---------------------------------------------------------------------------
// Elaboration: §13.4 fork restrictions inside functions
// ---------------------------------------------------------------------------

// §13.4.4: fork/join_none is permitted inside a function
TEST(ElabA603, ForkJoinNoneAllowedInFunction) {
  ElabA603Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  function void my_func();\n"
                              "    fork\n"
                              "      a = 1;\n"
                              "    join_none\n"
                              "  endfunction\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: fork/join is illegal inside a function
TEST(ElabA603, ForkJoinIllegalInFunction) {
  ElabA603Fixture f;
  ElaborateSrc("module m;\n"
               "  function void my_func();\n"
               "    fork\n"
               "      a = 1;\n"
               "    join\n"
               "  endfunction\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.4: fork/join_any is illegal inside a function
TEST(ElabA603, ForkJoinAnyIllegalInFunction) {
  ElabA603Fixture f;
  ElaborateSrc("module m;\n"
               "  function void my_func();\n"
               "    fork\n"
               "      a = 1;\n"
               "    join_any\n"
               "  endfunction\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.has_errors);
}
