// Tests for the §23.9 scope rules as they reach the name randomize, which no
// declaration gives a module. A.8.2 writes the scope randomize function of
// §18.12 as `[ std:: ] randomize` with its argument list optional, so a bare
// randomize read where no class method makes it the class's own method is
// that call, and resolves.
//
// A bare randomize read inside a class method is in
// test_elaborator_subclause_23_09f.cpp.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §23.9 with A.8.2 and §18.12: a bare randomize read in a module's function
// and in its initial block is the scope randomize call and draws no report,
// where a name beside it that nothing declares still does.
TEST(ScopeRandomizeName, ABareRandomizeReadResolvesAsTheScopeCall) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int ok;\n"
      "  function int f; return randomize; endfunction\n"
      "  initial begin\n"
      "    ok = randomize;\n"
      "    ok = randomize + nosuch;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 6,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
