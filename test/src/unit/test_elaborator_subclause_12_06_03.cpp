#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TernaryMatchesElaboration, TernaryMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = x matches 8'd5 ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6.3 gives a pattern identifier of a conditional expression's predicate
// the later clauses and e2 as its scope, so e3 reading the name reads no
// declaration and is §23.9's unresolved reference.
TEST(TernaryMatchesElaboration,
     PatternIdentifierReadInTheThirdOperandIsUnresolved) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int y;\n"
      "  initial y = v matches tagged Valid .k ? k : k;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'k'", 4,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
