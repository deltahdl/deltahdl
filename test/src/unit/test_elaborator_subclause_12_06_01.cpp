#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemElaboration, CaseMatchesItemElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CaseMatchesItemElaboration, CaseMatchesGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'b1;\n"
      "    case(x) matches\n"
      "      8'd5 &&& guard: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CaseMatchesItemElaboration, RealSelectorWithIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    case(r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorWithGuardedIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    case(r) matches\n"
      "      8'd5 &&& en: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 8,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok)\n"
      "    case (r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else\n"
      "    case (r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration, RealSelectorInARandcaseItemIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial randcase\n"
      "    1:\n"
      "      case (r) matches\n"
      "        8'd5: y = 8'd10;\n"
      "      endcase\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 6,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : {\n"
      "        case (r) matches\n"
      "          8'd5: y = 8'd10;\n"
      "        endcase\n"
      "      };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 7,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration,
     RealSelectorInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 {\n"
      "        case (r) matches\n"
      "          8'd5: y = 8'd10;\n"
      "        endcase\n"
      "      };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs", 8,
                            "12.6.1"));
}

TEST(CaseMatchesItemElaboration, PatternIdentifierOfAnotherItemIsUnresolved) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int y;\n"
      "  initial case (v) matches\n"
      "    tagged Valid .a : y = a;\n"
      "    tagged Invalid : y = a;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'a'", 6,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
