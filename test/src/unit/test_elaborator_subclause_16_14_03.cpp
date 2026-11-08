#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kDecls =
    "module m;\n"
    "  logic clk, a, b;\n";

TEST(CoverPassStatement, OrdinaryPassStatementIsAccepted) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) $display(\"hit\");\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(CoverPassStatement, RejectsConcurrentAssertPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssumePassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    assume property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentCoverPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    cover property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertNestedInBlock) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) begin\n"
                   "    assert property (@(posedge clk) b);\n"
                   "  end\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertNestedInIfThen) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    if (a) assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertNestedInIfElse) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    if (a) $display(\"x\");\n"
                   "    else assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertNestedInForLoop) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    for (int i = 0; i < 2; i = i + 1)\n"
                   "      assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertNestedInFork) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    fork assert property (@(posedge clk) b); join\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, AllowsImmediateAssertPassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a) assert (b);\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(CoverPassStatement, RejectsConcurrentAssertInCoverSequencePassStatement) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover sequence (@(posedge clk) a ##1 b)\n"
                   "    assert property (@(posedge clk) b);\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, CoverSequenceOrdinaryPassStatementIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      std::string(kDecls) +
          "  cover sequence (@(posedge clk) a ##1 b) $display(\"m\");\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(CoverPassStatement, RejectsConcurrentAssertInRandcaseArm) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    randcase\n"
                   "      1: assert property (@(posedge clk) b);\n"
                   "    endcase\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

TEST(CoverPassStatement, RejectsConcurrentAssertInRandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(std::string(kDecls) +
                   "  cover property (@(posedge clk) a)\n"
                   "    randsequence (main)\n"
                   "      main : { assert property (@(posedge clk) b); };\n"
                   "    endsequence\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concurrent assert, assume, or cover statement", 3,
                            "16.14.3"));
}

}  // namespace
