#include <gtest/gtest.h>

#include <cstddef>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ParallelBlockElaboration, ForkJoinInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkJoinAnyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkJoinNoneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, EmptyForkJoinElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ReturnInForkJoinErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement is not allowed inside a fork-join block", 4, "9.3.2"));
}

TEST(ParallelBlockElaboration, ReturnNestedInForkErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      begin\n"
      "        return;\n"
      "      end\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement is not allowed inside a fork-join block", 5, "9.3.2"));
}

TEST(ParallelBlockElaboration, ForkWithLocalparamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    fork\n"
      "      localparam int N = 4;\n"
      "      a = N;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin\n"
      "    fork\n"
      "      parameter int W = 8;\n"
      "      a = W;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithBeginEndElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 1;\n"
      "        b = 0;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefArgInForkJoinAnyIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration, RefArgInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration, RefArgInPlainForkJoinAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefStaticArgInForkJoinAnyAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref static int v);\n"
      "    fork\n"
      "      v = 1;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, RefArgInForkJoinAnyBlockItemInitAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      automatic int copy = v;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration,
     RefArgInARandsequenceCodeBlockInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : { v = 1; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            5, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     RefArgInARandsequenceWeightCodeBlockInForkJoinNoneIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : a := 5 { v = 1; };\n"
      "        a : { ; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            5, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ForkJoinNoneInAnAssertionPassStmtRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    assert (1) fork v = 1; join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            3, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ForkJoinNoneInAnAssertionFailStmtRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    assert (1) else fork v = 1; join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            3, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ForkJoinNoneInARandsequenceCodeBlockRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    randsequence(main)\n"
      "      main : { fork v = 1; join_none };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ForkJoinNoneInARandsequenceWeightCodeBlockRejectsARefArg) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(ref int v);\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { fork v = 1; join_none };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 'v' cannot be used inside a "
                            "fork-join_any or fork-join_none block",
                            4, "9.3.2"));
}

TEST(ParallelBlockElaboration,
     ReturnInARandsequenceCodeBlockInAForkIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : { return; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration,
     ReturnInARandsequenceWeightCodeBlockInAForkIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      randsequence(main)\n"
      "        main : alt := 5 { return; };\n"
      "        alt : { ; };\n"
      "      endsequence\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration,
     ReturnInAForkInARandsequenceCodeBlockIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randsequence(main)\n"
      "      main : { fork return; join_none };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

size_t CountReports(const ElabFixture& f, std::string_view needle) {
  size_t n = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.subclause == "9.3.2" && d.message.find(needle) != std::string::npos) {
      ++n;
    }
  }
  return n;
}

TEST(ParallelBlockElaboration, ReturnInNestedForksIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    fork\n"
      "      fork\n"
      "        return;\n"
      "      join\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountReports(f,
                         "return statement is not allowed inside a "
                         "fork-join block"),
            1u);
}

TEST(ParallelBlockElaboration, RefArgInNestedForkJoinNoneIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(ref int v);\n"
      "    fork\n"
      "      fork\n"
      "        v = 1;\n"
      "      join_none\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_EQ(CountReports(f,
                         "ref argument 'v' cannot be used inside a "
                         "fork-join_any or fork-join_none block"),
            1u);
}

}  // namespace
