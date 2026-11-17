#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(QueueCallArguments, QInitializeWithItsFullListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_initialize(1, 1, 4, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(QueueCallArguments, DISABLED_QInitializeWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_initialize(1, 1, 4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_initialize takes exactly 4 arguments", 4,
                            "20.15.1"));
}

TEST(QueueCallArguments, DISABLED_QInitializeWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_initialize(1, 1, 4, st, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_initialize takes exactly 4 arguments", 4,
                            "20.15.1"));
}

TEST(QueueCallArguments, DISABLED_QInitializeAsAnExpressionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_initialize(1, 1, 4, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_initialize is a system task and cannot be used as an expression", 4,
      "20.15.1"));
}

TEST(QueueCallArguments, DISABLED_QInitializeAsAConditionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    if ($q_initialize(1, 1, 4, st)) r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_initialize is a system task and cannot be used as an expression", 4,
      "20.15.1"));
}

TEST(QueueCallOutputs, DISABLED_QInitializeConstantStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_initialize(1, 1, 4, 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the status argument of $q_initialize shall be a variable",
                    4, "20.15.1"));
}

TEST(QueueCallOutputs, DISABLED_QInitializeExpressionStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_initialize(1, 1, 4, v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the status argument of $q_initialize shall be a variable",
                    4, "20.15.1"));
}

TEST(QueueCallArguments, QAddWithItsFullListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_add(1, 1, 0, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(QueueCallArguments, DISABLED_QAddWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_add(1, 1, 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_add takes exactly 4 arguments", 4, "20.15.2"));
}

TEST(QueueCallArguments, DISABLED_QAddWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_add(1, 1, 0, st, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_add takes exactly 4 arguments", 4, "20.15.2"));
}

TEST(QueueCallArguments, DISABLED_QAddAsAnExpressionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_add(1, 1, 0, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_add is a system task and cannot be used as an expression", 4,
      "20.15.2"));
}

TEST(QueueCallArguments, DISABLED_QAddAsAConditionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    if ($q_add(1, 1, 0, st)) r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_add is a system task and cannot be used as an expression", 4,
      "20.15.2"));
}

TEST(QueueCallOutputs, DISABLED_QAddConstantStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_add(1, 1, 0, 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the status argument of $q_add shall be a variable",
                            4, "20.15.2"));
}

TEST(QueueCallOutputs, DISABLED_QAddExpressionStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_add(1, 1, 0, v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the status argument of $q_add shall be a variable",
                            4, "20.15.2"));
}

TEST(QueueCallArguments, QRemoveWithItsFullListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, inf, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(QueueCallArguments, DISABLED_QRemoveWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, inf);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_remove takes exactly 4 arguments", 4,
                            "20.15.3"));
}

TEST(QueueCallArguments, DISABLED_QRemoveWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, inf, st, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_remove takes exactly 4 arguments", 4,
                            "20.15.3"));
}

TEST(QueueCallArguments, DISABLED_QRemoveAsAnExpressionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_remove(1, job, inf, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_remove is a system task and cannot be used as an expression", 4,
      "20.15.3"));
}

TEST(QueueCallArguments, DISABLED_QRemoveAsAConditionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    if ($q_remove(1, job, inf, st)) r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_remove is a system task and cannot be used as an expression", 4,
      "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveConstantJobIdIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, 7, inf, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the job_id argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveExpressionJobIdIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, v + 1, inf, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the job_id argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveConstantInformIdIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, 7, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the inform_id argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveExpressionInformIdIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, v + 1, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the inform_id argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveConstantStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, inf, 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallOutputs, DISABLED_QRemoveExpressionStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_remove(1, job, inf, v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_remove shall be a variable", 4, "20.15.3"));
}

TEST(QueueCallArguments, QFullWithItsFullListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_full(1, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(QueueCallArguments, DISABLED_QFullWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_full(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_full takes exactly 2 arguments", 4, "20.15.4"));
}

TEST(QueueCallArguments, DISABLED_QFullWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_full(1, st, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_full takes exactly 2 arguments", 4, "20.15.4"));
}

TEST(QueueCallOutputs, DISABLED_QFullConstantStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_full(1, 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_full shall be a variable", 4, "20.15.4"));
}

TEST(QueueCallOutputs, DISABLED_QFullExpressionStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_full(1, v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_full shall be a variable", 4, "20.15.4"));
}

TEST(QueueCallArguments, QExamWithItsFullListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(QueueCallArguments, DISABLED_QExamWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_exam takes exactly 4 arguments", 4, "20.15.5"));
}

TEST(QueueCallArguments, DISABLED_QExamWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v, st, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$q_exam takes exactly 4 arguments", 4, "20.15.5"));
}

TEST(QueueCallArguments, DISABLED_QExamAsAnExpressionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    r = $q_exam(1, 1, v, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_exam is a system task and cannot be used as an expression", 4,
      "20.15.5"));
}

TEST(QueueCallArguments, DISABLED_QExamAsAConditionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    if ($q_exam(1, 1, v, st)) r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$q_exam is a system task and cannot be used as an expression", 4,
      "20.15.5"));
}

TEST(QueueCallOutputs, DISABLED_QExamConstantQStatValueIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, 7, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the q_stat_value argument of $q_exam shall be a variable",
                    4, "20.15.5"));
}

TEST(QueueCallOutputs, DISABLED_QExamExpressionQStatValueIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v + 1, st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the q_stat_value argument of $q_exam shall be a variable",
                    4, "20.15.5"));
}

TEST(QueueCallOutputs, DISABLED_QExamConstantStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v, 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_exam shall be a variable", 4, "20.15.5"));
}

TEST(QueueCallOutputs, DISABLED_QExamExpressionStatusIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    $q_exam(1, 1, v, v + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the status argument of $q_exam shall be a variable", 4, "20.15.5"));
}

TEST(QueueCallArguments, QFullAsAConditionIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer st, job, inf, v, r;\n"
      "  initial begin\n"
      "    if ($q_full(1, st)) r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
