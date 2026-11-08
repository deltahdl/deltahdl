#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PureDpiImportRestrictions, PureFunctionAcceptedWhenWellFormed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(input int a, input int b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsVoidReturnType) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function void p(input int a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function must have a non-void "
                            "return type",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsOutputArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(output int o);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsInoutArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureCannotApplyToImportedTask) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionWithNoArgumentsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsLateOutputArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(input int x, output int o);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureTaskNames35_5_2) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureTaskMessageDropsTheProseSubclause) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  ASSERT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("§"), std::string::npos);
  }
}

TEST(PureDpiImportRestrictions, NonPureFunctionUnrestrictedShapeAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" function void f(output int o, inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
