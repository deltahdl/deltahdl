#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §35.5.2: only nonvoid functions with no output or inout arguments may be
// specified pure. The elaborator enforces these static restrictions and
// surfaces a diagnostic when they are violated.

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
  // §35.5.2 says pure applies to nonvoid functions; an imported task can
  // never be pure. Two sites reject this source: parser_dpi.cpp under
  // §35.5.4 with "an imported task cannot be declared pure", and
  // elaborator_dpi.cpp:23 under §35.5.2 with "imported task cannot be declared
  // pure", which is a substring of the parser's message. This case is about the
  // elaborator's rule, so it names §35.5.2, the only field that tells them
  // apart.
  ElabFixture f;
  // The parser rejects this source too, so it reaches the elaborator as a
  // fragment; the permissive helper says that is meant. See the note above on
  // the two sites.
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
  // The minimal valid pure signature: nonvoid return, zero arguments. The
  // arg-scan loop iterates zero times, so this test exercises the elaborator
  // path where only the return-type check runs.
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsLateOutputArgument) {
  // The arg-scan loop must inspect every argument, not just the first.
  // A leading input followed by an output must still raise a diagnostic.
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

// The two cases below read the elaborator's report over a pure imported task,
// and parser_dpi.cpp rejects the same source with "an imported task cannot
// be declared pure" under §35.5.4, whose message contains the elaborator's. The
// subclause each case names is what tells the two apart, since a search on the
// message alone answers with the parser's report first.

// §35.5.2: the report that rejects an imported task declared pure names the
// subclause stating the rule, so a caller learns which rule was enforced
// without matching the wording of the message.
TEST(PureDpiImportRestrictions, PureTaskNames35_5_2) {
  ElabFixture f;
  // The source is rejected by the parser as well, and the report this case is
  // about is emitted regardless; the permissive helper records that.
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
}

// The subclause left the message when it moved into the field. DiagEngine::Emit
// appends the field in the same "(§35.5.2)" form, so a literal that kept the
// prose would print the subclause twice.
TEST(PureDpiImportRestrictions, PureTaskMessageDropsTheProseSubclause) {
  ElabFixture f;
  // The source is rejected by the parser as well, and the report this case is
  // about is emitted regardless; the permissive helper records that.
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
  // §35.5.2's restrictions are scoped to pure functions. A non-pure import
  // with output and inout arguments must remain valid.
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" function void f(output int o, inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
