#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsOutputArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(output int o);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsInoutArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureCannotApplyToImportedTask) {
  // §35.5.2 says pure applies to nonvoid functions; an imported task can
  // never be pure. The parser surface lets `pure task` through, so the
  // elaborator carries the responsibility of rejecting it.
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// The elaborator's report over a pure imported task, selected by its whole
// message rather than by a substring of it. parser_port.cpp:627 rejects the
// same source with "an imported task cannot be declared pure" under §35.5.4,
// which contains the elaborator's message, so FindDiag returns the parser's
// report first and a case reading the subclause off it reads the wrong rule.
const Diagnostic* FindPureTaskReport(const ElabFixture& f) {
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message == "imported task cannot be declared pure") return &diag;
  }
  return nullptr;
}

// §35.5.2: the report that rejects an imported task declared pure names the
// subclause stating the rule, so a caller learns which rule was enforced
// without matching the wording of the message.
TEST(PureDpiImportRestrictions, PureTaskNames35_5_2) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  const Diagnostic* rep = FindPureTaskReport(f);
  ASSERT_NE(rep, nullptr);
  EXPECT_EQ(rep->subclause, "35.5.2");
}

// The subclause left the message when it moved into the field. DiagEngine::Emit
// appends the field in the same "(§35.5.2)" form, so a literal that kept the
// prose would print the subclause twice.
TEST(PureDpiImportRestrictions, PureTaskMessageDropsTheProseSubclause) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  const Diagnostic* rep = FindPureTaskReport(f);
  ASSERT_NE(rep, nullptr);
  EXPECT_EQ(rep->message.find("§"), std::string::npos);
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
