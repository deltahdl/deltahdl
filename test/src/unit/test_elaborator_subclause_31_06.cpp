#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §31.6 (printed page 915): "The notifier is a variable, declared in the
// module where timing check tasks are invoked", and Syntax 31-2 writes
// `notifier ::= variable_identifier`. A net of the module is no variable, so
// naming one as the notifier is refused.
TEST(TimingCheckNotifierElaboration, LocalNetNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk);\n"
      "  wire n;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 'n' is a net, not a "
                            "variable",
                            4, "31.6"));
}

// A port that is a net is refused the same way.
TEST(TimingCheckNotifierElaboration, NetPortNotifierRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, clk, output wire n);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 2, n);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "timing check notifier 'n' is a net, not a "
                            "variable",
                            3, "31.6"));
}

// A reg, an integer and a logic variable are each a variable, and so is an
// output port declared as one.
TEST(TimingCheckNotifierElaboration, VariableNotifiersAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input d, clk, output reg pr);\n"
      "  reg r; integer i; logic l;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5, r);\n"
      "    $setup(d, posedge clk, 5, i);\n"
      "    $setup(d, posedge clk, 5, l);\n"
      "    $setup(d, posedge clk, 5, pr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
