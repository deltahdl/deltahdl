#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefElaboration, NochangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.4.6 states a negative start/end edge offset shrinks the violation region,
// so negative offsets are legal here -- the opposite of the $width/$period
// non-negativity rule. Negative offset literals must elaborate without error.
TEST(TimingCheckEventDefElaboration, NochangeNegativeOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, -5, -5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Table 31-12: the start/end edge offsets are constant expressions. A specparam
// constant (11.2.1) in both offset positions is built from real specparam
// declaration syntax so the values flow through elaboration, not a stub.
TEST(TimingCheckEventDefElaboration, NochangeSpecparamOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam so = 5, eo = 7;\n"
      "    $nochange(posedge clk, data, so, eo);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// End-to-end over the §31.6 notifier dependency: the notifier argument of
// Syntax 31-14 is a module variable built from a real reg declaration, and the
// full $nochange form carrying it drives through parse+elaborate without error.
TEST(TimingCheckEventDefElaboration, NochangeDeclaredNotifierElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg nt;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 0, 0, nt);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
