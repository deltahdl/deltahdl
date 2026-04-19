#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.7.1 R3: a bare PATHPULSE$ sets module-wide pulse limits and must
// elaborate cleanly in the presence of a specify-block module path.
TEST(PulseControlSpecparamElab, ModuleWidePathpulseElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "    specparam PATHPULSE$ = (2, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.7.1 R4: a path-specific PATHPULSE$input$output override may coexist
// with the module-wide default without conflict.
TEST(PulseControlSpecparamElab, PathSpecificCoexistsWithModuleWide) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "    specparam PATHPULSE$ = (2, 5);\n"
      "    specparam PATHPULSE$a$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.7.1 R5: the input terminal of a PATHPULSE$ must be an entire port —
// a bit-select is not legal.
TEST(PulseControlSpecparamElab, BitSelectInputTerminalRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [3:0] a, output b);\n"
      "  specify\n"
      "    (a[0] => b) = 10;\n"
      "    specparam PATHPULSE$a[0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.7.1 R5: the output terminal of a PATHPULSE$ must be an entire port —
// a bit-select is not legal.
TEST(PulseControlSpecparamElab, BitSelectOutputTerminalRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output [3:0] b);\n"
      "  specify\n"
      "    (a => b[0]) = 10;\n"
      "    specparam PATHPULSE$a$b[0] = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.7.1 R5: part-selects on PATHPULSE$ terminals are likewise illegal.
TEST(PulseControlSpecparamElab, PartSelectTerminalRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [3:0] a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "    specparam PATHPULSE$a[3:0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
