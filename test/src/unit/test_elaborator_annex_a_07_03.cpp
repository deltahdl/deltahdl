#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SpecifyTerminalElaboration, TerminalBitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[3] => b[0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, TerminalPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[7:0] => b[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, TerminalIndexedPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[0+:4] => b[7-:4]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAcceptedAsInputIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(inout wire io, output o);\n"
      "  specify\n"
      "    (io => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InoutPortAcceptedAsOutputIdentifier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, inout wire io);\n"
      "  specify\n"
      "    (i => io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, OutputPortRejectedAsInputIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output o);\n"
      "  specify\n"
      "    (o => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InputPortRejectedAsOutputIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i);\n"
      "  specify\n"
      "    (i => i) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, RefPortRejectedAsInputIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m(ref logic v, output o);\n"
      "  specify\n"
      "    (v => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, RefPortRejectedAsOutputIdentifier) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, ref logic v);\n"
      "  specify\n"
      "    (i => v) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The first alternative of each production — input_identifier ::=
// input_port_identifier and output_identifier ::= output_port_identifier — must
// be *accepted*. Prior tests only exercised the inout alternative and the
// direction negatives; this observes a clean pass where a plain input port is
// taken as a path source and a plain output port as a path destination.
TEST(SpecifyTerminalElaboration, PlainInputAndOutputPortsAcceptedAsTerminals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, output o);\n"
      "  specify\n"
      "    (i => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyTerminalElaboration, InterfacePortFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (bus.a => bus.x) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
