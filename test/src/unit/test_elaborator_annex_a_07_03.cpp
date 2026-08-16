#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // `o` is legal as the destination, so the only report is the one about the
  // source terminal this case is named for.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "module path source 'o' must be connected to an input or inout port", 3,
      "30.4.1"));
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
  // `i` is legal as the source, so the destination report is the one this case
  // is named for.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "module path destination 'i' must be connected to an "
                    "output or inout port",
                    3, "30.4.1"));
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
  // §25.6 states the ref-port prohibition once for both roles the specify block
  // has, so a module path terminal reports the same subclause a timing-check
  // terminal does, and it is the subclause the sentence is written in.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'v' cannot be used as a terminal in a specify block", 3,
      "25.6"));
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
  // §25.6 states the ref-port prohibition once for both roles the specify block
  // has, so a module path terminal reports the same subclause a timing-check
  // terminal does, and it is the subclause the sentence is written in.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'v' cannot be used as a terminal in a specify block", 3,
      "25.6"));
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
