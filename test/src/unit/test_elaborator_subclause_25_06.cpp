#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyInterfaceTerminal, ModportInputUsableAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyInterfaceTerminal, ModportOutputUsableAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p);\n"
      "  specify\n"
      "    (i => p.b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyInterfaceTerminal, ModportOutputRejectedAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.b => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface signal 'p.b' is restricted by its "
                            "modport to an output and cannot be a module "
                            "path source",
                            7, "25.6"));
}

TEST(SpecifyInterfaceTerminal, ModportInputRejectedAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p);\n"
      "  specify\n"
      "    (i => p.a) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface signal 'p.a' is restricted by its "
                            "modport to an input and cannot be a module "
                            "path destination",
                            7, "25.6"));
}

TEST(SpecifyInterfaceTerminal, ModportInoutUsableAsEitherDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic io;\n"
      "  modport mp(inout io);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.io => o) = 5;\n"
      "    (i => p.io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyInterfaceTerminal, PlainInterfaceSignalUsableEitherDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "endinterface\n"
      "module m(Bus p);\n"
      "  specify\n"
      "    (p.a => p.b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyInterfaceTerminal, InterfaceSignalUsableAsTimingCheckTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, input clk);\n"
      "  specify\n"
      "    $setup(p.a, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyInterfaceTerminal, RefModportMemberRejectedAsPathTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(ref a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, output o);\n"
      "  specify\n"
      "    (p.a => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref modport member 'p.a' cannot be used as "
                            "a terminal in a specify block",
                            7, "25.6"));
}

TEST(SpecifyInterfaceTerminal, RefModportMemberRejectedAsTimingTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(ref a, output b);\n"
      "endinterface\n"
      "module m(Bus.mp p, input clk);\n"
      "  specify\n"
      "    $setup(p.a, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref modport member 'p.a' cannot be used "
                            "as a terminal in a specify block",
                            7, "25.6"));
}

TEST(SpecifyInoutTerminal, InoutPortUsableAsEitherTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, inout io, output o);\n"
      "  specify\n"
      "    (io => o) = 5;\n"
      "    (i => io) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyRefTerminalRejected, RefPortRejectedAsPathSource) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(ref logic r, output o);\n"
      "  specify\n"
      "    (r => o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref port 'r' cannot be used as a "
                            "terminal in a specify block",
                            3, "25.6"));
}

TEST(SpecifyRefTerminalRejected, RefPortRejectedAsPathDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input i, ref logic r);\n"
      "  specify\n"
      "    (i => r) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref port 'r' cannot be used as a "
                            "terminal in a specify block",
                            3, "25.6"));
}

TEST(SpecifyRefTerminalRejected, RefPortRejectedAsTimingCheckTerminal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(ref logic r, input clk);\n"
      "  specify\n"
      "    $setup(r, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref port 'r' cannot be used as a "
                            "terminal in a specify block",
                            3, "25.6"));
}

constexpr const char* kBusWithVector =
    "interface Bus;\n"
    "  logic a, b;\n"
    "  logic [3:0] v;\n"
    "  modport mp(input a, v, output b);\n"
    "endinterface\n";

void ExpectSourceRejected(ElabFixture& f, const char* name, int line) {
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string("interface signal '") + name +
                                "' is restricted by its modport to an output "
                                "and cannot be a module path source",
                            line, "25.6"));
}

void ExpectDestinationRejected(ElabFixture& f, const char* name, int line) {
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string("interface signal '") + name +
                                "' is restricted by its modport to an input "
                                "and cannot be a module path destination",
                            line, "25.6"));
}

TEST(SpecifyInterfaceTerminal,
     DISABLED_AModportPickedAtTheConnectionRestrictsAPathSource) {
  ElabFixture f;
  ElaborateSrc(std::string(kBusWithVector) +
                   "module m(Bus p, output o);\n"
                   "  specify\n"
                   "    (p.a => o) = 5;\n"
                   "    (p.b => o) = 5;\n"
                   "  endspecify\n"
                   "endmodule\n"
                   "module top;\n"
                   "  Bus b();\n"
                   "  wire o;\n"
                   "  m u(.p(b.mp), .o(o));\n"
                   "endmodule\n",
               f, "top");
  ExpectSourceRejected(f, "p.b", 9);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "interface signal 'p.a'", 8, "25.6"));
}

TEST(SpecifyInterfaceTerminal,
     DISABLED_AGenericModportHeaderGivesTheModportDirections) {
  ElabFixture f;
  ElaborateSrc(std::string(kBusWithVector) +
                   "module m(interface.mp p, input i, output o);\n"
                   "  specify\n"
                   "    (p.a => o) = 5;\n"
                   "    (i => p.b) = 5;\n"
                   "    (p.b => o) = 5;\n"
                   "    (i => p.a) = 5;\n"
                   "  endspecify\n"
                   "endmodule\n"
                   "module top;\n"
                   "  Bus b();\n"
                   "  wire i, o;\n"
                   "  m u(b.mp, i, o);\n"
                   "endmodule\n",
               f, "top");
  ExpectSourceRejected(f, "p.b", 10);
  ExpectDestinationRejected(f, "p.a", 11);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "interface signal", 8, "25.6"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "interface signal", 9, "25.6"));
}

TEST(SpecifyInterfaceTerminal, AModportOutputAmongFullPathSourcesIsRejected) {
  ElabFixture f;
  ElaborateSrc(std::string(kBusWithVector) +
                   "module m(Bus.mp p, input i, output o);\n"
                   "  specify\n"
                   "    (i, p.a *> o) = 5;\n"
                   "    (i, p.b *> o) = 5;\n"
                   "  endspecify\n"
                   "endmodule\n",
               f);
  ExpectSourceRejected(f, "p.b", 9);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "interface signal", 8, "25.6"));
}

TEST(SpecifyInterfaceTerminal, ABitSelectTakesItsSignalsModportDirection) {
  ElabFixture f;
  ElaborateSrc(std::string(kBusWithVector) +
                   "module m(Bus.mp p, input i, output o);\n"
                   "  specify\n"
                   "    (p.v[1] => o) = 5;\n"
                   "    (i => p.v[1]) = 5;\n"
                   "  endspecify\n"
                   "endmodule\n",
               f);
  ExpectDestinationRejected(f, "p.v", 9);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "interface signal", 8, "25.6"));
}

TEST(SpecifyInterfaceTerminal, AModportOutputIsATimingCheckTerminal) {
  EXPECT_TRUE(ElabOk(std::string(kBusWithVector) +
                     "module m(Bus.mp p, input clk);\n"
                     "  specify\n"
                     "    $setup(p.b, posedge clk, 10);\n"
                     "    $hold(posedge clk, p.b, 10);\n"
                     "  endspecify\n"
                     "endmodule\n"));
}

TEST(SpecifyRefTerminalRejected, RefPortAmongFullPathSourcesIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input i, ref logic r, output o);\n"
      "  specify\n"
      "    (i *> o) = 5;\n"
      "    (i, r *> o) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'r' cannot be used as a terminal in a specify block", 4,
      "25.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "ref port", 3, "25.6"));
}

TEST(SpecifyRefTerminalRejected, RefPortAsTimingCheckReferenceIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input d, input clk, ref logic r);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "    $setup(d, posedge r, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'r' cannot be used as a terminal in a specify block", 4,
      "25.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "ref port", 3, "25.6"));
}

TEST(SpecifyInterfaceTerminal, RefModportMemberRejectedAsPathDestination) {
  ElabFixture f;
  ElaborateSrc(
      "interface Bus;\n"
      "  logic a, b;\n"
      "  modport mp(ref a, output b);\n"
      "endinterface\n"
      "module m(input i, Bus.mp p);\n"
      "  specify\n"
      "    (i => p.b) = 5;\n"
      "    (i => p.a) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref modport member 'p.a' cannot be used as a terminal in a specify "
      "block",
      8, "25.6"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "ref modport member", 7, "25.6"));
}

}  // namespace
