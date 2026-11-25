#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "ref port 'v' cannot be used as a terminal in a specify block", 3,
      "25.6"));
}

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
      "interface Bus;\n"
      "  logic a, x;\n"
      "endinterface\n"
      "module m(Bus bus);\n"
      "  specify\n"
      "    (bus.a => bus.x) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::string PathIn(const std::string& head, const std::string& path) {
  return head +
         "\n"
         "  specify\n"
         "    " +
         path +
         "\n"
         "  endspecify\n"
         "endmodule\n";
}

bool ElaboratesClean(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return !f.has_errors;
}

bool AnErrorStandsOnLine(const std::string& src, uint32_t line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line) return true;
  }
  return false;
}

void ExpectPathReported(const std::string& src, const std::string& message) {
  ElabFixture f;
  ElaborateSrc(src, f);
  uint32_t line = LineHolding(src, "    ");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "30.4.1"))
      << src;
}

TEST(SpecifyTerminalElaboration, AnOutputPortIsNoSourceOfAnEdgeSensitivePath) {
  const std::string kHead = "module m(input i, clk, output o, o2);";
  ExpectPathReported(PathIn(kHead, "(posedge o2 => (o : i)) = 1;"),
                     "module path source 'o2' must be connected to an input "
                     "or inout port");
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "(posedge clk => (o : i)) = 1;")));
}

TEST(SpecifyTerminalElaboration, AnUnconnectedNetIsNoSourceOfAConditionalPath) {
  const std::string kHead = "module m(input c, i, output y); wire x;";
  for (const char* path : {"if (c) (x => y) = 1;", "ifnone (x => y) = 1;"}) {
    ExpectPathReported(
        PathIn(kHead, path),
        "module path source 'x' is not connected to an input or inout port");
  }
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "if (c) (i => y) = 1;")));
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "ifnone (i => y) = 1;")));
}

TEST(SpecifyTerminalElaboration, ABitSelectOfAnOutputPortIsNoSource) {
  const std::string kHead = "module m(input [1:0] i, output [1:0] o, p);";
  ExpectPathReported(
      PathIn(kHead, "(o[0] => p[0]) = 1;"),
      "module path source 'o' must be connected to an input or inout port");
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "(i[0] => p[0]) = 1;")));
}

TEST(SpecifyTerminalElaboration,
     AnInputPortIsNoDestinationOfAnEdgeSensitiveOrConditionalPath) {
  const std::string kHead = "module m(input en, clk, d, i2, output o);";
  for (const char* path :
       {"(posedge clk => (i2 +: d)) = 5;", "if (en) (d => i2) = 5;"}) {
    ExpectPathReported(PathIn(kHead, path),
                       "module path destination 'i2' must be connected to an "
                       "output or inout port");
  }
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "(posedge clk => (o +: d)) = 5;")));
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "if (en) (d => o) = 5;")));
}

TEST(SpecifyTerminalElaboration,
     ALocalVariableIsNoDestinationButAnOutputRegIs) {
  const std::string kHead = "module m(input a, output reg r); logic v;";
  ExpectPathReported(PathIn(kHead, "(a => v) = 5;"),
                     "module path destination 'v' is not connected to an "
                     "output or inout port");
  EXPECT_TRUE(ElaboratesClean(PathIn(kHead, "(a => r) = 5;")));
}

TEST(SpecifyTerminalElaboration, DISABLED_ASourceDeclaredNowhereIsRejected) {
  const std::string kHead = "module m(input i, output b);";
  for (const char* path : {"(nosuch => b) = 5;", "(bus.a => b) = 5;"}) {
    EXPECT_TRUE(AnErrorStandsOnLine(PathIn(kHead, path), 3)) << path;
  }
}

TEST(SpecifyTerminalElaboration,
     DISABLED_ADestinationNamingNoOutputIdentifierIsRejected) {
  const std::string kBus =
      "interface Bus;\n"
      "  logic a, b;\n"
      "endinterface\n";
  EXPECT_TRUE(AnErrorStandsOnLine(
      PathIn("module m(input i, output o);", "(i => nosuch) = 5;"), 3));
  EXPECT_TRUE(AnErrorStandsOnLine(
      PathIn("module m(input i, output o);", "(i => bus.x) = 5;"), 3));
  EXPECT_TRUE(AnErrorStandsOnLine(
      kBus + PathIn("module m(input i, Bus p);", "(i => p.zz) = 5;"), 6));
  EXPECT_TRUE(AnErrorStandsOnLine(
      kBus +
          PathIn("module m(input i, output o); Bus bi();", "(i => bi.b) = 5;"),
      6));
  EXPECT_TRUE(ElaboratesClean(
      kBus + PathIn("module m(input i, Bus p);", "(i => p.b) = 5;")));
}

TEST(SpecifyTerminalElaboration, AConstantPathTerminalSelectIsAccepted) {
  const std::string kHead =
      "module m(input [3:0] a, output [3:0] y); specparam K = 1;";
  for (const char* path :
       {"(a[K] => y[0]) = 2;", "(a[0] => y[K]) = 2;", "(a[K:0] *> y[0]) = 2;",
        "(a[K+:2] *> y[1:0]) = 2;", "(a[0+:K] *> y[K-:1]) = 2;"}) {
    EXPECT_TRUE(ElaboratesClean(PathIn(kHead, path))) << path;
  }
}

TEST(SpecifyTerminalElaboration,
     DISABLED_ANonConstantPathTerminalSelectIsRejected) {
  const std::string kHead =
      "module m(input [3:0] a, output [3:0] y); integer i;";
  for (const char* path :
       {"(a[i] => y[0]) = 2;", "(a[0] => y[i]) = 2;", "(a[i] *> y[0]) = 2;",
        "(a[0] *> y[i]) = 2;", "(a[i:0] *> y[0]) = 2;", "(a[3:i] => y[0]) = 2;",
        "(a[i+:2] *> y[1:0]) = 2;", "(a[0+:i] *> y[1:0]) = 2;",
        "(a[1:0] *> y[i-:2]) = 2;"}) {
    EXPECT_TRUE(AnErrorStandsOnLine(PathIn(kHead, path), 3)) << path;
  }
}

}  // namespace
