#include <gtest/gtest.h>

#include "common/types.h"
#include "elaborator/elaborator_helpers.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(NonAnsiStylePortDeclarations, BasicInputOutputElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(.a(i), .b(i));\n"
      "  inout i;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, BodyInoutWithNoKindIsANet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(i);\n"
      "  inout i;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_FALSE(design->top_modules[0]->ports[0].is_var);
}

TEST(NonAnsiStylePortDeclarations, TwoImplicitPortsSameNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, a);\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, MixedDirectionExplicitPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(.p({a, e}));\n"
      "  input a;\n"
      "  output e;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, SignednessInheritanceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b, c, d, e, f, g, h);\n"
      "  input [7:0] a;\n"
      "  input [7:0] b;\n"
      "  input signed [7:0] c;\n"
      "  input signed [7:0] d;\n"
      "  output [7:0] e;\n"
      "  output [7:0] f;\n"
      "  output signed [7:0] g;\n"
      "  output signed [7:0] h;\n"
      "  wire signed [7:0] b;\n"
      "  wire [7:0] c;\n"
      "  logic signed [7:0] f;\n"
      "  logic [7:0] g;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, DuplicateExplicitPortNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(.a(x), .a(y));\n"
      "  input x, y;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "duplicate port name '.a'", 1,
                            "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, PortWithoutDirectionInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port 'b' has no direction declaration", 1,
                            "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, DuplicatePortDeclarationIsError) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m(a);\n"
      "  input a;\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate port declaration for 'a'", 3,
                            "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, CompletePortDeclRedeclaredAsNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input wire [7:0] a;\n"
      "  wire [7:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of port 'a' that has a complete "
                            "port declaration",
                            3, "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, PartialPortDeclMatchingRanges) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  wire [7:0] a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, PartialPortDeclMismatchedRangesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  wire [3:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vector range of net 'a' does not match its port "
                            "declaration",
                            3, "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, UnsignedInterconnectPortIsAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout interconnect a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, SignedInterconnectPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module child(inout interconnect signed a);\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interconnect port 'a' shall not be declared "
                            "signed",
                            1, "23.2.2.3"));
}

TEST(NonAnsiStylePortDeclarations, ImplicitPortNetSignednessFollowsPort) {
  auto unsigned_net =
      delta::MakeImplicitPortNet("a", 8, false, delta::NetType::kWire);
  EXPECT_FALSE(unsigned_net.is_signed);

  auto signed_net =
      delta::MakeImplicitPortNet("c", 8, true, delta::NetType::kWire);
  EXPECT_TRUE(signed_net.is_signed);
}

TEST(NonAnsiStylePortDeclarations, SignedPortWithoutNetDeclFollowsDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input signed [7:0] a;\n"
      "  input [7:0] b;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool a_signed = false;
  bool b_signed = true;
  for (const auto& p : mod->ports) {
    if (p.name == "a") a_signed = p.is_signed;
    if (p.name == "b") b_signed = p.is_signed;
  }
  EXPECT_TRUE(a_signed) << "signed port with no net declaration stays signed";
  EXPECT_FALSE(b_signed) << "unsigned port with no net declaration is unsigned";
}

TEST(NonAnsiStylePortDeclarations, NetSignedMakesPortSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(b);\n"
      "  input [7:0] b;\n"
      "  wire signed [7:0] b;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool port_signed = false;
  bool net_signed = false;
  for (const auto& p : mod->ports)
    if (p.name == "b") port_signed = p.is_signed;
  for (const auto& n : mod->nets)
    if (n.name == "b") net_signed = n.is_signed;
  EXPECT_TRUE(port_signed) << "port should inherit signed from its net";
  EXPECT_TRUE(net_signed);
}

TEST(NonAnsiStylePortDeclarations, PortSignedMakesNetSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(c);\n"
      "  input signed [7:0] c;\n"
      "  wire [7:0] c;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool net_signed = false;
  for (const auto& n : mod->nets)
    if (n.name == "c") net_signed = n.is_signed;
  EXPECT_TRUE(net_signed) << "net should inherit signed from its port";
}

TEST(NonAnsiStylePortDeclarations, PortSignedMakesVariableSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(g);\n"
      "  output signed [7:0] g;\n"
      "  logic [7:0] g;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool var_signed = false;
  for (const auto& v : mod->variables)
    if (v.name == "g") var_signed = v.is_signed;
  EXPECT_TRUE(var_signed) << "variable should inherit signed from its port";
}

TEST(NonAnsiStylePortDeclarations, PartialPortDeclAsVariableMatchingRanges) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  logic [7:0] a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations,
     PartialPortDeclAsVariableMismatchedRangesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  logic [3:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vector range of variable 'a' does not match its "
                            "port declaration",
                            3, "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations,
     CompletePortDeclRedeclaredAsVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input logic [7:0] a;\n"
      "  logic [7:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of port 'a' that has a complete "
                            "port declaration",
                            3, "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, PortWithNetDeclButNoDirectionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  wire a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "port 'a' has no direction declaration", 1,
                            "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations,
     ImplicitSimpleIdentifierPortConnectableByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a);\n"
      "  input a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u)
      << "a simple-identifier implicit port carries its name and is nameable";
}

TEST(NonAnsiStylePortDeclarations,
     ImplicitConcatenationPortNotConnectableByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child({a, b});\n"
      "  input a, b;\n"
      "endmodule\n"
      "module top;\n"
      "  wire x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'a' not found", 6, "23.3.2.2"));
}

TEST(NonAnsiStylePortDeclarations, ImplicitPartSelectPortNotConnectableByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a[3:0]);\n"
      "  input [7:0] a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'a' not found", 6, "23.3.2.2"));
}

TEST(NonAnsiStylePortDeclarations, ImplicitBitSelectPortNotConnectableByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a[3]);\n"
      "  input [7:0] a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "port 'a' not found", 6, "23.3.2.2"));
}

TEST(NonAnsiStylePortDeclarations, SelectPortFixKeepsSimplePortNameable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a);\n"
      "  input [7:0] a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u)
      << "a simple-identifier implicit port keeps its name after the fix";
}

TEST(NonAnsiStylePortDeclarations, PortWithoutADirectionNames23_2_2_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "has no direction declaration", 1, "23.2.2.1"));
}

TEST(NonAnsiStylePortDeclarations, ABodyDeclarationGivesAPortItsKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b, f);\n"
      "  input a;\n"
      "  input [1:0] b; wand [1:0] b;\n"
      "  output [7:0] f; logic [7:0] f;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 3u);
  EXPECT_FALSE(ports[0].is_var);
  EXPECT_EQ(ports[0].net_type, delta::NetType::kWire);
  EXPECT_FALSE(ports[1].is_var);
  EXPECT_EQ(ports[1].net_type, delta::NetType::kWand);
  EXPECT_TRUE(ports[2].is_var);
  EXPECT_EQ(ports[2].net_type, delta::NetType::kNone);
}

TEST(NonAnsiStylePortDeclarations, AVarDeclaredPortIsACompleteVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input var [1:0] a;\n"
      "  output var b;\n"
      "  wire b;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  const auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_TRUE(ports[0].is_var);
  EXPECT_EQ(ports[0].net_type, delta::NetType::kNone);
  EXPECT_EQ(ports[0].width, 2u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of port 'b' that has a complete "
                            "port declaration",
                            4, "23.2.2.1"));
}

}  // namespace
