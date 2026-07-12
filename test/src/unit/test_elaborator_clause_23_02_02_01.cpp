#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, PortWithoutDirectionInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, DuplicatePortDeclarationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input a;\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, CompletePortDeclRedeclaredAsNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input wire [7:0] a;\n"
      "  wire [7:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// §23.2.2.1: an interconnect port may be connected without complaint as long as
// no signedness is forced on it.
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

// §23.2.2.1: it shall be illegal to specify `signed` for a port declared as an
// interconnect port.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.2.2.1: a net implicitly assumed for a port expression is considered
// unsigned unless the port itself is declared signed; every other implicit net
// is unsigned. The signedness half of the implicit-net rule that §23.2.2.1
// shares with §6.10.
TEST(NonAnsiStylePortDeclarations, ImplicitPortNetSignednessFollowsPort) {
  auto unsigned_net = delta::MakeImplicitPortNet(
      "a", /*port_width=*/8, /*port_is_signed=*/false, delta::NetType::kWire);
  EXPECT_FALSE(unsigned_net.is_signed);

  auto signed_net = delta::MakeImplicitPortNet(
      "c", /*port_width=*/8, /*port_is_signed=*/true, delta::NetType::kWire);
  EXPECT_TRUE(signed_net.is_signed);
}

// §23.2.2.1: real-source form of the implicit-net-signedness rule. A non-ANSI
// port that has no explicit net declaration is not materialized as a separate
// net; it stands for the implicit net directly, so the "unsigned unless the
// port is declared signed" rule manifests on the port itself. Driven through
// parse+elaborate with no net declarations for either port.
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

// §23.2.2.1: if the net declaration of a non-ANSI port is signed, the port is
// also considered signed.
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

// §23.2.2.1: if the port direction declaration is signed, the net declaration
// of that port is also considered signed.
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

// §23.2.2.1: the signedness reconciliation also applies when the port is later
// redeclared as a variable rather than a net.
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

// §23.2.2.1: a port declared only with a direction may be completed by a
// separate variable declaration; when the variable is a vector its range must
// match the port declaration. Matching ranges elaborate cleanly.
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

// §23.2.2.1: the range of the completing variable declaration must be identical
// to the port declaration's range.
TEST(NonAnsiStylePortDeclarations,
     PartialPortDeclAsVariableMismatchedRangesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  logic [3:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §23.2.2.1: once a port is completely declared (here with a variable data
// type), redeclaring it again in a data type declaration is an error.
TEST(NonAnsiStylePortDeclarations,
     CompletePortDeclRedeclaredAsVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input logic [7:0] a;\n"
      "  logic [7:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §23.2.2.1: each port_identifier must be declared in the body with a
// direction; a bare net declaration does not satisfy that requirement.
TEST(NonAnsiStylePortDeclarations, PortWithNetDeclButNoDirectionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  wire a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

// §23.2.2.1: named port connections may be used for an implicit port only when
// its port_expression is a simple (or escaped) identifier, which then serves as
// the port name. Here the implicit port `a` is a plain identifier, so the name
// is available for a named connection (see 23.3.2.2) and binds cleanly.
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

// §23.2.2.1 (negative): an implicit port whose port_expression is a
// concatenation has no port name, so it shall not be reachable by a named
// connection. The concatenation elements (`a`, `b`) are internal names, not
// port names, so `.a(...)` finds no such port and the named connection (see
// 23.3.2.2) is rejected.
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
  EXPECT_GT(f.diag.WarningCount(), 0u)
      << "a concatenation implicit port has no name and cannot be "
         "name-connected";
}

// §23.2.2.1 (negative): a part-select implicit port carries no port name, so a
// named connection using the base identifier must not resolve to it — the LRM's
// split-vector example that "cannot use named port connections." The port is
// built from real non-ANSI source and reached through the named-connection path
// of 23.3.2.2.
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
  EXPECT_GT(f.diag.WarningCount(), 0u)
      << "a part-select implicit port has no name and cannot be name-connected";
}

// §23.2.2.1 (negative): the same holds for a bit-select implicit port; it too
// has no port name and cannot be reached by a named connection.
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
  EXPECT_GT(f.diag.WarningCount(), 0u)
      << "a bit-select implicit port has no name and cannot be name-connected";
}

// §23.2.2.1 (positive contrast): the fix must not strip the name from a simple
// implicit port or an explicitly-named port. A plain identifier port stays
// name-connectable, so this named connection resolves without warning.
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

}  // namespace
