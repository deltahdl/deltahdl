
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

void ExpectWideModuleElaborates(int port_count) {
  std::string src = "module wide(";
  for (int i = 0; i < port_count; ++i) {
    if (i > 0) src += ", ";
    src += "input logic p";
    src += std::to_string(i);
  }
  src += ");\nendmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f, "wide");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports.size(),
            static_cast<size_t>(port_count));
}

TEST(PortDeclaration, StructPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } data_in,\n"
      "  output logic [15:0] data_out\n"
      ");\n"
      "  assign data_out = data_in;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kStruct);
}

TEST(PortDeclaration, UnionPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input union packed { logic [31:0] word; logic [3:0][7:0] bytes; } u\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kUnion);
}

TEST(PortDeclaration, EventPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input event e);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kEvent);
}

TEST(PortDeclaration, InterfacePortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module m(ifc bus);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].name, "bus");
}

TEST(PortDeclaration, ArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [7:0] mem [0:15],\n"
      "  output wire [3:0] bus [4]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
}

// §23.2.2: a port may be a *variable* of any allowed data type. The mh1
// example illustrates this with var-qualified integer and real ports. Those
// var-typed scalar forms are only exercised at parse time elsewhere; observe
// here that they survive elaboration with their data-type kind preserved and
// the non-net (variable) flag set, alongside a struct output port.
TEST(PortDeclaration, VarTypedScalarPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mh1(\n"
      "  input var int in1,\n"
      "  input var shortreal in2,\n"
      "  output struct packed { logic [7:0] a; logic [7:0] b; } out\n"
      ");\n"
      "endmodule\n",
      f, "mh1");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 3u);
  const auto& ports = design->top_modules[0]->ports;
  EXPECT_EQ(ports[0].type_kind, DataTypeKind::kInt);
  EXPECT_TRUE(ports[0].is_var);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].type_kind, DataTypeKind::kShortreal);
  EXPECT_TRUE(ports[1].is_var);
  EXPECT_EQ(ports[2].type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(ports[2].direction, Direction::kOutput);
}

// §23.2.2: an enumeration is an admitted port data type, and §23.2.2.3 decides
// the port kind separately from it: "If the port kind is omitted: for input and
// inout ports, the port shall default to a net of default net type." No
// exception is made for a port that names a data type -- that clause's own
// `module mh1 (integer x);` means `inout wire integer x`, and `module mh7
// (input var integer x);` shows that `var` is what makes an input a variable.
// So the inline enum port carries the enum kind at its base (int) width and is
// a net.
//
// Being a net, it is a net the standard forbids. §6.7.1 admits only a 4-state
// integral type as a net's data type, so that "a net is composed entirely of
// 4-state bits", and an enumeration with no explicit base has the 2-state `int`
// base of §6.19. So the port carries the enum kind at its base width, is a net,
// and is rejected -- all three read off the same declaration.
TEST(PortDeclaration, EnumPortElaboratesAsANetWhenThePortKindIsOmitted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input enum { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.type_kind, DataTypeKind::kEnum);
  EXPECT_EQ(port.width, 32u);
  EXPECT_FALSE(port.is_var);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// The same port with `var` written in front of it. §23.2.2.3 counts `var`
// among the port kinds -- "the term port kind is used to mean any of the net
// type keywords, or the keyword var, which are used to explicitly declare a
// port of one of these kinds" -- so it says what the port is, not what type it
// has. The port is then a variable rather than the net an input defaults to,
// and §6.7.1 is about nets, so the very enumeration rejected just above is
// accepted here.
//
// The two sources differ by that one word, which is what makes this pair worth
// having: it reads the effect of `var` rather than the acceptability of an
// enumeration. Syntax 23-4 writes the variable form as `var_data_type ::=
// data_type | var data_type_or_implicit`, the same data_type the net form
// takes, so an enumeration defined in place stands after `var` exactly as it
// stands without it. The port name is asserted because a parse that did not
// recognize the enumeration there would read the name from the `enum` keyword.
TEST(PortDeclaration, VarEnumPortElaboratesAsAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input var enum { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.name, "color");
  EXPECT_EQ(port.type_kind, DataTypeKind::kEnum);
  EXPECT_EQ(port.width, 32u);
  EXPECT_TRUE(port.is_var);
}

// A struct defined in place is the other data_type form that has to be
// recognized where a port's type is written, and `var` takes it for the same
// reason it takes an enumeration. The output port above is written without a
// port kind; this one is written with one, so the two spellings of the same
// declared type are both covered.
TEST(PortDeclaration, VarStructPortElaboratesAsAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input var struct packed { logic [7:0] a; logic [7:0] b; } s\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.name, "s");
  EXPECT_EQ(port.type_kind, DataTypeKind::kStruct);
  EXPECT_EQ(port.width, 16u);
  EXPECT_TRUE(port.is_var);
}

// The same port with a 4-state base is a legal net, so it elaborates cleanly.
// This is what separates the rejection above from one that turned away every
// enum port, and it is the spelling that makes an enum usable on an input
// whose port kind is omitted.
TEST(PortDeclaration, EnumPortWithAFourStateBaseIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input enum logic [1:0] { RED, GREEN, BLUE } color\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.2.2.3's rule is not about enumerations: an input port with the port kind
// omitted is a net whatever data type it names, so any 2-state data type on one
// is a net data type §6.7.1 does not admit.
TEST(PortDeclaration, TwoStateInputPortIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(\n"
      "  input bit [7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net data type must be 4-state", 2, "6.7.1"));
}

// The asymmetry §23.2.2.3 draws, and the reason the rejection above cannot be
// written as "a 2-state port data type is illegal". For an output "if the data
// type is declared with the explicit data_type syntax, the port kind shall
// default to variable", and the clause's `module mh11(output integer x);`
// means `output var integer x`. A variable is outside §6.7.1 entirely, so the
// same 2-state data type is accepted here.
TEST(PortDeclaration, TwoStateOutputPortIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  output bit [7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.2.2: a port data type may carry multiple packed dimensions. The
// elaborated width is the product of the two packed dimensions (4 * 8) with no
// unpacked dimension.
TEST(PortDeclaration, PackedArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [3:0][7:0] data\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(port.width, 32u);
  EXPECT_EQ(port.num_unpacked_dims, 0u);
}

// §23.2.2: a port may be a multidimensional (2-D) unpacked array. Both unpacked
// dimensions are folded to their element counts (4 and 2) during elaboration.
TEST(PortDeclaration, MultiDimUnpackedArrayPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input logic [7:0] mem [0:3][0:1]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  const auto& port = design->top_modules[0]->ports[0];
  EXPECT_EQ(port.num_unpacked_dims, 2u);
  ASSERT_EQ(port.unpacked_dim_sizes.size(), 2u);
  EXPECT_EQ(port.unpacked_dim_sizes[0], 4u);
  EXPECT_EQ(port.unpacked_dim_sizes[1], 2u);
}

TEST(PortDeclaration, ModuleWithAtLeast256PortsElaborates) {
  ExpectWideModuleElaborates(300);
}

TEST(PortDeclaration, ModuleWithExactly256PortsElaborates) {
  ExpectWideModuleElaborates(256);
}

TEST(PortDeclaration, UnpackedArrayOfStructPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(\n"
      "  input struct packed { logic [7:0] a; logic [7:0] b; } items [0:3]\n"
      ");\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->ports[0].type_kind, DataTypeKind::kStruct);
}

}  // namespace
