#include <gtest/gtest.h>

#include <string>

#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_port_connection_elab.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(ImplicitNamedPortConnectionElaboration,
     ImplicitConnectionHasCorrectDirection) {
  ElabFixture f;
  ExpectTwoPortDirections(f, ".a, .b");
}

TEST(ImplicitNamedPortConnectionElaboration, ErrorWhenSignalNotDeclared) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires signal 'a' to be declared", 4,
                            "23.3.2.3"));
}

TEST(ImplicitNamedPortConnectionElaboration,
     ErrorWhenSignalNotDeclaredEvenWithDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a = 1'b0);\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires signal 'a' to be declared", 4,
                            "23.3.2.3"));
}

TEST(ImplicitNamedPortConnectionElaboration, NoImplicitNetForUndeclaredSignal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& net : mod->nets) {
    EXPECT_NE(net.name, "a");
  }
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "implicit named port connection '.a' requires signal 'a' "
                    "to be declared in the instantiating scope",
                    4, "23.3.2.3"));
}

TEST(ImplicitNamedPortConnectionElaboration, MixedImplicitAndExplicitResolve) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, x, c;\n"
      "  child u0(.a, .b(x), .c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 3u);
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_NE(bindings[1].connection, nullptr);
  EXPECT_NE(bindings[2].connection, nullptr);
}

TEST(ImplicitNamedPortConnectionElaboration, ErrorForNonEquivalentDataTypes) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] a;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires equivalent data types", 5, "23.3.2.3"));
}

TEST(ImplicitNamedPortConnectionElaboration,
     ImplicitConnectionDoesNotUseDefault) {
  // 23.3.2.3: when an implicit .name connection is used it is assumed the
  // coder intends to connect the like-named signal, so the input port's
  // default value is NOT used even though one is specified. The binding must
  // therefore be the like-named signal identifier, not the default literal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 1u);
  ASSERT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[0].connection->kind, ExprKind::kIdentifier);
  EXPECT_EQ(bindings[0].connection->text, "a");
  // The connection is the signal, distinct from the port's default value.
  EXPECT_NE(bindings[0].connection,
            mod->children[0].resolved->ports[0].default_value);
}

TEST(ImplicitNamedPortConnectionElaboration, EmptyParensLeavesPortUnconnected) {
  // 23.3.2.3: to leave a port that has a default value unconnected, empty
  // parentheses are written after the name (.name()). In contrast to the
  // implicit .name form -- which connects the like-named signal -- the empty
  // form connects nothing, and the default value is still not used. The
  // like-named signal 'a' exists in scope yet is deliberately NOT connected.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.a());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 1u);
  // No signal is connected, and the default is present but left unused: the
  // unconnected net port takes 'z (§23.3.3.3).
  ASSERT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[0].connection->kind, ExprKind::kUnbasedUnsizedLiteral);
  EXPECT_NE(mod->children[0].resolved->ports[0].default_value, nullptr);
}

TEST(ImplicitNamedPortConnectionElaboration, ErrorForDissimilarNetTypes) {
  // 23.3.2.3: an implicit .name connection between two genuinely dissimilar
  // net types is an error -- precisely the cases where an explicit named
  // connection only warns (23.3.3.7). A wand port driven by a wor signal is
  // such a case.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor a;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "between dissimilar net types", 5, "23.3.2.3"));
}

TEST(ImplicitNamedPortConnectionElaboration,
     ExplicitDissimilarNetTypesOnlyWarns) {
  // Contrast with the implicit form above: an explicit .a(a) named connection
  // of the same dissimilar net types is only a warning, not an error. The
  // 23.3.2.3 escalation to an error applies only to the implicit .name form.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "endmodule\n"
      "module top;\n"
      "  wor a;\n"
      "  child u0(.a(a));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(ImplicitNamedPortConnectionElaboration,
     EquivalentNetTypesConnectWithoutError) {
  // 23.3.2.3: the dissimilar-net-type error is limited to genuinely dissimilar
  // nets. wire and tri are equivalent aliases, so an implicit .name connection
  // between a wire port and a tri signal is accepted with no error and the
  // signal is bound.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  tri a;\n"
      "  child u0(.a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 1u);
  EXPECT_NE(bindings[0].connection, nullptr);
}

// 23.3.2.3: an implicit .name connection needs its name declared in the
// instantiating scope, and an interface instance is one such declaration for an
// interface port (§25.3.2). This is the control for that acceptance: with no
// instance and no signal of the name `iface` in top -- the only `iface` being
// the port of `sub` -- the connection is still reported, on line 7.
TEST(ImplicitNamedPortConnectionElaboration,
     ErrorWhenInterfaceInstanceNotDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "interface test_bus;\n"
      "  logic test_pad;\n"
      "endinterface\n"
      "module sub(test_bus iface);\n"
      "endmodule\n"
      "module top;\n"
      "  sub sub (.iface);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires signal 'iface' to be declared", 7,
                            "23.3.2.3"));
}

// §23.3.2.3 with §6.22.2: the declarations either side of the implicit
// connection have equivalent data types, so an int port joined to a 4-state
// unsigned vector of its width, and a signed port joined to an unsigned vector
// of its width, are each reported, while a 4-state net port joined to a logic
// vector, a 2-state port to a bit vector and an output to a wire are not.
TEST(ImplicitNamedPortConnectionElaboration,
     SameWidthButNonEquivalentTypesAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input var int a, input var logic signed [7:0] b,\n"
      "             input logic [7:0] c, input var bit [3:0] d,\n"
      "             output logic [7:0] e);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [31:0] a;\n"
      "  logic [7:0] b, c;\n"
      "  bit [3:0] d;\n"
      "  wire [7:0] e;\n"
      "  child u0(.a, .b, .c, .d, .e);\n"
      "endmodule\n",
      f);
  const char* message = "differ in signing or in their number of states";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'.a' requires equivalent",
                            10, "23.3.2.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'.b' requires equivalent",
                            10, "23.3.2.3"));
  for (const char* port : {"'.c'", "'.d'", "'.e'"}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), port, 10, "23.3.2.3"))
        << port;
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 10, "23.3.2.3"));
}

// §23.3.2.3: a `.name` connection to a variable a package import brings into
// the instantiating module is no error, from an explicit import or a wildcard
// one alike, whichever of the packages declares it; a name imported only
// inside a generate block is not visible at module level (§26.3 with §27.5),
// and a `.name` connection to it stays an error.
TEST(ImplicitNamedPortConnectionElaboration, ImportedNamesAreDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  logic a, b;\n"
      "endpackage\n"
      "package q;\n"
      "  logic c;\n"
      "endpackage\n"
      "package r;\n"
      "  logic e;\n"
      "endpackage\n"
      "module child(input logic a, input logic b, input logic c,\n"
      "             input logic e);\n"
      "endmodule\n"
      "module top;\n"
      "  import p::a;\n"
      "  import q::*;\n"
      "  import p::*;\n"
      "  if (1) begin : g\n"
      "    import r::e;\n"
      "  end\n"
      "  child u0(.a, .b, .c, .e);\n"
      "endmodule\n",
      f);
  for (const char* name : {"'a'", "'b'", "'c'"}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               std::string("requires signal ") + name, 20,
                               "23.3.2.3"))
        << name;
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "requires signal 'e'", 20,
                            "23.3.2.3"));
}

}  // namespace
