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
  EXPECT_NE(bindings[0].connection,
            mod->children[0].resolved->ports[0].default_value);
}

TEST(ImplicitNamedPortConnectionElaboration, EmptyParensLeavesPortUnconnected) {
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
  ASSERT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[0].connection->kind, ExprKind::kUnbasedUnsizedLiteral);
  EXPECT_NE(mod->children[0].resolved->ports[0].default_value, nullptr);
}

TEST(ImplicitNamedPortConnectionElaboration, ErrorForDissimilarNetTypes) {
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
