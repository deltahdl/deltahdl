#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_port_connection_elab.h"
#include "lexer/token.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  // No connection is made, and the default is present but left unused.
  EXPECT_EQ(bindings[0].connection, nullptr);
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
  EXPECT_TRUE(f.has_errors);
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

}  // namespace
