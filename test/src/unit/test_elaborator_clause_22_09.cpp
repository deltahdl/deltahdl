#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Locate the binding for a named port on an instance, or null if the port was
// left without a connection.
const RtlirPortBinding* FindBinding(const RtlirModuleInst& inst,
                                    std::string_view port) {
  for (const auto& b : inst.port_bindings) {
    if (b.port_name == port) return &b;
  }
  return nullptr;
}

// §22.9: while `unconnected_drive pull1 is active, an unconnected input port is
// driven high. Observe the synthesized port connection carrying the constant 1.
TEST(UnconnectedDriveElaboration, Pull1DrivesUnconnectedInputHigh) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull1\n"
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  const auto* b = FindBinding(top->children[0], "a");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(b->connection, nullptr);
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 1u);
}

// §22.9: while `unconnected_drive pull0 is active, an unconnected input port is
// driven low. Observe the synthesized port connection carrying the constant 0.
TEST(UnconnectedDriveElaboration, Pull0DrivesUnconnectedInputLow) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`unconnected_drive pull0\n"
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  const auto* b = FindBinding(top->children[0], "a");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(b->connection, nullptr);
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 0u);
}

// §22.9: the pull applies "instead of the normal default". Without the
// directive, the same unconnected input keeps the default high-impedance
// connection rather than a pulled constant.
TEST(UnconnectedDriveElaboration, NoDirectiveLeavesUnconnectedInputDefault) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  const auto* b = FindBinding(top->children[0], "a");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(b->connection, nullptr);
  EXPECT_NE(b->connection->kind, ExprKind::kIntegerLiteral);
}

}
