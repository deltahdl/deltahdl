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

// Elaborate a top wrapping a single unconnected-input child instance,
// optionally guarded by the given `unconnected_drive directive line, then
// return the binding for the child's input port. The shared assertions that
// every §22.9 test relies on (design built, no errors, one top, one child,
// present binding with a connection) run here; `out_binding` receives the
// located binding.
void ElaborateUnconnectedChild(std::string_view directive, ElabFixture& f,
                               const RtlirPortBinding** out_binding) {
  std::string src;
  if (!directive.empty()) {
    src += directive;
    src += "\n";
  }
  src +=
      "module child(input wire a);\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "endmodule\n";
  // Leave the `unconnected_drive directive in effect for the single child
  // instance: deltahdl models unconnected_drive as one compilation-unit-wide
  // value taken after preprocessing, so a trailing `nounconnected_drive would
  // reset it before elaboration. Per §22.9 an unclosed directive stays active.

  auto* design = ElaborateWithPreprocessor(src, f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  const auto* b = FindBinding(top->children[0], "a");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(b->connection, nullptr);
  *out_binding = b;
}

// §22.9: while `unconnected_drive pull1 is active, an unconnected input port is
// driven high. Observe the synthesized port connection carrying the constant 1.
TEST(UnconnectedDriveElaboration, Pull1DrivesUnconnectedInputHigh) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(
      ElaborateUnconnectedChild("`unconnected_drive pull1", f, &b));
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 1u);
}

// §22.9: while `unconnected_drive pull0 is active, an unconnected input port is
// driven low. Observe the synthesized port connection carrying the constant 0.
TEST(UnconnectedDriveElaboration, Pull0DrivesUnconnectedInputLow) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(
      ElaborateUnconnectedChild("`unconnected_drive pull0", f, &b));
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 0u);
}

// §22.9: the pull applies "instead of the normal default". Without the
// directive, the same unconnected input keeps the default high-impedance
// connection rather than a pulled constant.
TEST(UnconnectedDriveElaboration, NoDirectiveLeavesUnconnectedInputDefault) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(ElaborateUnconnectedChild("", f, &b));
  EXPECT_NE(b->connection->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
