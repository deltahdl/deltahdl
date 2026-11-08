#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

const RtlirPortBinding* FindBinding(const RtlirModuleInst& inst,
                                    std::string_view port) {
  for (const auto& b : inst.port_bindings) {
    if (b.port_name == port) return &b;
  }
  return nullptr;
}

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

TEST(UnconnectedDriveElaboration, Pull1DrivesUnconnectedInputHigh) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(
      ElaborateUnconnectedChild("`unconnected_drive pull1", f, &b));
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 1u);
}

TEST(UnconnectedDriveElaboration, Pull0DrivesUnconnectedInputLow) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(
      ElaborateUnconnectedChild("`unconnected_drive pull0", f, &b));
  EXPECT_EQ(b->connection->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(b->connection->int_val, 0u);
}

TEST(UnconnectedDriveElaboration, NoDirectiveLeavesUnconnectedInputDefault) {
  ElabFixture f;
  const RtlirPortBinding* b = nullptr;
  ASSERT_NO_FATAL_FAILURE(ElaborateUnconnectedChild("", f, &b));
  EXPECT_NE(b->connection->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
