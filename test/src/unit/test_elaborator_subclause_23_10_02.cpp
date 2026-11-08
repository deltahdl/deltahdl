#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterValueAssignment,
     FunctionLocalParameterIsNotOverridableByInstanceAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  function automatic int g();\n"
      "    parameter int INNER = 10;\n"
      "    return INNER;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterValueAssignment,
     TaskLocalParameterIsNotOverridableByInstanceAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  task automatic t();\n"
      "    parameter int INNER = 10;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(8)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedAssignmentCannotTargetTaskLocalParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  task automatic t();\n"
      "    parameter int INNER = 10;\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.INNER(9)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'INNER'", 7,
                            "23.10.2.2"));
}

TEST(ModuleInstanceParameterValueAssignment,
     NestedParameterDoesNotEnlargeOrderedAssignmentSurface) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  function automatic int g();\n"
      "    parameter int INNER = 10;\n"
      "    return INNER;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8, 9) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "too many positional parameter overrides for module 'child'", 8,
      "23.10.2.1"));
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedAssignmentCannotTargetFunctionLocalParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  function automatic int g();\n"
      "    parameter int INNER = 10;\n"
      "    return INNER;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.INNER(9)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'INNER'", 8,
                            "23.10.2.2"));
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedBlockLocalParameterIsNotOverridableByInstanceAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  initial begin : blk\n"
      "    parameter int INNER = 10;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedAssignmentCannotTargetNamedBlockLocalParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "  initial begin : blk\n"
      "    parameter int INNER = 10;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.INNER(9)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'INNER'", 7,
                            "23.10.2.2"));
}

TEST(ModuleInstanceParameterValueAssignment,
     RedefiningSourceParameterUpdatesDependentParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int BASE = 2,\n"
      "               parameter int DERIVED = BASE * 10)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.BASE(5)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 2u);
  EXPECT_EQ(u0->params[0].name, "BASE");
  EXPECT_EQ(u0->params[0].resolved_value, 5);
  EXPECT_EQ(u0->params[1].name, "DERIVED");
  EXPECT_EQ(u0->params[1].resolved_value, 50);
}

TEST(ModuleInstanceParameterValueAssignment,
     StringParameterOverrideReplacesEveryCharacter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string NAME = \"unset\") ();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NAME(\"configured\")) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "NAME");
  EXPECT_TRUE(u0->params[0].is_string_value);
  EXPECT_EQ(u0->params[0].resolved_string, "configured");
}

TEST(ModuleInstanceParameterValueAssignment,
     LenOfAnOverriddenStringParameterFoldsToTheOverridesCharacterCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string NAME = \"unset\") ();\n"
      "  localparam int N = NAME.len();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NAME(\"configured\")) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  const RtlirParamDecl* n = nullptr;
  for (const auto& param : u0->params) {
    if (param.name == "N") n = &param;
  }
  ASSERT_NE(n, nullptr);
  EXPECT_TRUE(n->is_resolved);
  EXPECT_EQ(n->resolved_value, 10);
}

int64_t ChildParam(const RtlirDesign* design, std::string_view name) {
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules[0]->children.empty()) {
    return -1;
  }
  const auto* child = design->top_modules[0]->children[0].resolved;
  if (child == nullptr) return -1;
  for (const auto& param : child->params) {
    if (param.name == name && param.is_resolved) return param.resolved_value;
  }
  return -1;
}

TEST(ModuleInstanceParameterValueAssignment, ElementOfAParameterArray) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter W = 8) (); endmodule\n"
      "module top;\n"
      "  parameter int PARR[3] = '{10, 20, 30};\n"
      "  child #(.W(PARR[2])) u0();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ChildParam(design, "W"), 30);
}

TEST(ModuleInstanceParameterValueAssignment, ElementOfARangedParameterArray) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter W = 8) (); endmodule\n"
      "module top;\n"
      "  parameter int PARR[1:3] = '{10, 20, 30};\n"
      "  child #(.W(PARR[1])) u0();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ChildParam(design, "W"), 10);
}

}  // namespace
