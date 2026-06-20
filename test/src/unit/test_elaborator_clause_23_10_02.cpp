#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §23.10.2: module instance parameter value assignment supplies values to the
// parameters specified in a module's definition. A parameter declared inside a
// named block, task, or function is not part of that overridable surface; such
// a parameter can only be redefined directly with a defparam statement, never
// by an ordered or named instance parameter value assignment. The tests below
// confirm that the elaborator's override surface is the module's own parameters
// and excludes parameters nested inside a function, task, or named block.

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
  // Only the module parameter W is part of the override surface; the function's
  // INNER parameter is not exposed to instance parameter value assignment.
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
     NestedParameterDoesNotEnlargeOrderedAssignmentSurface) {
  ElabFixture f;
  // The module exposes a single overridable parameter (W). A function-local
  // parameter must not count toward the ordered list, so a second positional
  // value has no parameter to bind to and is rejected.
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
  EXPECT_TRUE(f.has_errors);
}

TEST(ModuleInstanceParameterValueAssignment,
     NamedAssignmentCannotTargetFunctionLocalParameter) {
  ElabFixture f;
  // A parameter declared inside a function is not part of the module's
  // overridable surface. A named instance parameter value assignment that tries
  // to reach it by name is rejected; such a parameter can only be redefined
  // directly by a defparam statement.
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
  EXPECT_TRUE(f.has_errors);
}

// §23.10.2 also notes that when a parameter's value depends on a second
// parameter, redefining the second parameter updates the first as well (see
// §23.10.3, Parameter dependence). The elaborator re-evaluates a dependent
// parameter against the overridden value of the parameter it references, so an
// instance parameter value assignment to the source parameter flows through.
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

}  // namespace
