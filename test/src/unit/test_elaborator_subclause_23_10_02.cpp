#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
     NamedAssignmentCannotTargetTaskLocalParameter) {
  ElabFixture f;
  // The error-path counterpart for the task site: a parameter declared inside a
  // task is not part of the module's overridable surface, so a named instance
  // parameter value assignment aimed at it is rejected. Such a parameter can
  // only be redefined directly by a defparam statement. ResolveNamedInstParams
  // files the rejection under §23.10.2.2, the subclause for the named form of
  // the assignment.
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
  // The module exposes a single overridable parameter (W). A function-local
  // parameter must not count toward the ordered list, so a second positional
  // value has no parameter to bind to and is rejected.
  // ResolvePositionalInstParams files the rejection under §23.10.2.1, the
  // subclause for the ordered form of the assignment.
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
  // A parameter declared inside a function is not part of the module's
  // overridable surface. A named instance parameter value assignment that tries
  // to reach it by name is rejected; such a parameter can only be redefined
  // directly by a defparam statement. ResolveNamedInstParams files the
  // rejection under §23.10.2.2, the subclause for the named form.
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
  // §23.10.2 names three declaration sites -- a named block, a task, or a
  // function -- whose parameters can only be redefined by a defparam statement,
  // never by an instance parameter value assignment. A parameter declared in a
  // named begin-end block is therefore not part of the module's override
  // surface, which stays limited to the module's own parameter W.
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
  // The error-path counterpart for the named-block site: a named instance
  // parameter value assignment that tries to reach a block-local parameter is
  // rejected, because that parameter can only be redefined by defparam.
  // ResolveNamedInstParams files the rejection under §23.10.2.2, the subclause
  // for the named form.
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

// §6.16 rules that for the string data type "no truncation occurs", and
// §23.10.2 puts an overridden parameter's value under that rule as much as a
// declared one. "configured" is ten characters, which is past both the eight
// RtlirParamDecl::resolved_value can hold and the four the 32-bit lowering
// keeps, so this asserts the characters reached the elaborated parameter rather
// than that some wider number did. is_string_value is asserted beside them
// because it is what every later reader consults before touching
// resolved_string.
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

// §6.16.1's len() over an overridden parameter, which does not follow from the
// characters being stored. StringParamLength reads resolved_string only after
// is_string_value passes, so an override that carried the characters without
// setting the flag leaves len() unfolded and `N` at its unresolved 0. Ten is
// also unreachable from the packed value of "configured", which §11.10 makes
// wider than the 64 bits resolved_value holds, and from the five characters of
// the declaration's own default.
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

}  // namespace
