#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ModuleInstanceParameterAssignment,
     OverrideSuppliesValueToInstanceParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
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
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ModuleInstanceParameterAssignment, UnknownParameterNameProducesError) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.NOPE(8)) u0();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'NOPE'", 4,
                            "23.10.2.2"));
}

TEST(ModuleInstanceParameterAssignment,
     PartialOverrideLeavesUnspecifiedAtDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int A = 1,\n"
      "               parameter int B = 2,\n"
      "               parameter int C = 3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.B(20)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 3u);
  EXPECT_EQ(u0->params[0].name, "A");
  EXPECT_EQ(u0->params[0].resolved_value, 1);
  EXPECT_EQ(u0->params[1].name, "B");
  EXPECT_EQ(u0->params[1].resolved_value, 20);
  EXPECT_EQ(u0->params[2].name, "C");
  EXPECT_EQ(u0->params[2].resolved_value, 3);
}

TEST(ModuleInstanceParameterAssignment, EmptyExpressionRetainsDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 7)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W()) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_EQ(u0->params[0].resolved_value, 7);
}

// The value linked to a named parameter is an expression evaluated in the
// instantiating module's scope, not merely a literal. A parameter of the
// enclosing module is a valid constant form for that value (§6.20.2).
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideValueMayBeParentParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top #(parameter int P = 12)();\n"
      "  child #(.W(P)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 12);
}

// A localparam of the enclosing module is another constant form (§6.20.2) that
// may supply a named override value; it flows through the same scope-evaluation
// path as a literal or parameter but is declared differently.
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideValueMayBeParentLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int L = 9;\n"
      "  child #(.W(L)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "W");
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 9);
}

// Named assignment also binds a TYPE parameter (§6.20.3): the operand of the
// override is a type rather than a value expression, taking a distinct code
// path. The chosen type propagates to declarations inside the child, so a
// variable typed by the parameter takes the overridden type's width.
TEST(ModuleInstanceParameterAssignment, TypeParameterNamedOverrideSelectsType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter type T = byte)();\n"
      "  T sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.T(int)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  const RtlirVariable* sig = nullptr;
  for (const auto& v : u0->variables)
    if (v.name == "sig") sig = &v;
  ASSERT_NE(sig, nullptr);
  // int is 32 bits; the default byte would have been 8.
  EXPECT_EQ(sig->width, 32u);
}

TEST(ModuleInstanceParameterAssignment,
     DifferentInstancesMayUseDifferentMethods) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(8) u_ordered();\n"
      "  child #(.W(8)) u_named();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  auto* u_ordered = top->children[0].resolved;
  auto* u_named = top->children[1].resolved;
  ASSERT_NE(u_ordered, nullptr);
  ASSERT_NE(u_named, nullptr);
  ASSERT_EQ(u_ordered->params.size(), 1u);
  ASSERT_EQ(u_named->params.size(), 1u);
  EXPECT_EQ(u_ordered->params[0].resolved_value, 8);
  EXPECT_EQ(u_named->params[0].resolved_value, 8);
}

// §6.20.4 rules that a local parameter cannot be modified by an instance
// parameter value assignment, so a named assignment naming one names nothing
// §23.10.2.2 lets an instantiation override. The report that says so names the
// subclause, which lets a caller learn which rule was enforced without matching
// the wording of the message.
TEST(ModuleInstanceParameterAssignment,
     LocalparamIsNotOverridableNames23_10_2_2) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int W = 4, localparam int L = 8)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.L(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "has no parameter", 4, "23.10.2.2"));
}

// The resolved value of parameter `name` of top's one child instance, or -1
// where the design holds no such instance or parameter or the fold left it
// unresolved.
int64_t ChildParamValue(RtlirDesign* design, std::string_view name) {
  if (design->top_modules.empty() || design->top_modules[0]->children.empty())
    return -1;
  const auto* child = design->top_modules[0]->children[0].resolved;
  if (child == nullptr) return -1;
  for (const auto& p : child->params) {
    if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
  }
  return -1;
}

// Q of c, whose `logic [TOP:0] P` follows its `parameter int TOP = 15` in the
// parameter port list and whose Q is set from P, instantiated once in top
// with `assignment` as the instance's parameter value assignment.
int64_t ChildQUnder(std::string_view assignment, ElabFixture& f) {
  std::string src =
      "module c #(parameter int TOP = 15, parameter logic [TOP:0] P = 0);\n"
      "  localparam int Q = P;\n"
      "endmodule\n"
      "module top;\n"
      "  c #(";
  src += assignment;
  src += ") u();\nendmodule\n";
  auto* design = ElaborateSrc(src, f, "top");
  if (design == nullptr) return -1;
  return ChildParamValue(design, "Q");
}

// §23.10.2 (printed page 766) with §6.20.2 (printed 126): a named parameter
// value assignment gives the parameter the value of an expression written in
// the instantiating module, converted to the range of its declaration, and
// that range may be written in terms of an earlier parameter of the same
// list: `logic [TOP:0] P` under `parameter int TOP = 15` is 16 bits, so
// `.P(16'hABCD)` gives P every bit of the literal and Q, set from P in the
// child, reads 0xABCD. The range is sized with TOP in scope, as the port
// list folds each parameter after the ones before it; cut to a width folded
// without TOP, the vector atom's one bit, P would be 1.
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideIsConvertedToARangeWrittenAsAnEarlierParameter) {
  ElabFixture f;
  EXPECT_EQ(ChildQUnder(".P(16'hABCD)", f), 0xABCD);
  EXPECT_FALSE(f.has_errors);
}

// The same list with TOP overridden in the same assignment: §23.10.2 has the
// later parameter's range follow the earlier one's new value, so `.TOP(7)`
// makes P eight bits and `.P(16'hABCD)` is cut to 0xCD, which Q reads.
TEST(ModuleInstanceParameterAssignment,
     NamedOverrideIsConvertedToARangeTheSameAssignmentOverrides) {
  ElabFixture f;
  EXPECT_EQ(ChildQUnder(".TOP(7), .P(16'hABCD)", f), 0xCD);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
