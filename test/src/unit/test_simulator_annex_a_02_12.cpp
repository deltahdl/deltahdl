#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

// §A.2.12 end-to-end coverage. The productions of §A.2.12 (let_declaration,
// let_port_item, let_formal_type, let_expression, let_list_of_arguments,
// let_actual_arg) are syntactic, but the let construct they define is consumed
// by the whole pipeline: the declaration's `= expression` right-hand side and
// each let_actual_arg are real §A.8.3 expressions, and a typed let_formal_type
// is a real §A.2.2.1 data_type. These tests build a let from real source
// syntax, invoke it, and observe the simulated result — i.e. observe the
// productions being expanded by production code (EvalLetExpansion), not merely
// parsed.

namespace {

// let_declaration with no port list, referenced as a bare let_expression
// (let_identifier alone). The right-hand side is a real literal expression;
// the value flows through expansion into the assigned variable.
TEST(LetSim, NoPortLetExpandsToRhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let answer = 8'd42;\n"
      "  initial x = answer;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

// let_expression with positional let_actual_arg entries, each a literal
// §A.8.3 expression, substituted into the let body.
TEST(LetSim, PositionalLiteralActualsSubstituted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let sum(a, b) = a + b;\n"
      "  initial x = sum(8'd5, 8'd9);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 14u}});
}

// let_actual_arg ::= expression: an actual may be a compound expression built
// from real signal references and arithmetic, not just a literal. This drives
// the non-literal §A.8.3 expression path into the same let.
TEST(LetSim, CompoundExpressionActualsSubstituted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, z;\n"
      "  let sum(a, b) = a + b;\n"
      "  initial begin\n"
      "    y = 8'd2;\n"
      "    z = 8'd4;\n"
      "    x = sum(y + 8'd1, z);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

// let_formal_type ::= data_type_or_implicit — the explicit data_type form. The
// formal's packed §A.2.2.1 data_type governs its width, so a wider actual is
// narrowed to the formal type before the body evaluates.
TEST(LetSim, TypedFormalNarrowsActualToDataTypeWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let low(logic [3:0] v) = v;\n"
      "  initial x = low(8'hAB);\n"
      "endmodule\n",
      f);
  // 8'hAB truncated to the 4-bit formal is 4'hB == 11.
  LowerRunAndCheck(f, design, {{"x", 11u}});
}

// let_formal_type ::= untyped — the untyped alternative imposes no width, so
// the actual passes through unchanged.
TEST(LetSim, UntypedFormalPassesActualThrough) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let same(untyped a) = a;\n"
      "  initial x = same(8'hC8);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 200u}});
}

// let_port_item ::= ... [ = expression ] — when the invocation omits the
// actual, the formal's default expression is evaluated and used in the body.
TEST(LetSim, PortDefaultUsedWhenActualOmitted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let scaled(int d = 5) = d * 2;\n"
      "  initial x = scaled();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

// let_list_of_arguments, the fully-named alternative: each formal is bound by
// name and substituted into the body regardless of listing order.
TEST(LetSim, NamedActualsBindByName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  let mux(sel, d0, d1) = sel ? d1 : d0;\n"
      "  initial x = mux(.sel(1'b1), .d0(8'd10), .d1(8'd20));\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 20u}});
}

}  // namespace
