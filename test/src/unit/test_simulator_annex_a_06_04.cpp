#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StatementSimSyntax, FunctionBodyStatementExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val();\n"
      "    return 8'd99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_val();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 99u}});
}

// statement_or_null: the bare-semicolon null form must run as a no-op, leaving
// the surrounding statements' effects intact. Driven end-to-end so the parsed
// kNull node is actually scheduled and executed rather than merely parsed.
TEST(StatementSimSyntax, NullStatementIsNoOpAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    ;\n"
      "    x = x + 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 8u}});
}

// statement: the optional block_identifier label wraps a statement_item without
// altering its runtime effect. The assigned value comes from a real A.8.3
// binary expression, observed after simulation.
TEST(StatementSimSyntax, LabeledStatementExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    lbl : x = 8'd4 * 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 8u}});
}

// statement: an attribute_instance prefix must not change the semantics of the
// wrapped statement_item; the subtraction expression still evaluates and
// stores.
TEST(StatementSimSyntax, AttributedStatementExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    (* keep *) x = 8'd9 - 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

// function_statement_or_null: a null statement inside a function body is a
// no-op, so the function still returns its computed value end-to-end.
TEST(StatementSimSyntax, NullStatementInFunctionBodyPreservesResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] compute();\n"
      "    ;\n"
      "    return 8'd6 + 8'd36;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

}  // namespace
