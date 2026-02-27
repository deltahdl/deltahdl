// §13.4.1: Return values and void functions


#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Elaboration: function declaration within module
// ---------------------------------------------------------------------------
TEST(ParserA26, ElabFunctionDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// =============================================================================
// A.6.4 Statements — Elaboration
// =============================================================================
// ---------------------------------------------------------------------------
// Elaboration: function_statement context restrictions
// ---------------------------------------------------------------------------
// §13.4.4: return with value in void function is an error
TEST(ElabA604, VoidFunctionReturnWithValueError) {
  ElabA604Fixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4: non-void function can return a value
TEST(ElabA604, NonVoidFunctionReturnWithValue) {
  ElabA604Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// void'(function_subroutine_call) elaborates without error
TEST(ElabA609, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(); return 1; endfunction\n"
      "  initial void'(foo());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § tf_call — function call as expression elaborates
TEST(ElabA82, TfCallAsExprElaborates) {
  ElabA82Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial x = add_one(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
