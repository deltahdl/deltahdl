// Tests for A.8.2 — Subroutine calls — Elaboration

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabA82Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA82Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

} // namespace

// =============================================================================
// A.8.2 Subroutine calls — Elaboration
// =============================================================================

// § constant_function_call — function call in parameter context
TEST(ElabA82, ConstantFunctionCallInParam) {
  ElabA82Fixture f;
  auto *design =
      ElaborateSrc("module m;\n"
                   "  function int calc(int n); return n * 2; endfunction\n"
                   "  localparam int P = calc(4);\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § tf_call — function call as expression elaborates
TEST(ElabA82, TfCallAsExprElaborates) {
  ElabA82Fixture f;
  auto *design =
      ElaborateSrc("module m;\n"
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

// § system_tf_call — $clog2 as expression elaborates
TEST(ElabA82, SystemTfCallAsExprElaborates) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [31:0] x;\n"
                              "  initial x = $clog2(256);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § system_tf_call — $bits with expression argument
TEST(ElabA82, SystemTfCallBitsElaborates) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] v;\n"
                              "  logic [31:0] x;\n"
                              "  initial x = $bits(v);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § function_subroutine_call — in continuous assignment
TEST(ElabA82, FunctionCallInContAssign) {
  ElabA82Fixture f;
  auto *design =
      ElaborateSrc("module m;\n"
                   "  wire [7:0] y;\n"
                   "  function logic [7:0] compute(input logic [7:0] a);\n"
                   "    return a + 8'd1;\n"
                   "  endfunction\n"
                   "  assign y = compute(8'd5);\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § method_call — method call elaborates
TEST(ElabA82, MethodCallElaborates) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  initial begin obj.method(); end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § list_of_arguments — named arguments elaborate
TEST(ElabA82, NamedArgsElaborate) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = add(.b(2), .a(1));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § subroutine_call — nested function calls elaborate
TEST(ElabA82, NestedCallsElaborate) {
  ElabA82Fixture f;
  auto *design =
      ElaborateSrc("module m;\n"
                   "  function int f(int n); return n + 1; endfunction\n"
                   "  function int g(int n); return n * 2; endfunction\n"
                   "  logic [31:0] x;\n"
                   "  initial x = f(g(3));\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § void'(function_subroutine_call) — void cast elaborates
TEST(ElabA82, VoidCastElaborates) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  function int foo(); return 1; endfunction\n"
                              "  initial void'(foo());\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § system_tf_call — $display statement elaborates
TEST(ElabA82, SystemTaskDisplayElaborates) {
  ElabA82Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  initial $display(\"hello %d\", 42);\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
