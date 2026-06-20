#include "fixture_elaborator.h"

using namespace delta;

namespace {

struct GenElab {
  ElabFixture f;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;
};

GenElab RunElaboration(const std::string& src, std::string_view top = "") {
  GenElab r;
  auto fid = r.f.mgr.AddFile("<test>", src);
  Lexer lexer(r.f.mgr.FileContent(fid), fid, r.f.diag);
  Parser parser(lexer, r.f.arena, r.f.diag);
  r.cu = parser.Parse();
  if (!r.cu) return r;
  auto name = top.empty() ? r.cu->modules.back()->name : top;
  Elaborator elab(r.f.arena, r.f.diag, r.cu);
  r.design = elab.Elaborate(name);
  r.f.has_errors = r.f.diag.HasErrors();
  return r;
}

int CountVariablesNamed(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
}

// §27.3: the expressions in a generate scheme are constant expressions
// resolved against the enclosing scope (see §23.9). A generate-if whose
// condition is a module parameter elaborates cleanly and instantiates the
// selected block's declarations into the module.
TEST(GenerateConstructSyntax, ConstantConditionFromEnclosingScopeElaborates) {
  auto r = RunElaboration(
      "module top;\n"
      "  parameter P = 1;\n"
      "  if (P == 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 1);
}

// §27.3: all expressions in generate schemes shall be constant expressions,
// deterministic at elaboration time. A condition that depends on a runtime
// variable is not constant, and the elaborator flags it.
TEST(GenerateConstructSyntax, NonConstantGenerateSchemeIsDiagnosed) {
  auto r = RunElaboration(
      "module top;\n"
      "  logic v;\n"
      "  if (v) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_GE(r.f.diag.WarningCount(), 1u);
}

// §27.3: the constant-expression requirement covers every generate-scheme
// expression, including a case-generate selector. A selector that depends on
// a runtime variable is not constant and is flagged.
TEST(GenerateConstructSyntax, NonConstantCaseSelectorIsDiagnosed) {
  auto r = RunElaboration(
      "module top;\n"
      "  logic v;\n"
      "  case (v)\n"
      "    0: begin\n"
      "      logic a;\n"
      "    end\n"
      "    default: begin\n"
      "      logic b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_GE(r.f.diag.WarningCount(), 1u);
}

// §27.3: elaboration of a generate construct results in zero or more
// instances of a generate block. A false condition yields zero, so the
// block's declarations never reach the module.
TEST(GenerateConstructSyntax, FalseConditionYieldsZeroInstances) {
  auto r = RunElaboration(
      "module top;\n"
      "  if (0) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 0);
}

// §27.3: a loop generate construct may produce more than one instance of its
// generate block; each iteration contributes its own copy of the block's
// declarations.
TEST(GenerateConstructSyntax, LoopProducesMultipleInstances) {
  auto r = RunElaboration(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 3; i = i + 1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVariablesNamed(r.design->top_modules[0], 'a'), 3);
}

}  // namespace
