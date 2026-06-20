#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

SpecifyItem* FindPathpulseInSpecify(ModuleDecl* mod) {
  auto* spec = FindSpecifyBlock(mod->items);
  if (spec == nullptr) return nullptr;
  for (auto* it : spec->specify_items) {
    if (it->kind == SpecifyItemKind::kSpecparam && it->is_pathpulse) return it;
  }
  return nullptr;
}

// Syntax 30-7 first alternative (PATHPULSE$ = ( reject )): a lone reject limit
// produces a module-wide pathpulse specparam with no error limit.
TEST(PulseControlSpecparamParsing, PathpulseRejectOnlyExtraction) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_pathpulse);
  EXPECT_TRUE(item->pathpulse_input.empty());
  EXPECT_TRUE(item->pathpulse_output.empty());
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_EQ(item->pathpulse_error, nullptr);
}

// Syntax 30-7 second alternative
// (PATHPULSE$ input $ output = ( ... )): the input and output terminal
// descriptors are captured for a path-specific specparam.
TEST(PulseControlSpecparamParsing, PathpulseExtractsInputOutputTerminals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$clk$q = (3, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_pathpulse);
  EXPECT_EQ(item->pathpulse_input, "clk");
  EXPECT_EQ(item->pathpulse_output, "q");
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_NE(item->pathpulse_error, nullptr);
}

// limit_value ::= constant_mintypmax_expression: each limit may be a full
// min:typ:max triple.
TEST(PulseControlSpecparamParsing, PathpulseMintypmaxExpressionPreserved) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->pathpulse_reject, nullptr);
  ASSERT_NE(item->pathpulse_error, nullptr);
  EXPECT_EQ(item->pathpulse_reject->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->pathpulse_error->kind, ExprKind::kMinTypMax);
}

// The PATHPULSE$ specparam form is also accepted in a module-level specparam
// declaration, exercising the separate specparam-declaration parse path.
TEST(PulseControlSpecparamParsing, PulseControlSpecparamModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  specparam PATHPULSE$ = (2, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §30.7.1: the module path input and output terminals may not be a bit-select
// or part-select of a vector. Such a terminal cannot form a PATHPULSE$
// identifier (the brackets terminate the identifier), so the declaration is
// rejected.
TEST(PulseControlSpecparamParsing, TerminalCannotBeBitOrPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$a[0]$b = (1, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
