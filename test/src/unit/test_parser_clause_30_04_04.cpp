#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// §30.4.4 State-dependent paths — Syntax 30-5.
//
// This clause owns the grammar production
//   state_dependent_path_declaration ::=
//       if ( module_path_expression ) simple_path_declaration
//     | if ( module_path_expression ) edge_sensitive_path_declaration
//     | ifnone simple_path_declaration
// and the prose statement that a state-dependent path description is composed
// of a conditional expression, a module path description, and a delay
// expression.
//
// The detailed conditional-expression operand/operator rules (§30.4.4.1), the
// simple/edge-sensitive descriptions (§30.4.4.2/§30.4.4.3) and the ifnone
// semantics (§30.4.4.4) belong to the descendant subclauses and are exercised
// in their own canonical files. The tests below observe only the grammar
// production itself: the parser recognizing each of the three right-hand-side
// alternatives and decomposing it into condition + path + delay.
//
// Production code: src/parser/parser_specify.cpp — ParseSpecifyItem (the `if`
// and `ifnone` branches), ParseConditionalPathDecl, ParseIfnonePathDecl.

namespace {

// Alternative 1: if ( module_path_expression ) simple_path_declaration.
// The conditional expression, the module path, and the delay are all captured.
TEST(StateDependentPathSyntax, IfGuardWrapsSimplePath) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if (en) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  // The three structural items of a state-dependent path description:
  ASSERT_NE(si->path.condition, nullptr);    // conditional expression
  ASSERT_EQ(si->path.src_ports.size(), 1u);  // module path description
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);  // delay expression
  // A guarded simple path is neither edge-sensitive nor an ifnone default.
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNone);
  EXPECT_FALSE(si->path.is_ifnone);
}

// Alternative 2: if ( module_path_expression ) edge_sensitive_path_declaration.
// The same `if (...)` guard wraps an edge-sensitive path description.
TEST(StateDependentPathSyntax, IfGuardWrapsEdgeSensitivePath) {
  auto r = Parse(
      "module m(input clk, input d, input en, output q);\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = (3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  ASSERT_NE(si->path.condition, nullptr);           // conditional expression
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);  // edge-sensitive path
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.delays.size(), 2u);  // delay expression
}

// Alternative 3: ifnone simple_path_declaration.
// The default form carries no conditional expression and is flagged ifnone.
TEST(StateDependentPathSyntax, IfnoneWrapsSimplePath) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    ifnone (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);           // ifnone alternative
  EXPECT_EQ(si->path.condition, nullptr);    // no conditional expression
  ASSERT_EQ(si->path.src_ports.size(), 1u);  // module path description
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  ASSERT_EQ(si->path.delays.size(), 1u);  // delay expression
}

// Error case for alternatives 1 and 2: the module_path_expression must be
// enclosed in parentheses after `if`. A bare condition with no parentheses is
// not a well-formed state_dependent_path_declaration, so the parser reports an
// error rather than accepting it.
TEST(StateDependentPathSyntax, IfGuardRequiresParenthesizedCondition) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if en (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
