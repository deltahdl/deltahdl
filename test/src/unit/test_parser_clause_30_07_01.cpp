#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Locate the first PATHPULSE$ specparam inside a module's specify block, or
// at module scope. Returns nullptr when none exists.
SpecifyItem* FindPathpulseInSpecify(ModuleDecl* mod) {
  auto* spec = FindSpecifyBlock(mod->items);
  if (spec == nullptr) return nullptr;
  for (auto* it : spec->specify_items) {
    if (it->kind == SpecifyItemKind::kSpecparam && it->is_pathpulse) return it;
  }
  return nullptr;
}

TEST(PulseControlSpecparamParsing, PulseControlSpecparamRejectOnly) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PulseControlSpecparamParsing, PulseControlSpecparamRejectAndError) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PulseControlSpecparamParsing, PulseControlSpecparamPathSpecific) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$in1$out1 = (3, 7);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PulseControlSpecparamParsing, PulseControlSpecparamModuleLevel) {
  auto r = Parse(
      "module m;\n"
      "  specparam PATHPULSE$ = (2, 5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PulseControlSpecparamParsing, LimitValueMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- AST extraction: PATHPULSE$ must expose its input/output terminals and
// both limit expressions so downstream stages can apply §30.7.1 semantics.

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

TEST(PulseControlSpecparamParsing, PathpulseBothLimitsExtracted) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam PATHPULSE$ = (2, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindPathpulseInSpecify(r.cu->modules[0]);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_pathpulse);
  EXPECT_NE(item->pathpulse_reject, nullptr);
  EXPECT_NE(item->pathpulse_error, nullptr);
}

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

}  // namespace
