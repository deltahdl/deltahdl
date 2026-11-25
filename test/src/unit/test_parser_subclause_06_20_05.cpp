#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

using namespace delta;

namespace {

TEST_F(SpecifyParseTest, SpecparamDeclaration) {
  auto* unit = Parse("module m; specparam tRISE = 10; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
}

TEST_F(SpecifyParseTest, SpecparamWithRange) {
  auto* unit = Parse("module m; specparam [31:0] tDELAY = 100; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tDELAY");
}

TEST_F(SpecifyParseTest, MultipleSpecparams) {
  auto* unit =
      Parse("module m; specparam tRISE = 10; specparam tFALL = 12; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[1]->name, "tFALL");
}

TEST_F(SpecifyTest, SpecparamInsideSpecify) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRISE = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(item->param_name, "tRISE");
  EXPECT_NE(item->param_value, nullptr);
}
static bool HasSpecifyItemKind(ModuleItem* spec_block, SpecifyItemKind kind) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == kind) return true;
  }
  return false;
}

TEST(SpecparamParsing, SpecifyBlockWithSpecparam) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (clk => q) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kSpecparam));
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kPathDecl));
}

TEST(SpecparamParsing, SpecparamPackedDim) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam [31:0] tDELAY = 50; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SpecparamParsing, SpecparamMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 1:2:3; endspecify\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SpecparamParsing, ErrorSpecparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100 endspecify\n"
      "endmodule");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endspecify'", 2, "6.20.5"));
}

TEST(SpecparamParsing, CommaSeparatedSpecparamList) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50, tHOLD = 10; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SpecparamParsing, SpecparamWithConstantExpression) {
  auto r = Parse(
      "module m;\n"
      "  specparam tDelay = 2 * 5 + 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(SpecparamParsing, SpecparamReferencingPriorSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specparam tBase = 10;\n"
      "  specparam tDerived = tBase + 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "tBase");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "tDerived");
}

TEST(SpecparamParsing, SpecparamInBothSpecifyAndModuleBody) {
  auto r = Parse(
      "module m;\n"
      "  specparam tSetup = 5;\n"
      "  specify\n"
      "    specparam tHold = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tSetup");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
}

TEST(SpecparamParsing, SpecparamInAGenerateBlockIsReported) {
  auto r = Parse(
      "module t;\n"
      "  if (1) begin : g specparam sp = 1; end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "specparam declaration not allowed inside a "
                            "generate block or region",
                            2, "27.2"));
}

TEST(SpecparamParsing, SpecparamInProceduralCodeIsReported) {
  for (const char* src :
       {"module t;\n  function int f(); specparam sp = 1; return sp;\n"
        "  endfunction\nendmodule\n",
        "module t;\n  initial begin specparam sp = 1; end\nendmodule\n"}) {
    SCOPED_TRACE(src);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
  }
}

TEST(SpecparamParsing, SpecparamInTheModuleBodyAndASpecifyBlockIsAccepted) {
  auto r = Parse(
      "module t;\n"
      "  specparam a = 2, b = a * 3.5;\n"
      "  specify specparam c = b; endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

std::size_t ErrorsIn(const std::vector<Diagnostic>& diags) {
  std::size_t errors = 0;
  for (const Diagnostic& diag : diags) {
    if (diag.severity == DiagSeverity::kError) ++errors;
  }
  return errors;
}

TEST(SpecparamParsing, SpecparamInAClassOrTheCompilationUnitIsReported) {
  for (const char* src : {
           "class C;\n  specparam d = 1;\n  int x;\nendclass\n",
           "class C;\n  specparam [7:0] d = 1, e = 2:3:4;\nendclass\n",
           "virtual class C #(int P = 1);\n  specparam d = P;\nendclass\n",
           "interface class C;\n  specparam d = 1;\nendclass\n",
           "class C; class D;\n  specparam d = 1;\nendclass endclass\n",
           "module t; class C;\n  specparam d = 1;\nendclass endmodule\n",
           "package p; class C;\n  specparam d = 1;\nendclass endpackage\n",
           "int x;\nspecparam d = 1;\nmodule t; endmodule\n",
           "int x;\nspecparam [7:0] d = 1, e = 2:3:4;\nmodule t; endmodule\n",
           "module t; endmodule\nspecparam PATHPULSE$ = (1, 2);\n",
       }) {
    SCOPED_TRACE(src);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags,
                              "specparam declaration must appear inside a "
                              "module or a specify block",
                              2, "6.20.5"));
    EXPECT_EQ(ErrorsIn(r.diags), 1u);
  }
}

TEST(SpecparamParsing, ParameterDeclaredInASpecifyBlockIsReported) {
  for (const char* declaration :
       {"parameter p = 1;", "localparam p = 1;", "parameter int p = 1, q = 2;",
        "localparam [3:0] p = 1;", "parameter type T = int;",
        "localparam type T = logic [3:0];"}) {
    SCOPED_TRACE(declaration);
    auto r = Parse("module t(input a, output b);\n  specify\n    " +
                   std::string(declaration) +
                   "\n    (a => b) = 5;\n  endspecify\nendmodule\n");
    EXPECT_TRUE(ReportedError(
        r.diags, "parameter declaration must appear outside a specify block", 3,
        "6.20.5"));
    EXPECT_EQ(ErrorsIn(r.diags), 1u);
  }
}

TEST(SpecparamParsing, ParameterDeclaredBesideASpecifyBlockIsAccepted) {
  auto r = Parse(
      "module t(input a, output b);\n"
      "  parameter int p = 1;\n"
      "  localparam type T = int;\n"
      "  specify\n"
      "    specparam s = p;\n"
      "    (a => b) = s;\n"
      "  endspecify\n"
      "  localparam [3:0] q = 1;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
