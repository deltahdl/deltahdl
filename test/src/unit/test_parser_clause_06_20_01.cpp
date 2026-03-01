// §6.20.1: Parameter declaration syntax

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfSpecparamAssignmentsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50, tHOLD = 10; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// parameter_port_list: data_type list_of_param_assignments (no keyword)
TEST(SourceText, ParamPortDataTypeForm) {
  auto r = Parse("module m #(int WIDTH = 8); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "WIDTH");
}

// parameter_port_list: mixed forms
TEST(SourceText, ParamPortMixedForms) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 2,\n"
      "           type T = logic, int C = 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
  EXPECT_EQ(r.cu->modules[0]->params[2].first, "T");
  EXPECT_EQ(r.cu->modules[0]->params[3].first, "C");
}

TEST(ParserA83, ParamExprBinaryOp) {
  auto r = Parse(
      "module m #(parameter int P = 2 * 8);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind, ExprKind::kBinary);
}

// --- list_of_param_assignments ---
// param_assignment { , param_assignment }
TEST(ParserA23, ListOfParamAssignmentsSingle) {
  auto r = Parse("module m; parameter int A = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserA23, ListOfParamAssignmentsMultiple) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA24, ParamAssignmentNoDefault) {
  // Parameter in module header without default
  auto r = Parse("module m #(parameter int P); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- type_assignment ---
// type_identifier [ = data_type_or_incomplete_class_scoped_type ]
TEST(ParserA24, TypeAssignmentWithDefault) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

}  // namespace
