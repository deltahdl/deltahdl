// §23.10.2.2: Parameter value assignment by name

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

namespace {

TEST(ParserAnnexA0411, ElaborationParamOverrideNamed) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(16)) u0(.d(16'd0));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "W");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

// --- program_instantiation: with named parameter_value_assignment ---
TEST(ParserAnnexA0413, ProgramInstWithNamedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(16)) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection23, ModuleInstNamedParamOverride) {
  auto r = Parse(
      "module top;\n"
      "  sub #(.WIDTH(8), .DEPTH(16)) u1(.a(w1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
}

}  // namespace
