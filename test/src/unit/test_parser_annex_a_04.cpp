#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

} // namespace

// =============================================================================
// A.4 -- Instantiations
// =============================================================================

TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ParserAnnexA, A4ModuleInstNamed) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

TEST(ParserAnnexA, A4ModuleInstWithParams) {
  auto r = Parse("module m; sub #(8, 4) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateForBlock) {
  auto r = Parse("module m;\n"
                 "  genvar i;\n"
                 "  for (i = 0; i < 4; i = i + 1) begin\n"
                 "    wire w;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor)
      found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateIfElse) {
  auto r = Parse("module m;\n"
                 "  if (WIDTH > 8) begin\n"
                 "    wire [15:0] bus;\n"
                 "  end else begin\n"
                 "    wire [7:0] bus;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found = true;
      EXPECT_NE(item->gen_else, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateCase) {
  auto r = Parse("module m;\n"
                 "  case (WIDTH)\n"
                 "    8: begin\n"
                 "      wire [7:0] d;\n"
                 "    end\n"
                 "    default: begin\n"
                 "      wire [31:0] d;\n"
                 "    end\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_EQ(item->gen_case_items.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateRegion) {
  auto r = Parse("module m;\n"
                 "  generate\n"
                 "    wire w;\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
