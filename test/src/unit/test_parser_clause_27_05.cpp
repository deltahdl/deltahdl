// §27.5: Conditional generate constructs

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// These unit tests embed SystemVerilog source as inline C++ string literals
// rather than loading external .sv files. This is intentional: each test is
// fully self-contained with the input source and structural assertions in one
// place, so a reader can understand what is being tested without
// cross-referencing a second file. When a test fails, the input and expected
// AST shape are visible together in the test output. Integration and
// conformance testing uses external .sv files instead: the CHIPS Alliance
// sv-tests suite validates broad language coverage, and the sim-tests under
// test/src/e2e/ verify end-to-end simulation behavior against .expected output
// files. This inline pattern is standard practice for compiler parser unit
// tests (used by LLVM, Clang, rustc, etc.).
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

struct StructMemberExpected {
  const char *name;
  DataTypeKind type_kind;
};

static void VerifyGenerateCaseItem(const GenerateCaseItem &ci, size_t idx,
                                   bool expect_default,
                                   size_t expect_pattern_count) {
  EXPECT_EQ(ci.is_default, expect_default) << "case item " << idx;
  EXPECT_EQ(ci.patterns.size(), expect_pattern_count) << "case item " << idx;
  EXPECT_FALSE(ci.body.empty()) << "case item " << idx;
}

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

namespace {

TEST(Parser, GenerateIf) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_body.empty());
}

TEST(Parser, GenerateIfElse) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end else begin\n"
      "    assign a = c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_else, nullptr);
}

TEST(Parser, GenerateCase) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    2: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_NE(item->gen_cond, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  VerifyGenerateCaseItem(item->gen_case_items[0], 0, false, 1);
  VerifyGenerateCaseItem(item->gen_case_items[1], 1, false, 1);
}

TEST(Parser, GenerateCaseDefault) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "    default: begin\n"
      "      assign a = c;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_TRUE(item->gen_case_items[1].is_default);
}

TEST(Parser, GenerateCaseMultiPattern) {
  auto r = Parse(
      "module t;\n"
      "  case (WIDTH)\n"
      "    1, 2: begin\n"
      "      assign a = b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 1);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
}

TEST(Parser, GenerateCaseInRegion) {
  auto r = Parse(
      "module t;\n"
      "  generate\n"
      "    case (WIDTH)\n"
      "      1: begin\n"
      "        assign a = b;\n"
      "      end\n"
      "    endcase\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateCase) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

struct ParseResult313 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string &src) {
  ParseResult313 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem *> &items,
                                 ModuleItemKind kind, const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem *> &items,
                         const std::string &name) {
  for (const auto *item : items)
    for (const auto &attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

// 15. Labeled generate blocks (if-generate)
TEST(ParserClause03, Cl3_13_LabeledIfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter USE_FAST = 1;\n"
      "  if (USE_FAST) begin : fast_path\n"
      "    logic [7:0] result;\n"
      "  end else begin : slow_path\n"
      "    logic [15:0] result;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  bool found_gen_if = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen_if = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen_if);
}

}  // namespace
