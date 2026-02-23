// §27.4: Loop generate constructs

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

static ModuleItem *FindItemByKind(const std::vector<ModuleItem *> &items,
                                  ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

struct ModportPortExpected {
  Direction dir;
  const char *name;
};

namespace {

TEST(Parser, GenerateFor) {
  auto r = Parse(
      "module t;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

struct ParseResult303 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult303 Parse(const std::string &src) {
  ParseResult303 result;
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

static ModuleItem *FindItemByKind(ParseResult303 &r, ModuleItemKind kind) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static bool HasItemOfKind(const std::vector<ModuleItem *> &items,
                          ModuleItemKind kind) {
  for (const auto *item : items)
    if (item->kind == kind) return true;
  return false;
}

static bool HasAlwaysOfKind(const std::vector<ModuleItem *> &items,
                            AlwaysKind kind) {
  for (const auto *item : items)
    if (item->kind == ModuleItemKind::kAlwaysBlock && item->always_kind == kind)
      return true;
  return false;
}

// §3.3 Generate blocks
TEST(ParserClause03, Cl3_3_GenerateBlocks) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter N = 4) ();\n"
              "  genvar i;\n"
              "  generate\n"
              "    for (i = 0; i < N; i = i + 1) begin : gen_loop\n"
              "      logic [7:0] data;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
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

// 14. Generate block scope (for-generate)
TEST(ParserClause03, Cl3_13_GenerateForBlockScope) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    logic [7:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen);
}

}  // namespace
