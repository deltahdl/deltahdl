// §25.7: Tasks and functions in interfaces

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
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

namespace {

// interface_or_generate_item ::= { attribute_instance } extern_tf_declaration
// extern_tf_declaration ::= extern method_prototype ;
// Verify extern function prototype inside an interface.
TEST(SourceText, ExternFunctionPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void compute(input int x);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto *ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(ifc->items[0]->name, "compute");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  // Prototype only — no body statements.
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration ::= extern method_prototype ;
// method_prototype ::= task_prototype — extern task prototype.
TEST(SourceText, ExternTaskPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto *ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration ::= extern forkjoin task_prototype ;
TEST(SourceText, ExternForkjoinTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task parallel_run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto *ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "parallel_run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->is_forkjoin);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

}  // namespace
