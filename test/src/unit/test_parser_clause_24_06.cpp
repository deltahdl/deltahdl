// §24.6: Program-wide space and anonymous programs

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

// anonymous_program: program ; { ... } endprogram
TEST(SourceText, AnonymousProgram) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// anonymous_program_item: class_declaration, interface_class_declaration
TEST(SourceText, AnonymousProgramClasses) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    class C; endclass\n"
      "    interface class IC;\n"
      "      pure virtual function void f();\n"
      "    endclass\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// anonymous_program_item: covergroup, class_constructor, ;
TEST(SourceText, AnonymousProgramMisc) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    covergroup cg; endgroup\n"
      "    function MyClass::new(); endfunction\n"
      "    ;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// anonymous_program at file scope (outside package)
TEST(SourceText, AnonymousProgramTopLevel) {
  auto r = Parse(
      "program;\n"
      "  function void f(); endfunction\n"
      "  class C; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
