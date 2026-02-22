#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabA610Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA610Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

}  // namespace

// =============================================================================
// A.6.10 Assertion statements — Elaboration
// =============================================================================

// simple_immediate_assert_statement elaborates
TEST(ElabA610, SimpleAssertElaborates) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial assert(1) $display(\"pass\"); else $display(\"fail\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// simple_immediate_assume_statement elaborates
TEST(ElabA610, SimpleAssumeElaborates) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial assume(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// simple_immediate_cover_statement elaborates
TEST(ElabA610, SimpleCoverElaborates) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial cover(1) $display(\"covered\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// deferred_immediate_assert_statement elaborates
TEST(ElabA610, DeferredAssertElaborates) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// concurrent assert property at module level elaborates
TEST(ElabA610, AssertPropertyElaborates) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  assert property (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// multiple assertion types in same module elaborate
TEST(ElabA610, MixedAssertionsElaborate) {
  ElabA610Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    assert(1);\n"
      "    assume(1);\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
