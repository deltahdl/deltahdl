// Tests for A.7.2 — Specify path declarations — Elaboration

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

struct ElabA702Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA702Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

} // namespace

// =============================================================================
// A.7.2 Specify path declarations — Elaboration
// =============================================================================

// Simple parallel path elaborates without errors
TEST(ElabA702, SimpleParallelPathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a => b) = 5;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Simple full path elaborates
TEST(ElabA702, SimpleFullPathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a, b *> c) = 10;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Edge-sensitive path elaborates
TEST(ElabA702, EdgeSensitivePathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (posedge clk => q) = 5;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// State-dependent path (if) elaborates
TEST(ElabA702, StateDependentIfPathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    if (en) (a => b) = 10;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// State-dependent path (ifnone) elaborates
TEST(ElabA702, StateDependentIfnonePathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    ifnone (a => b) = 15;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Path with polarity operator elaborates
TEST(ElabA702, PathWithPolarityElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a + => b) = 5;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Edge-sensitive path with data source elaborates
TEST(ElabA702, EdgeSensitiveWithDataSourceElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (posedge clk => (q : d)) = 5;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// All path types together elaborate
TEST(ElabA702, AllPathTypesElaborate) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a => b) = 5;\n"
                              "    (c, d *> e) = 10;\n"
                              "    (posedge clk => q) = 3;\n"
                              "    if (en) (a => b) = 8;\n"
                              "    ifnone (a => b) = 15;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
