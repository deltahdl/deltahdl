// Tests for A.7.1 — Specify block declaration — Elaboration

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

struct ElabA701Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA701Fixture &f) {
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
// A.7.1 Specify block declaration — Elaboration
// =============================================================================

// Empty specify block elaborates without errors
TEST(ElabA701, EmptySpecifyBlockElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Specify block with path declaration elaborates
TEST(ElabA701, SpecifyBlockWithPathElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a => b) = 5;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Specify block with pulsestyle declaration elaborates
TEST(ElabA701, SpecifyBlockWithPulsestyleElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    pulsestyle_onevent out1;\n"
                              "    pulsestyle_ondetect out2;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Specify block with showcancelled declaration elaborates
TEST(ElabA701, SpecifyBlockWithShowcancelledElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    showcancelled out1;\n"
                              "    noshowcancelled out2;\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Specify block with all five item kinds elaborates
TEST(ElabA701, SpecifyBlockWithAllItemKindsElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    specparam tPD = 5;\n"
                              "    pulsestyle_onevent out1;\n"
                              "    showcancelled out2;\n"
                              "    (a => b) = tPD;\n"
                              "    $setup(data, posedge clk, 10);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
