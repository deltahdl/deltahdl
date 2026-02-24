// §14.3: Clocking block declaration

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

struct ElabA611Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA611Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

namespace {

// =============================================================================
// A.6.11 Clocking block — Elaboration
// =============================================================================
// Plain clocking block declaration elaborates
TEST(ElabA611, PlainClockingBlockElaborates) {
  ElabA611Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Clocking block with multiple direction groups elaborates
TEST(ElabA611, MultipleDirectionGroupsElaborate) {
  ElabA611Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "    inout c;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Clocking block with default skew elaborates
TEST(ElabA611, DefaultSkewElaborates) {
  ElabA611Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Multiple clocking blocks in same module elaborate
TEST(ElabA611, MultipleClockingBlocksElaborate) {
  ElabA611Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  clocking cb1 @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cb2 @(posedge clk2);\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
