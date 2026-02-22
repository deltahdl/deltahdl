// Tests for A.7.5 — System timing checks — Elaboration

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

struct ElabA705Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA705Fixture &f) {
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
// A.7.5 system_timing_check — Elaboration
// =============================================================================

// $setup timing check elaborates
TEST(ElabA705, SetupTimingCheckElaborates) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    $setup(data, posedge clk, 10);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// $hold timing check elaborates
TEST(ElabA705, HoldTimingCheckElaborates) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    $hold(posedge clk, data, 5);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// All 12 system_timing_check alternatives in one specify block
TEST(ElabA705, AllTwelveCheckTypesElaborate) {
  ElabA705Fixture f;
  auto *design =
      ElaborateSrc("module m;\n"
                   "  specify\n"
                   "    $setup(d, posedge clk, 10);\n"
                   "    $hold(posedge clk, d, 5);\n"
                   "    $setuphold(posedge clk, d, 10, 5);\n"
                   "    $recovery(posedge clk, rst, 8);\n"
                   "    $removal(posedge clk, rst, 3);\n"
                   "    $recrem(posedge clk, rst, 8, 3);\n"
                   "    $skew(posedge clk1, negedge clk2, 3);\n"
                   "    $timeskew(posedge clk1, posedge clk2, 5);\n"
                   "    $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
                   "    $period(posedge clk, 50);\n"
                   "    $width(posedge clk, 20);\n"
                   "    $nochange(posedge clk, d, 0, 0);\n"
                   "  endspecify\n"
                   "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Timing checks mixed with path declarations elaborate
TEST(ElabA705, TimingChecksMixedWithPathsElaborate) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    (a => b) = 5;\n"
                              "    $setup(d, posedge clk, 10);\n"
                              "    (c *> e) = 10;\n"
                              "    $hold(posedge clk, d, 5);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Timing checks with specparam declarations elaborate
TEST(ElabA705, TimingChecksWithSpecparamsElaborate) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    specparam tSetup = 10;\n"
                              "    $setup(d, posedge clk, tSetup);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Multiple specify blocks with timing checks elaborate
TEST(ElabA705, MultipleSpecifyBlocksElaborate) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  specify\n"
                              "    $setup(d, posedge clk, 10);\n"
                              "  endspecify\n"
                              "  specify\n"
                              "    $hold(posedge clk, d, 5);\n"
                              "  endspecify\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
