// §31.3.1: $setup

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

namespace {

// =============================================================================
// A.7.5 system_timing_check — Elaboration
// =============================================================================
// $setup timing check elaborates
TEST(ElabA705, SetupTimingCheckElaborates) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Timing checks with specparam declarations elaborate
TEST(ElabA705, TimingChecksWithSpecparamsElaborate) {
  ElabA705Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tSetup = 10;\n"
      "    $setup(d, posedge clk, tSetup);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA70501Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA70501Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.7.5.1 $setup_timing_check — command structure
// =============================================================================
TEST(ElabA70501, SetupWithNotifierElaborates) {
  ElabA70501Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA70503Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA70503Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// =============================================================================
// A.7.5.3 Elab — specify_terminal_descriptor with ranges
// =============================================================================
// Terminal with bit select elaborates
TEST(ElabA70503, TerminalBitSelectElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with posedge elaborates
TEST(ElabA70503, TimingCheckEventPosedgeElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — timing_check_event with edge controls
// =============================================================================
// timing_check_event with no edge elaborates
TEST(ElabA70503, TimingCheckEventNoEdgeElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
