// §30.4.2: Simple module paths

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

namespace {

// Specify block with path declaration elaborates
TEST(ElabA701, SpecifyBlockWithPathElaborates) {
  ElabA701Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

struct ElabA703Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA703Fixture &f) {
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
// A.7.3 Specify block terminals — Elaboration
// =============================================================================
// Terminal with bit-select elaborates
TEST(ElabA703, TerminalBitSelectElaborates) {
  ElabA703Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[3] => b[0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Terminal with part-select range elaborates
TEST(ElabA703, TerminalPartSelectElaborates) {
  ElabA703Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[7:0] => b[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Terminal with indexed part-select elaborates
TEST(ElabA703, TerminalIndexedPartSelectElaborates) {
  ElabA703Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a[0+:4] => b[7-:4]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Terminal with dotted interface.port elaborates
TEST(ElabA703, TerminalDottedElaborates) {
  ElabA703Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (intf.sig => intf.out) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

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

// =============================================================================
// A.7.2 Specify path declarations — Elaboration
// =============================================================================
// Simple parallel path elaborates without errors
TEST(ElabA702, SimpleParallelPathElaborates) {
  ElabA702Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
