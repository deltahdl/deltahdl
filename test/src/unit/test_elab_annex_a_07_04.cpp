// Tests for A.7.4 — Specify path delays — Elaboration

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

struct ElabA704Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src,
                                 ElabA704Fixture &f) {
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
// A.7.4 Specify path delays — Elaboration
// =============================================================================

// 6-delay path elaborates
TEST(ElabA704, SixDelayPathElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 12-delay path elaborates
TEST(ElabA704, TwelveDelayPathElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Min:typ:max delay elaborates
TEST(ElabA704, MinTypMaxDelayElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Min:typ:max with 2 delays elaborates
TEST(ElabA704, MinTypMaxTwoDelaysElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 6-delay min:typ:max elaborates
TEST(ElabA704, SixDelayMinTypMaxElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Specparam reference in delay elaborates
TEST(ElabA704, SpecparamDelayElaborates) {
  ElabA704Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3, tFall = 5;\n"
      "    (a => b) = (tRise, tFall);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
