// §7.3.1: Packed unions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"

using namespace delta;

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// =============================================================================
// §7.3.1: Packed union validation
// =============================================================================
TEST(Elaboration, HardPackedUnion_SameWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, HardPackedUnion_DifferentWidth_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, SoftPackedUnion_DifferentWidth_OK) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  union soft { logic [7:0] a; logic [15:0] b; } u;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
