// §22.8: `default_nettype

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

namespace {

TEST(Elaboration, ImplicitNetNone_Error) {
  // `default_nettype none causes undeclared identifier to be an error.
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module top;\n"
                           "  assign w = 1'b1;\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  cu->default_nettype = NetType::kNone;
  Elaborator elab(f.arena, f.diag, cu);
  elab.Elaborate("top");
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
