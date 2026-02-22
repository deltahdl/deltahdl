// §18.13: Random number system functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "synthesis/synth_lower.h"

using namespace delta;

struct SynthFixture {
  SourceManager src_mgr;
  DiagEngine diag{src_mgr};
  Arena arena;
};

static const RtlirModule *ElaborateSrc(SynthFixture &f,
                                       const std::string &src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Lexer lexer(f.src_mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

namespace {

TEST(SynthLower, RejectSystemCall) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m;\n"
                           "  reg x;\n"
                           "  always_comb begin x = $random; end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  EXPECT_EQ(aig, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
