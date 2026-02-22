// §9.2.2.2: Combinational logic always_comb procedure

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "synthesis/aig.h"
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
  if (!cu || cu->modules.empty())
    return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty())
    return nullptr;
  return design->top_modules[0];
}

namespace {

TEST(SynthLower, AlwaysCombSimpleAssign) {
  SynthFixture f;
  auto *mod = ElaborateSrc(f, "module m(input a, input b, output reg y);\n"
                              "  always_comb begin\n"
                              "    y = a & b;\n"
                              "  end\n"
                              "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AlwaysCombIfElse) {
  SynthFixture f;
  auto *mod =
      ElaborateSrc(f, "module m(input sel, input a, input b, output reg y);\n"
                      "  always_comb begin\n"
                      "    if (sel) y = a;\n"
                      "    else y = b;\n"
                      "  end\n"
                      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 3);
  EXPECT_EQ(aig->outputs.size(), 1);
}

TEST(SynthLower, AlwaysCombCaseStmt) {
  SynthFixture f;
  auto *mod =
      ElaborateSrc(f, "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                      "  always_comb begin\n"
                      "    case (sel)\n"
                      "      2'b00: y = 2'b01;\n"
                      "      2'b01: y = 2'b10;\n"
                      "      default: y = 2'b00;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto *aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

} // namespace
