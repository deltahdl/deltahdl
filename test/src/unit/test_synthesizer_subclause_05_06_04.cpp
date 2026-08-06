#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "preprocessor/preprocessor.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

const RtlirModule* PreprocessAndElaborate(SynthFixture& f,
                                          const std::string& src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Preprocessor preproc(f.src_mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.src_mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.src_mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  cu->default_nettype = preproc.DefaultNetType();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

TEST(CompilerDirectiveSynthesis, DirectivePersistsToSynthesizedModule) {
  SynthFixture f;
  const auto* mod = PreprocessAndElaborate(
      f,
      "`define WIDTH 4\n"
      "module ignored; endmodule\n"
      "module m(input logic [`WIDTH-1:0] a, output logic [`WIDTH-1:0] y);\n"
      "  assign y = a;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  EXPECT_NE(aig, nullptr);
}

TEST(CompilerDirectiveSynthesis, MacroIsolatedBetweenCus) {
  {
    SynthFixture f1;
    const auto* mod = PreprocessAndElaborate(
        f1,
        "`define ONLY 4\n"
        "module a(input logic [`ONLY-1:0] x, output logic [`ONLY-1:0] y);\n"
        "  assign y = x;\n"
        "endmodule\n");
    ASSERT_NE(mod, nullptr);
  }
  SynthFixture f2;
  const auto* mod2 = PreprocessAndElaborate(
      f2,
      "module b(input logic [`ONLY-1:0] x, output logic [`ONLY-1:0] y);\n"
      "  assign y = x;\n"
      "endmodule\n");

  EXPECT_TRUE(mod2 == nullptr || f2.diag.HasErrors());
}

}  // namespace
