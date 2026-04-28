#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

static std::string PreprocessFile(const std::string& path,
                                  const std::string& src, PreprocFixture& f,
                                  Preprocessor& pp) {
  auto fid = f.mgr.AddFile(path, src);
  return pp.Preprocess(fid);
}

// §5.6.4: "The ` character (the ASCII value 0x60, called grave accent)
// introduces a language construct used to implement compiler directives."
TEST(CompilerDirectivePreprocessor, GraveAccentIntroducesDirective) {
  PreprocFixture f;
  // ASCII 0x60 is the grave accent; spell it explicitly.
  std::string src = std::string("\x60") + "define X 42\n" + "\x60" + "X\n";
  auto result = Preprocess(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("42"), std::string::npos);
}

// §5.6.4: A `define preceded by no grave accent is not a directive — the
// word "define" alone is not consumed as a compiler directive.
TEST(CompilerDirectivePreprocessor, NoGraveAccentNoDirective) {
  PreprocFixture f;
  auto result = Preprocess("define X 42\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // The text passes through unchanged because there is no `\`'.
  EXPECT_NE(result.find("define X 42"), std::string::npos);
}

// §5.6.4: "The compiler behavior dictated by a compiler directive shall take
// effect as soon as the compiler reads the directive."
TEST(CompilerDirectivePreprocessor, DirectiveTakesEffectImmediately) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

// §5.6.4: "The directive shall remain in effect for the rest of the
// compilation unit ... unless a different compiler directive specifies
// otherwise."  State persists across subsequent Preprocess() calls on the
// same Preprocessor (same CU).
TEST(CompilerDirectivePreprocessor, DirectivePersistsAcrossSameCu) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  // A second file with no directives — state must survive.
  PreprocessFile("b.sv", "module m; endmodule\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
}

// §5.6.4: "...unless a different compiler directive specifies otherwise."
TEST(CompilerDirectivePreprocessor, DirectiveOverriddenByLaterDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`default_nettype none\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
  PreprocessFile("b.sv", "`default_nettype wire\n", f, pp);
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

// §5.6.4: "A compiler directive in one description file can, therefore,
// control compilation behavior in multiple description files."
TEST(CompilerDirectivePreprocessor, DefineInOneFileVisibleInAnother) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessFile("a.sv", "`define WIDTH 16\n", f, pp);
  auto result = PreprocessFile("b.sv", "localparam W = `WIDTH;\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("16"), std::string::npos);
}

// §5.6.4: "A compiler directive shall not affect other compilation units."
// A `define in one CU is invisible in another CU.
TEST(CompilerDirectivePreprocessor, MacroDefinedInOneCuInvisibleInOther) {
  // CU1 defines a macro.
  {
    PreprocFixture f;
    Preprocessor cu1(f.mgr, f.diag, {});
    PreprocessFile("cu1.sv", "`define ONLY_IN_CU1 1\n", f, cu1);
    EXPECT_FALSE(f.diag.HasErrors());
  }
  // CU2 — fresh fixture, fresh Preprocessor — the macro must not exist.
  PreprocFixture f2;
  Preprocessor cu2(f2.mgr, f2.diag, {});
  auto result = PreprocessFile(
      "cu2.sv",
      "`ifdef ONLY_IN_CU1\nleaked\n`else\nisolated\n`endif\n", f2, cu2);
  EXPECT_FALSE(f2.diag.HasErrors());
  EXPECT_EQ(result.find("leaked"), std::string::npos);
  EXPECT_NE(result.find("isolated"), std::string::npos);
}

// §5.6.4: Two Preprocessor instances built simultaneously each maintain
// independent directive state.
TEST(CompilerDirectivePreprocessor, ConcurrentCusIndependent) {
  PreprocFixture f;
  Preprocessor cu1(f.mgr, f.diag, {});
  Preprocessor cu2(f.mgr, f.diag, {});
  PreprocessFile("cu1.sv", "`default_nettype none\n", f, cu1);
  PreprocessFile("cu2.sv", "`default_nettype tri\n", f, cu2);
  EXPECT_EQ(cu1.DefaultNetType(), NetType::kNone);
  EXPECT_EQ(cu2.DefaultNetType(), NetType::kTri);
}

}  // namespace
