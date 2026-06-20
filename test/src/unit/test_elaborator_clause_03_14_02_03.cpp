#include "fixture_elaborator.h"

using namespace delta;

namespace {

static RtlirDesign* ElaborateWithPreprocAndCu(const std::string& src,
                                              ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->preproc_timescale = preproc.CurrentTimescale();
  cu->has_preproc_timescale = preproc.HasTimescale();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

TEST(TimescalePrecedenceElaboration, MixedKeywordSpecificationErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, UniformKeywordsAcceptable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "module a;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n"
      "module b;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, UniformlyUnspecifiedAcceptable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, PreprocTimescaleSuppliesFallback) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "`timescale 1ns / 1ps\n"
      "module a;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, CuTimeunitSuppliesFallback) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocAndCu(
      "timeunit 1ns;\n"
      "timeprecision 1ps;\n"
      "module a;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TimescalePrecedenceElaboration, MixedAcrossModuleAndInterfaceErrors) {
  ElabFixture f;
  ElaborateWithPreprocAndCu(
      "interface bus_if;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n"
      "module a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
