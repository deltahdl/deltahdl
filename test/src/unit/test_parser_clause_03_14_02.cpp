// §3.14.2: Specifying time units and precision

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

// Helper: preprocess source and return timescale state.

// Helper: parse source and return the compilation unit.
struct ParseResult31402 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31402 Parse(const std::string& src) {
  ParseResult31402 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.PreprocessTimescale(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// 29. Both mechanisms handle all three magnitudes (1, 10, 100).
TEST(ParserClause03, Cl3_14_2_BothMechanismsMagnitudes) {
  // `timescale with magnitudes.
  auto r1 = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_EQ(r1.timescale.magnitude, 1);
  auto r10 = PreprocessTimescale("`timescale 10ns / 10ps\n");
  EXPECT_EQ(r10.timescale.magnitude, 10);
  auto r100 = PreprocessTimescale("`timescale 100ns / 100ps\n");
  EXPECT_EQ(r100.timescale.magnitude, 100);
  // timeunit with magnitudes: all three parse successfully.
  EXPECT_FALSE(Parse("module m; timeunit 1ns; endmodule\n").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 10ns; endmodule\n").has_errors);
  EXPECT_FALSE(Parse("module m; timeunit 100ns; endmodule\n").has_errors);
}

}  // namespace
