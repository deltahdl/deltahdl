#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ProceduralTimingControlSynthesis, TimingControlStmtIsRejectedByName) {
  SynthFixture f;
  auto fid = f.src_mgr.AddFile("<test>",
                               "module m;\n"
                               "  reg x;\n"
                               "endmodule\n");
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kTimingControl;
  stmt->range.start = SourceLoc{fid, 2, 3};
  SynthLower synth(f.arena, f.diag);
  RtlirModule mod;
  EXPECT_FALSE(synth.CheckStmtSynthesizable(stmt, &mod));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural timing control is not synthesizable", 2,
                            "9.4"));
}

}  // namespace
