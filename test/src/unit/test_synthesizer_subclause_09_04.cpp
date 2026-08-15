#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §9.4: a procedural timing control delays when a procedural statement occurs,
// which is a property of a simulation rather than of hardware. The kind stands
// for the timing controls as a family, above the delay control of §9.4.1 and
// the event control of §9.4.2, and it gets its own sentence and its own
// position like every other construct the walk rejects.
//
// The statement is built here rather than parsed because no production yields
// this kind: src/parser/ builds a kDelay or a kEventControl for every timing
// control it reads, so a source text cannot reach the branch under test.
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
  EXPECT_FALSE(synth.CheckStmtSynthesizable(stmt));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "procedural timing control is not synthesizable", 2,
                            "9.4"));
}

}  // namespace
