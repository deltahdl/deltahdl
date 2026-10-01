#include <gtest/gtest.h>

#include "fixture_program.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithBins) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins low = {[0:15]};
          bins high = {[16:31]};
        }
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// §19.5.1, §19.5.1.2 and §19.5.2 with A.2.11: each covergroup_value_range
// form -- a `$` low or high bound, an absolute and a relative tolerance -- a
// set_covergroup_expression, a goto repetition and a bin's own guard are held
// on the tree with their parts.
TEST_F(VerifyParseTest, BinsValueFormsTree) {
  auto* unit = Parse(R"(
    module m;
      int v;
      real r;
      int set[$];
      bit en;
      covergroup cg;
        coverpoint v {
          bins lo = {[$:10]};
          bins hi = {[20:$]};
          bins s = set iff (en);
          bins g = (1 => 3 [-> 2] => 5);
        }
        coverpoint r {
          bins near = {[1.0 +/- 0.5]};
          bins pct = {[10.0 +%- 5.0]};
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = nullptr;
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) cg = item->covergroup;
  }
  ASSERT_NE(cg, nullptr);
  ASSERT_EQ(cg->items.size(), 2u);
  const CoverPointDecl* v = cg->items[0].cover_point;
  ASSERT_EQ(v->bins.size(), 4u);
  EXPECT_EQ(v->bins[0].ranges[0].kind, CovergroupValueRangeKind::kRange);
  EXPECT_EQ(v->bins[0].ranges[0].lo, nullptr);
  EXPECT_NE(v->bins[0].ranges[0].hi, nullptr);
  EXPECT_NE(v->bins[1].ranges[0].lo, nullptr);
  EXPECT_EQ(v->bins[1].ranges[0].hi, nullptr);
  EXPECT_EQ(v->bins[2].kind, BinsOrOptionsKind::kSetExpression);
  EXPECT_NE(v->bins[2].iff, nullptr);
  ASSERT_EQ(v->bins[3].transitions.size(), 1u);
  EXPECT_EQ(v->bins[3].transitions[0].steps[1].repetition,
            TransRepetition::kGoto);
  const CoverPointDecl* r = cg->items[1].cover_point;
  ASSERT_EQ(r->bins.size(), 2u);
  EXPECT_EQ(r->bins[0].ranges[0].kind,
            CovergroupValueRangeKind::kAbsoluteTolerance);
  EXPECT_EQ(r->bins[1].ranges[0].kind,
            CovergroupValueRangeKind::kRelativeTolerance);
}

}  // namespace
