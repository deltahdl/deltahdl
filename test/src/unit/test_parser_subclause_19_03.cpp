#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, BasicCovergroup) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupEndLabel) {
  auto* unit = Parse(R"(
    module m;
      covergroup my_cg @(posedge clk);
        coverpoint x;
      endgroup : my_cg
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(CovergroupParsing, CovergroupWithBlockEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(begin top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupWithFunctionSample) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupDefinedInClass) {
  EXPECT_TRUE(ParseOk(R"(
    class C;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endclass
  )"));
}

TEST(CovergroupParsing, CovergroupWithNoCoverageEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupExtendsInClass) {
  EXPECT_TRUE(ParseOk(R"(
    class C;
      covergroup extends base_cg;
        coverpoint x;
      endgroup
    endclass
  )"));
}

TEST(CovergroupParsing, CovergroupInPackage) {
  EXPECT_TRUE(ParseOk(R"(
    package p;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endpackage
  )"));
}

TEST(CovergroupParsing, CovergroupInProgram) {
  EXPECT_TRUE(ParseOk(R"(
    program prog;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endprogram
  )"));
}

TEST(CovergroupParsing, CovergroupWithFormalArguments) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg (ref int x, input int c) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupWithCoverageOption) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, OutputFormalArgumentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (output int x) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a covergroup formal argument cannot be declared "
                            "'output' or 'inout'",
                            3, "19.3"));
}

TEST(CovergroupParsing, InoutFormalArgumentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (inout int x) @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a covergroup formal argument cannot be declared "
                            "'output' or 'inout'",
                            3, "19.3"));
}

TEST(CovergroupParsing, CovergroupInInterface) {
  EXPECT_TRUE(ParseOk(R"(
    interface intf;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endinterface
  )"));
}

TEST(CovergroupParsing, CovergroupInChecker) {
  EXPECT_TRUE(ParseOk(R"(
    checker chk;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endchecker
  )"));
}

TEST(CovergroupParsing, CovergroupWithTypeOption) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        type_option.merge_instances = 1;
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupWithCrossCoverage) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        cp_a: coverpoint a;
        cp_b: coverpoint b;
        axb: cross cp_a, cp_b;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupWithOredBlockEvents) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(begin top.worker or end top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupWithEndBlockEvent) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @@(end top.worker);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(CovergroupParsing, CovergroupBlockEventMissingBeginEndRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg @@(top.worker);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'begin' or 'end' in block event",
                            3, "19.3"));
}

TEST(CovergroupParsing, CovergroupWithFunctionNonSampleRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function collect(int v);
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'sample', got 'collect'", 3, "19.3"));
}

TEST(CovergroupParsing, MissingEndgroupNames19_3) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endgroup'", 2, "19.3"));
}

const CovergroupDecl* FirstCovergroup(const CompilationUnit* unit) {
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) return item->covergroup;
  }
  return nullptr;
}

TEST_F(VerifyParseTest, CovergroupTreeHoldsItsDeclaration) {
  auto* unit = Parse(R"(
    module m;
      bit [1:0] v;
      bit clk;
      covergroup cg (int lim) @(posedge clk);
        option.at_least = 2;
        a: coverpoint v { bins lo = {0}; bins hi[] = {[1:3]}; }
        b: coverpoint v iff (lim > 0);
        x: cross a, b;
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = FirstCovergroup(unit);
  ASSERT_NE(cg, nullptr);
  EXPECT_EQ(cg->name, "cg");
  ASSERT_EQ(cg->formals.size(), 1u);
  EXPECT_EQ(cg->formals[0].name, "lim");
  EXPECT_EQ(cg->event.kind, CoverageEventKind::kClocking);
  ASSERT_EQ(cg->event.clocking.size(), 1u);
  EXPECT_EQ(cg->event.clocking[0].edge, Edge::kPosedge);
  ASSERT_EQ(cg->items.size(), 4u);
  ASSERT_EQ(cg->items[0].kind, CoverageSpecKind::kOption);
  EXPECT_FALSE(cg->items[0].option.is_type_option);
  EXPECT_EQ(cg->items[0].option.member, "at_least");
  ASSERT_EQ(cg->items[1].kind, CoverageSpecKind::kCoverPoint);
  const CoverPointDecl* a = cg->items[1].cover_point;
  EXPECT_EQ(a->label, "a");
  ASSERT_EQ(a->bins.size(), 2u);
  EXPECT_EQ(a->bins[0].kind, BinsOrOptionsKind::kValues);
  EXPECT_EQ(a->bins[0].name, "lo");
  EXPECT_FALSE(a->bins[0].is_array);
  ASSERT_EQ(a->bins[0].ranges.size(), 1u);
  EXPECT_EQ(a->bins[0].ranges[0].kind, CovergroupValueRangeKind::kValue);
  EXPECT_EQ(a->bins[1].name, "hi");
  EXPECT_TRUE(a->bins[1].is_array);
  EXPECT_EQ(a->bins[1].array_size, nullptr);
  ASSERT_EQ(a->bins[1].ranges.size(), 1u);
  EXPECT_EQ(a->bins[1].ranges[0].kind, CovergroupValueRangeKind::kRange);
  ASSERT_EQ(cg->items[2].kind, CoverageSpecKind::kCoverPoint);
  EXPECT_EQ(cg->items[2].cover_point->label, "b");
  EXPECT_NE(cg->items[2].cover_point->iff, nullptr);
  EXPECT_TRUE(cg->items[2].cover_point->bins.empty());
  ASSERT_EQ(cg->items[3].kind, CoverageSpecKind::kCoverCross);
  const CoverCrossDecl* x = cg->items[3].cover_cross;
  EXPECT_EQ(x->label, "x");
  ASSERT_EQ(x->items.size(), 2u);
  EXPECT_EQ(x->items[0].name, "a");
  EXPECT_EQ(x->items[1].name, "b");
}

TEST_F(VerifyParseTest, CovergroupTreeHoldsBinsAndCrossBody) {
  auto* unit = Parse(R"(
    module m;
      bit [3:0] v;
      bit [3:0] w;
      bit clk;
      covergroup cg @(posedge clk);
        a: coverpoint v {
          bins t = (1 => 2 [* 2] => 3), (0 => 1);
          wildcard bins wc = {4'b1??1};
          bins d = default;
          bins s = default sequence;
          type_option.weight = 2;
        }
        b: coverpoint w;
        x: cross a, b {
          bins sel = binsof(a.t) && !binsof(b) intersect {1};
          ignore_bins ig = binsof(a) intersect {[0:1]};
          option.weight = 3;
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = FirstCovergroup(unit);
  ASSERT_NE(cg, nullptr);
  ASSERT_EQ(cg->items.size(), 3u);
  const CoverPointDecl* a = cg->items[0].cover_point;
  ASSERT_NE(a, nullptr);
  ASSERT_EQ(a->bins.size(), 5u);
  EXPECT_EQ(a->bins[0].kind, BinsOrOptionsKind::kTransitions);
  ASSERT_EQ(a->bins[0].transitions.size(), 2u);
  ASSERT_EQ(a->bins[0].transitions[0].steps.size(), 3u);
  EXPECT_EQ(a->bins[0].transitions[0].steps[1].repetition,
            TransRepetition::kConsecutive);
  EXPECT_NE(a->bins[0].transitions[0].steps[1].repeat_lo, nullptr);
  EXPECT_EQ(a->bins[0].transitions[1].steps.size(), 2u);
  EXPECT_TRUE(a->bins[1].wildcard);
  EXPECT_EQ(a->bins[1].kind, BinsOrOptionsKind::kValues);
  EXPECT_EQ(a->bins[2].kind, BinsOrOptionsKind::kDefault);
  EXPECT_EQ(a->bins[3].kind, BinsOrOptionsKind::kDefaultSequence);
  EXPECT_EQ(a->bins[4].kind, BinsOrOptionsKind::kOption);
  EXPECT_TRUE(a->bins[4].option.is_type_option);
  EXPECT_EQ(a->bins[4].option.member, "weight");
  const CoverCrossDecl* x = cg->items[2].cover_cross;
  ASSERT_NE(x, nullptr);
  ASSERT_EQ(x->body.size(), 3u);
  ASSERT_EQ(x->body[0].kind, CrossBodyItemKind::kBinsSelection);
  const SelectExpression* sel = x->body[0].bins.select;
  ASSERT_NE(sel, nullptr);
  ASSERT_EQ(sel->kind, SelectExpressionKind::kAnd);
  EXPECT_EQ(sel->lhs->kind, SelectExpressionKind::kBinsOf);
  EXPECT_EQ(sel->lhs->bins_of, "a");
  EXPECT_EQ(sel->lhs->bins_of_bin, "t");
  ASSERT_EQ(sel->rhs->kind, SelectExpressionKind::kNot);
  EXPECT_EQ(sel->rhs->lhs->bins_of, "b");
  EXPECT_EQ(sel->rhs->lhs->intersect.size(), 1u);
  EXPECT_EQ(x->body[1].bins.keyword, BinsKeyword::kIgnoreBins);
  EXPECT_EQ(x->body[2].kind, CrossBodyItemKind::kOption);
  EXPECT_EQ(x->body[2].option.member, "weight");
}

TEST_F(VerifyParseTest, CovergroupTreeHoldsSampleAndBlockEvents) {
  auto* unit = Parse(R"(
    module m;
      covergroup cs with function sample(int s);
        coverpoint s;
      endgroup
      covergroup cb @@(begin m.t or end m.t);
        coverpoint v;
      endgroup
      bit v;
      task t; endtask
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  std::vector<const CovergroupDecl*> cgs;
  for (const ModuleItem* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) {
      cgs.push_back(item->covergroup);
    }
  }
  ASSERT_EQ(cgs.size(), 2u);
  EXPECT_EQ(cgs[0]->event.kind, CoverageEventKind::kSampleFunction);
  ASSERT_EQ(cgs[0]->event.sample_formals.size(), 1u);
  EXPECT_EQ(cgs[0]->event.sample_formals[0].name, "s");
  EXPECT_EQ(cgs[1]->event.kind, CoverageEventKind::kBlockEvent);
  ASSERT_EQ(cgs[1]->event.block_event.size(), 2u);
  EXPECT_TRUE(cgs[1]->event.block_event[0].is_begin);
  EXPECT_FALSE(cgs[1]->event.block_event[1].is_begin);
  ASSERT_EQ(cgs[1]->event.block_event[0].path.size(), 2u);
  EXPECT_EQ(cgs[1]->event.block_event[0].path[1], "t");
}

TEST_F(VerifyParseTest, EmbeddedCovergroupTreeOnClassMember) {
  auto* unit = Parse(R"(
    class C;
      bit v;
      covergroup cg;
        coverpoint v;
      endgroup
    endclass
  )");
  EXPECT_FALSE(diag_.HasErrors());
  ASSERT_EQ(unit->classes.size(), 1u);
  const CovergroupDecl* cg = nullptr;
  for (const ClassMember* member : unit->classes[0]->members) {
    if (member->kind == ClassMemberKind::kCovergroup) cg = member->covergroup;
  }
  ASSERT_NE(cg, nullptr);
  EXPECT_EQ(cg->name, "cg");
  ASSERT_EQ(cg->items.size(), 1u);
  EXPECT_EQ(cg->items[0].kind, CoverageSpecKind::kCoverPoint);
}

TEST_F(VerifyParseTest, CovergroupEventIsBareIdentifier) {
  auto* unit = Parse(R"(
    module m;
      bit clk;
      bit [1:0] v;
      covergroup cg @clk;
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const CovergroupDecl* cg = FirstCovergroup(unit);
  ASSERT_NE(cg, nullptr);
  EXPECT_EQ(cg->event.kind, CoverageEventKind::kClocking);
  ASSERT_EQ(cg->event.clocking.size(), 1u);
  ASSERT_NE(cg->event.clocking[0].signal, nullptr);
  EXPECT_EQ(cg->event.clocking[0].signal->text, "clk");
}

TEST(CovergroupParsing, ACovergroupDeclaredInTheCompilationUnit) {
  auto result = Parse(R"(
    covergroup ucg with function sample(bit x);
      coverpoint x { bins one = {1}; bins zero = {0}; }
    endgroup
    module t;
      ucg c = new;
    endmodule
  )");
  ASSERT_FALSE(result.has_errors);
  ASSERT_EQ(result.cu->cu_items.size(), 1u);
  EXPECT_EQ(result.cu->cu_items[0]->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_EQ(result.cu->cu_items[0]->name, "ucg");
}

}  // namespace
