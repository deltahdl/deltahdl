// Tests for §17 Checkers, §18 Constrained Random, §19 Functional Coverage

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct VerifyParseTest : ::testing::Test {
protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §17 Checker declarations
// =============================================================================

TEST_F(VerifyParseTest, BasicChecker) {
  auto *unit = Parse(R"(
    checker my_check;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST_F(VerifyParseTest, CheckerWithEndLabel) {
  auto *unit = Parse(R"(
    checker labeled_check;
    endchecker : labeled_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "labeled_check");
}

TEST_F(VerifyParseTest, CheckerWithPorts) {
  auto *unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "port_check");
  EXPECT_GE(unit->checkers[0]->ports.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerWithBody) {
  auto *unit = Parse(R"(
    checker body_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, MultipleCheckers) {
  auto *unit = Parse(R"(
    checker c1;
    endchecker
    checker c2;
    endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerCoexistsWithModule) {
  auto *unit = Parse(R"(
    module m;
    endmodule
    checker c;
    endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

// =============================================================================
// §18 Constrained random — randcase
// =============================================================================

TEST_F(VerifyParseTest, RandcaseInModule) {
  auto *unit = Parse(R"(
    module m;
      initial begin
        randcase
          3 : x = 1;
          1 : x = 2;
        endcase
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_FALSE(items.empty());
}

TEST_F(VerifyParseTest, RandcaseSingleBranch) {
  auto *unit = Parse(R"(
    module m;
      initial begin
        randcase
          1 : y = 42;
        endcase
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §19 Functional coverage — covergroup
// =============================================================================

TEST_F(VerifyParseTest, BasicCovergroup) {
  auto *unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  // Covergroup should parse without error.
}

TEST_F(VerifyParseTest, CovergroupWithBins) {
  auto *unit = Parse(R"(
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

TEST_F(VerifyParseTest, CovergroupWithCross) {
  auto *unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        cross a, b;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupEndLabel) {
  auto *unit = Parse(R"(
    module m;
      covergroup my_cg @(posedge clk);
        coverpoint x;
      endgroup : my_cg
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupWithOption) {
  auto *unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupWithIff) {
  auto *unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x iff (en);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §17.3 Checker declarations (additional)
// =============================================================================

TEST_F(VerifyParseTest, CheckerWithOutputPort) {
  auto *unit = Parse(R"(
    checker mutex(logic [31:0] sig, event clock, output bit failure);
      assert property (@clock $onehot0(sig))
        failure = 1'b0; else failure = 1'b1;
    endchecker : mutex
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "mutex");
  EXPECT_GE(unit->checkers[0]->ports.size(), 3u);
}

TEST_F(VerifyParseTest, CheckerWithRandVariable) {
  auto *unit = Parse(R"(
    checker observer_model(bit valid, reset);
      default clocking @$global_clock; endclocking
      rand bit flag;
    endchecker : observer_model
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "observer_model");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithRandConstVariable) {
  auto *unit = Parse(R"(
    checker reason_about_one_bit(bit [63:0] data1, bit [63:0] data2,
                                  event clock);
      rand const bit [5:0] idx;
      a1: assert property (@clock data1[idx] == data2[idx]);
    endchecker : reason_about_one_bit
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "reason_about_one_bit");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, NestedCheckerDeclaration) {
  auto *unit = Parse(R"(
    checker outer;
      checker inner;
      endchecker
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "outer");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

// =============================================================================
// §17.4 Checker instantiation
// =============================================================================

TEST_F(VerifyParseTest, CheckerInstantiationPositional) {
  auto *unit = Parse(R"(
    checker mutex(logic [31:0] sig, event clock, output bit failure);
      assert property (@clock $onehot0(sig))
        failure = 1'b0; else failure = 1'b1;
    endchecker
    module m(wire [31:0] bus, logic clk);
      logic res;
      mutex check_bus(bus, posedge clk, res);
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(unit->modules[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerInstantiationNamed) {
  auto *unit = Parse(R"(
    checker my_check(input logic clk, input logic data);
    endchecker
    module m;
      logic clk, data;
      my_check inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(unit->modules[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerInstantiationInAlwaysBlock) {
  auto *unit = Parse(R"(
    checker c1(event clk, logic [7:0] a, b);
      logic [7:0] sum;
      always_ff @(clk) begin
        sum <= a + 1'b1;
      end
    endchecker
    module m(input logic clk, logic [7:0] in1, in2);
      always @(posedge clk) begin
        c1 check_inside(posedge clk, in1, in2);
      end
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §17.4 Context inference
// =============================================================================

TEST_F(VerifyParseTest, CheckerContextInferenceDefaults) {
  auto *unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      property p(logic sig);
        sig;
      endproperty
      a1: assert property (@clock disable iff (reset) p(test_sig));
    endchecker : check_in_context
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "check_in_context");
  EXPECT_GE(unit->checkers[0]->ports.size(), 3u);
}

TEST_F(VerifyParseTest, CheckerContextInferenceInstantiation) {
  auto *unit = Parse(R"(
    checker check_in_context(logic test_sig,
        event clock = $inferred_clock,
        logic reset = $inferred_disable);
      a1: assert property (@clock disable iff (reset) test_sig);
    endchecker : check_in_context
    module m(logic rst);
      wire clk;
      logic a, en;
      wire b = a && en;
      check_in_context my_check1(.test_sig(b), .clock(clk), .reset(rst));
    endmodule : m
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CheckerContextInferenceImplicit) {
  auto *unit = Parse(R"(
    checker check_ctx(logic sig,
        event clock = $inferred_clock);
    endchecker
    module m;
      logic clk, a;
      always @(posedge clk) begin
        check_ctx chk(a);
      end
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §17.5 Checker procedures
// =============================================================================

TEST_F(VerifyParseTest, CheckerWithInitialProcedure) {
  auto *unit = Parse(R"(
    checker init_check(input logic clk, input logic rst);
      logic flag;
      initial begin
        flag = 0;
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "init_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithAlwaysFF) {
  auto *unit = Parse(R"(
    checker check(logic a, b, c, clk, rst);
      logic x, y, z;
      assign x = a;
      always_ff @(posedge clk or negedge rst) begin
        a1: assert (b);
        if (rst)
          z <= b;
        else z <= !c;
      end
    endchecker : check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithAlwaysComb) {
  auto *unit = Parse(R"(
    checker comb_check(logic a, b);
      logic v;
      always_comb begin
        if (a)
          v = b;
        else
          v = !b;
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "comb_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithFinalProcedure) {
  auto *unit = Parse(R"(
    checker final_check;
      logic count;
      final begin
        $display("count = %0d", count);
      end
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "final_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

// =============================================================================
// §17.7.2 Checker with clocking and assume-based randomization
// =============================================================================

TEST_F(VerifyParseTest, CheckerWithDefaultClocking) {
  auto *unit = Parse(R"(
    checker clocked_check(bit clk);
      default clocking @(posedge clk); endclocking
      rand bit flag;
      a1: assert property (flag == 1'b1);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "clocked_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithAssumeProperty) {
  auto *unit = Parse(R"(
    checker observer_model(bit valid, reset);
      default clocking @$global_clock; endclocking
      rand bit flag;
      m1: assume property (reset |=> !flag);
      m2: assume property (!reset && flag |=> flag);
      m3: assume property ($rising_gclk(flag) |-> valid);
    endchecker : observer_model
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "observer_model");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerNestedWithClocking) {
  auto *unit = Parse(R"(
    checker c1(bit fclk, bit a, bit b);
      default clocking @(posedge fclk); endclocking
      checker c2(bit bclk, bit x, bit y);
        default clocking @(posedge bclk); endclocking
        rand bit m, n;
        u1: assume property (x != m);
        u2: assume property (y != n);
      endchecker
      rand bit q, r;
      c2 B1(fclk, q + r, r);
      always_ff @(posedge fclk)
        r <= a || q;
      u3: assume property (a != q);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "c1");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithCovergroupAndClocking) {
  auto *unit = Parse(R"(
    checker my_check(logic clk, active);
      bit active_d1 = 1'b0;
      always_ff @(posedge clk) begin
        active_d1 <= active;
      end
      covergroup cg_active @(posedge clk);
        cp_active : coverpoint active
        {
          bins idle = { 1'b0 };
          bins active = { 1'b1 };
        }
        option.per_instance = 1;
      endgroup
    endchecker : my_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

} // namespace
