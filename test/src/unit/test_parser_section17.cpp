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
  CompilationUnit* Parse(const std::string& src) {
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
  auto* unit = Parse(R"(
    checker my_check;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST_F(VerifyParseTest, CheckerWithEndLabel) {
  auto* unit = Parse(R"(
    checker labeled_check;
    endchecker : labeled_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "labeled_check");
}

TEST_F(VerifyParseTest, CheckerWithPorts) {
  auto* unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "port_check");
  EXPECT_GE(unit->checkers[0]->ports.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerWithBody) {
  auto* unit = Parse(R"(
    checker body_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, MultipleCheckers) {
  auto* unit = Parse(R"(
    checker c1;
    endchecker
    checker c2;
    endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerCoexistsWithModule) {
  auto* unit = Parse(R"(
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
  auto* unit = Parse(R"(
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
  auto& items = unit->modules[0]->items;
  ASSERT_FALSE(items.empty());
}

TEST_F(VerifyParseTest, RandcaseSingleBranch) {
  auto* unit = Parse(R"(
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
  auto* unit = Parse(R"(
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

TEST_F(VerifyParseTest, CovergroupWithCross) {
  auto* unit = Parse(R"(
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
  auto* unit = Parse(R"(
    module m;
      covergroup my_cg @(posedge clk);
        coverpoint x;
      endgroup : my_cg
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupWithOption) {
  auto* unit = Parse(R"(
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
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x iff (en);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
