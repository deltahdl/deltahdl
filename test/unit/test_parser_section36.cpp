// Tests for §36-§41 System API functions (VPI, Assertion, Coverage, Data Read)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ApiParseTest : ::testing::Test {
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
// §39 Assertion control system functions
// =============================================================================

TEST_F(ApiParseTest, AssertOnSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOn;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertOffSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOff;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertKillSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertKill;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §40 Coverage control system functions
// =============================================================================

TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, CoverageGetMaxSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        int x;
        x = $coverage_get_max(0, 0);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §41 Data read API / General system functions
// =============================================================================

TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmemhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmembSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemb("data.bin", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, WritememhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $writememh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, MultipleApiCallsInModule) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        $assertOn;
        $coverage_control(1, 0, 0);
        $readmemh("data.hex", mem);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  ASSERT_FALSE(unit->modules[0]->items.empty());
}

}  // namespace
